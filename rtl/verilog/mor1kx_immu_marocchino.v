/////////////////////////////////////////////////////////////////////
//                                                                 //
//  mor1kx_immu_marocchino                                         //
//                                                                 //
//  Description:                                                   //
//    Instruction MMU implementation                               //
//    Tightly coupled with MAROCCHINO FETCH                        //
//    Based on mor1kx_immu                                         //
//                                                                 //
/////////////////////////////////////////////////////////////////////
//                                                                 //
//   Copyright (C) 2013 Stefan Kristiansson                        //
//                      stefan.kristiansson@saunalahti.fi          //
//                                                                 //
//   Copyright (C) 2015 Andrey Bacherov                            //
//                      avbacherov@opencores.org                   //
//                                                                 //
//      This Source Code Form is subject to the terms of the       //
//      Open Hardware Description License, v. 1.0. If a copy       //
//      of the OHDL was not distributed with this file, You        //
//      can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt    //
//                                                                 //
/////////////////////////////////////////////////////////////////////

`include "mor1kx-defines.v"

module mor1kx_immu_marocchino
#(
  parameter FEATURE_IMMU_HW_TLB_RELOAD = "NONE",
  parameter OPTION_OPERAND_WIDTH       = 32,
  parameter OPTION_RESET_PC            = {{(OPTION_OPERAND_WIDTH-13){1'b0}},
                                          `OR1K_RESET_VECTOR,8'd0},
  parameter OPTION_IMMU_SET_WIDTH      = 6,
  parameter OPTION_IMMU_WAYS           = 1,
  parameter OPTION_IMMU_CLEAR_ON_INIT  = 0
)
(
  // clock & reset
  input                                 clk,
  input                                 rst,

  // controls
  input                                 adv_i,        // advance
  input                                 force_off_i,  // drop stored "IMMU enable"

  // configuration
  input                                 enable_i,
  input                                 supervisor_mode_i,

  // address translation
  input      [OPTION_OPERAND_WIDTH-1:0] virt_addr_i,
  output reg [OPTION_OPERAND_WIDTH-1:0] virt_addr_fetch_o,
  output     [OPTION_OPERAND_WIDTH-1:0] phys_addr_fetch_o,

  // flags
  output reg                            cache_inhibit_o,
  output reg                            tlb_miss_o,
  output                                pagefault_o,

  // HW reload
  output reg                            tlb_reload_req_o,
  input                                 tlb_reload_ack_i,
  output reg [OPTION_OPERAND_WIDTH-1:0] tlb_reload_addr_o,
  input      [OPTION_OPERAND_WIDTH-1:0] tlb_reload_data_i,
  output                                tlb_reload_pagefault_o,
  input                                 tlb_reload_pagefault_clear_i,
  output                                tlb_reload_busy_o,

  // SPR interface
  input                          [15:0] spr_bus_addr_i,
  input                                 spr_bus_we_i,
  input                                 spr_bus_stb_i,
  input      [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_i,
  output     [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_o,
  output reg                            spr_bus_ack_o
);

  wire  [OPTION_OPERAND_WIDTH-1:0] itlb_match_dout[OPTION_IMMU_WAYS-1:0];
  wire [OPTION_IMMU_SET_WIDTH-1:0] itlb_match_addr;
  reg       [OPTION_IMMU_WAYS-1:0] itlb_match_we;
  wire  [OPTION_OPERAND_WIDTH-1:0] itlb_match_din;

  wire  [OPTION_OPERAND_WIDTH-1:0] itlb_match_huge_dout[OPTION_IMMU_WAYS-1:0];
  wire [OPTION_IMMU_SET_WIDTH-1:0] itlb_match_huge_addr;
  wire                             itlb_match_huge_we;

  wire  [OPTION_OPERAND_WIDTH-1:0] itlb_trans_dout[OPTION_IMMU_WAYS-1:0];
  wire [OPTION_IMMU_SET_WIDTH-1:0] itlb_trans_addr;
  reg       [OPTION_IMMU_WAYS-1:0] itlb_trans_we;
  wire  [OPTION_OPERAND_WIDTH-1:0] itlb_trans_din;

  wire  [OPTION_OPERAND_WIDTH-1:0] itlb_trans_huge_dout[OPTION_IMMU_WAYS-1:0];
  wire [OPTION_IMMU_SET_WIDTH-1:0] itlb_trans_huge_addr;
  wire                             itlb_trans_huge_we;

  reg                              itlb_match_reload_we;
  reg   [OPTION_OPERAND_WIDTH-1:0] itlb_match_reload_din;

  reg                              itlb_trans_reload_we;
  reg   [OPTION_OPERAND_WIDTH-1:0] itlb_trans_reload_din;

  wire                             itlb_match_spr_cs;
  reg                              itlb_match_spr_cs_r;
  wire                             itlb_trans_spr_cs;
  reg                              itlb_trans_spr_cs_r;

  wire                             immucr_spr_cs;
  reg                              immucr_spr_cs_r;
  reg   [OPTION_OPERAND_WIDTH-1:0] immucr;

  wire                       [1:0] spr_way_idx;
  reg                        [1:0] spr_way_idx_r;

  wire      [OPTION_IMMU_WAYS-1:0] way_hit;
  wire      [OPTION_IMMU_WAYS-1:0] way_huge_hit;

  reg                              tlb_reload_pagefault;
  reg                              tlb_reload_huge;

  // sxe: supervisor execute enable
  // uxe: user exexute enable
  reg                              sxe;
  reg                              uxe;

  wire                             spr_immu_stb;    // SPR acceess

  genvar                           i;
  integer                          j;


  // ICACHE/IMMU match address store register
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      virt_addr_fetch_o <= OPTION_RESET_PC - 4; // will be restored on 1st advance
    else if (adv_i)
      virt_addr_fetch_o <= virt_addr_i;
  end // @ clock


  // Stored "IMMU enable" and "Supevisor Mode" flags
  // (for masking IMMU output flags, but not for advancing)
  reg enable_r;
  reg supervisor_mode_r;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      enable_r          <= 1'b0;
      supervisor_mode_r <= 1'b0;
    end
    else if (force_off_i | spr_immu_stb) begin
      enable_r          <= 1'b0;
      supervisor_mode_r <= supervisor_mode_r;
    end
    else if (adv_i) begin
      enable_r          <= enable_i;
      supervisor_mode_r <= supervisor_mode_i;
    end
  end // @ clock


  //---------------//
  // SPR interface //
  //---------------//

  //   We don't expect R/W-collisions for SPRbus vs FETCH advance
  // because we execute l.mt(f)spr after pipeline stalling (see OMAN)

  assign spr_immu_stb = spr_bus_stb_i & (spr_bus_addr_i[15:11] == `OR1K_SPR_IMMU_BASE);

  // Process IMMU Control Register
  //  # IMMUCR "chip select"
  assign immucr_spr_cs = spr_immu_stb & (~(|spr_bus_addr_i[10:0])) & (FEATURE_IMMU_HW_TLB_RELOAD != "NONE");
  //  # IMMUCR proc
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      immucr <= {OPTION_OPERAND_WIDTH{1'b0}};
    else if (immucr_spr_cs & spr_bus_we_i)
      immucr <= spr_bus_dat_i;
  end // @ clock

  // SPR ack generation
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      spr_bus_ack_o <= 1'b0;
    else if (spr_bus_ack_o)
      spr_bus_ack_o <= 1'b0;
    else if (spr_immu_stb)
      spr_bus_ack_o <= 1'b1;
  end // @ clock

  // match RAM chip select
  assign itlb_match_spr_cs = spr_immu_stb & (|spr_bus_addr_i[10:9]) & ~spr_bus_addr_i[7];
  // translate RAM chip select
  assign itlb_trans_spr_cs = spr_immu_stb & (|spr_bus_addr_i[10:9]) &  spr_bus_addr_i[7];
  // way select
  assign spr_way_idx = {spr_bus_addr_i[10], spr_bus_addr_i[8]};

  // SPR data output multiplexer control
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      itlb_match_spr_cs_r <= 1'b0;
      itlb_trans_spr_cs_r <= 1'b0;
      immucr_spr_cs_r     <= 1'b0;
      spr_way_idx_r       <= 2'd0;
    end
    else if (spr_bus_ack_o) begin
      itlb_match_spr_cs_r <= 1'b0;
      itlb_trans_spr_cs_r <= 1'b0;
      immucr_spr_cs_r     <= 1'b0;
      spr_way_idx_r       <= 2'd0;
    end
    else if (spr_immu_stb) begin
      itlb_match_spr_cs_r <= itlb_match_spr_cs;
      itlb_trans_spr_cs_r <= itlb_trans_spr_cs;
      immucr_spr_cs_r     <= immucr_spr_cs;
      spr_way_idx_r       <= spr_way_idx;
    end
  end // @ clock
  // SPR data output multiplexer
  assign spr_bus_dat_o = itlb_match_spr_cs_r ? itlb_match_dout[spr_way_idx_r] :
                         itlb_trans_spr_cs_r ? itlb_trans_dout[spr_way_idx_r] :
                         immucr_spr_cs_r     ? immucr                         :
                                               {OPTION_OPERAND_WIDTH{1'b0}};


  generate
  for (i = 0; i < OPTION_IMMU_WAYS; i=i+1) begin : ways
    // 8KB page hit
    assign way_hit[i] = (itlb_match_dout[i][31:13] == virt_addr_fetch_o[31:13]) & // address hit
                        ~(&itlb_match_huge_dout[i][1:0]) &                        // not valid huge
                        itlb_match_dout[i][0] &                                   // valid bit
                        enable_r;                                                 // mmu enabled
    // Huge page hit
    assign way_huge_hit[i] = (itlb_match_huge_dout[i][31:24] == virt_addr_fetch_o[31:24]) & // address hit
                             itlb_match_huge_dout[i][1] & itlb_match_huge_dout[i][0] &      // valid huge
                             enable_r;                                                      // mmu enabled
  end
  endgenerate

  reg [OPTION_OPERAND_WIDTH-1:0] phys_addr;
  
  always @(*) begin
    tlb_miss_o        = ~tlb_reload_pagefault & ~spr_immu_stb & enable_r;
    phys_addr         = virt_addr_fetch_o[23:0];
    sxe               = 1'b0;
    uxe               = 1'b0;
    cache_inhibit_o   = 1'b0;

    for (j = 0; j < OPTION_IMMU_WAYS; j=j+1) begin
      if (way_huge_hit[j] | way_hit[j])
        tlb_miss_o = 1'b0;

      if (way_huge_hit[j]) begin
        phys_addr         = {itlb_trans_huge_dout[j][31:24], virt_addr_fetch_o[23:0]};
        sxe               = itlb_trans_huge_dout[j][6];
        uxe               = itlb_trans_huge_dout[j][7];
        cache_inhibit_o   = itlb_trans_huge_dout[j][1];
      end
      else if (way_hit[j])begin
        phys_addr         = {itlb_trans_dout[j][31:13], virt_addr_fetch_o[12:0]};
        sxe               = itlb_trans_dout[j][6];
        uxe               = itlb_trans_dout[j][7];
        cache_inhibit_o   = itlb_trans_dout[j][1];
      end

      itlb_match_we[j] = 1'b0;
      if (itlb_match_reload_we & ~tlb_reload_huge)
        itlb_match_we[j] = 1'b1;
      if (j == spr_way_idx)
        itlb_match_we[j] = itlb_match_spr_cs & spr_bus_we_i & ~spr_bus_ack_o;
 
      itlb_trans_we[j] = 1'b0;
      if (itlb_trans_reload_we & ~tlb_reload_huge)
        itlb_trans_we[j] = 1'b1;
      if (j == spr_way_idx)
        itlb_trans_we[j] = itlb_trans_spr_cs & spr_bus_we_i & ~spr_bus_ack_o;
    end
  end // loop by ways

  assign pagefault_o = (supervisor_mode_r ? ~sxe : ~uxe) & ~tlb_reload_busy_o & ~spr_immu_stb & enable_r;

  assign phys_addr_fetch_o = enable_r ? phys_addr : virt_addr_fetch_o;


  // match 8KB input address
  assign itlb_match_addr =
    (itlb_match_spr_cs & ~spr_bus_ack_o) ? spr_bus_addr_i[OPTION_IMMU_SET_WIDTH-1:0]          :
                                           virt_addr_i[13+(OPTION_IMMU_SET_WIDTH-1):13];
  // match huge address and write command
  assign itlb_match_huge_addr = virt_addr_i[24+(OPTION_IMMU_SET_WIDTH-1):24];
  assign itlb_match_huge_we   = itlb_match_reload_we & tlb_reload_huge;
  // match data in
  assign itlb_match_din = itlb_match_reload_we ? itlb_match_reload_din : spr_bus_dat_i;


  // translation 8KB input address
  assign itlb_trans_addr =
    (itlb_trans_spr_cs & ~spr_bus_ack_o) ? spr_bus_addr_i[OPTION_IMMU_SET_WIDTH-1:0]          :
                                           virt_addr_i[13+(OPTION_IMMU_SET_WIDTH-1):13];
  // translation huge address and write command
  assign itlb_trans_huge_addr = virt_addr_i[24+(OPTION_IMMU_SET_WIDTH-1):24];
  assign itlb_trans_huge_we   = itlb_trans_reload_we & tlb_reload_huge;
  // translation data in
  assign itlb_trans_din = itlb_trans_reload_we ? itlb_trans_reload_din : spr_bus_dat_i;


  /*
  localparam [3:0] TLB_IDLE            = 4'b0001,
                   TLB_GET_PTE_POINTER = 4'b0010,
                   TLB_GET_PTE         = 4'b0100,
                   TLB_READ            = 4'b1000; */

  generate
  /* verilator lint_off WIDTH */
  if (FEATURE_IMMU_HW_TLB_RELOAD != "NONE") begin
  /* verilator lint_on WIDTH */
  
    initial begin
      $display("IMMU ERROR: HW TLB reload is not implemented in MAROCCHINO");
      $finish();
    end
  
    // Hardware TLB reload
    // Compliant with the suggestions outlined in this thread:
    // http://lists.openrisc.net/pipermail/openrisc/2013-July/001806.html
    //
    // PTE layout:
    // | 31 ... 13 | 12 |  11 |   10  | 9 | 8 | 7 | 6 | 5 | 4 | 3 | 2 | 1 | 0 |
    // |    PPN    | Reserved |PRESENT| L | X | W | U | D | A |WOM|WBC|CI |CC |
    //
    // Where X/W/U maps into SXE/UXE like this:
    // X | W | U   SXE | UXE
    // ---------   ---------
    // 0 | x | 0 =  0  |  0
    // 0 | x | 1 =  0  |  0
    //    ...
    // 1 | x | 0 =  1  |  0
    // 1 | x | 1 =  1  |  1
    /*
    reg [3:0] tlb_reload_state = TLB_IDLE;
    wire      do_reload;
  
    assign do_reload              = enable_r & tlb_miss_o & (immucr[31:10] != 22'd0);
    assign tlb_reload_busy_o      = (tlb_reload_state != TLB_IDLE) | do_reload;
    assign tlb_reload_pagefault_o = tlb_reload_pagefault & ~tlb_reload_pagefault_clear_i;
  
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        tlb_reload_pagefault <= 1'b0;
      else if(tlb_reload_pagefault_clear_i)
        tlb_reload_pagefault <= 1'b0;
  
      itlb_trans_reload_we  <= 1'b0;
      itlb_trans_reload_din <= {OPTION_OPERAND_WIDTH{1'b0}};
      itlb_match_reload_we  <= 1'b0;
      itlb_match_reload_din <= {OPTION_OPERAND_WIDTH{1'b0}};
  
      case (tlb_reload_state)
        TLB_IDLE: begin
          tlb_reload_huge  <= 1'b0;
          tlb_reload_req_o <= 1'b0;
          if (do_reload) begin
            tlb_reload_req_o  <= 1'b1;
            tlb_reload_addr_o <= {immucr[31:10],virt_addr_fetch_o[31:24],2'b00};
            tlb_reload_state  <= TLB_GET_PTE_POINTER;
          end
        end // tlb reload idle
  
        //
        // Here we get the pointer to the PTE table, next is to fetch
        // the actual pte from the offset in the table.
        // The offset is calculated by:
        // ((virt_addr_match >> PAGE_BITS) & (PTE_CNT-1)) << 2
        // Where PAGE_BITS is 13 (8 kb page) and PTE_CNT is 2048
        // (number of PTEs in the PTE table)
        //
        TLB_GET_PTE_POINTER: begin
          tlb_reload_huge <= 0;
          if (tlb_reload_ack_i) begin
            if (tlb_reload_data_i[31:13] == 0) begin
              tlb_reload_pagefault <= 1'b1;
              tlb_reload_req_o     <= 1'b0;
              tlb_reload_state     <= TLB_IDLE;
            end
            else if (tlb_reload_data_i[9]) begin
              tlb_reload_huge  <= 1'b1;
              tlb_reload_req_o <= 1'b0;
              tlb_reload_state <= TLB_GET_PTE;
            end
            else begin
              tlb_reload_addr_o <= {tlb_reload_data_i[31:13],virt_addr_fetch_o[23:13],2'b00};
              tlb_reload_state  <= TLB_GET_PTE;
            end
          end
        end // tlb get pointer
  
        //
        // Here we get the actual PTE, left to do is to translate the
        // PTE data into our translate and match registers.
        //
        TLB_GET_PTE: begin
          if (tlb_reload_ack_i) begin
            tlb_reload_req_o <= 1'b0;
            // Check PRESENT bit
            if (~tlb_reload_data_i[10]) begin
              tlb_reload_pagefault <= 1'b1;
              tlb_reload_state     <= TLB_IDLE;
            end
            else begin
              // Translate register generation.
              // PPN
              itlb_trans_reload_din[31:13] <= tlb_reload_data_i[31:13];
              // UXE = X & U
              itlb_trans_reload_din[7] <= tlb_reload_data_i[8] & tlb_reload_data_i[6];
              // SXE = X
              itlb_trans_reload_din[6] <= tlb_reload_data_i[8];
              // Dirty, Accessed, Weakly-Ordered-Memory, Writeback cache,
              // Cache inhibit, Cache coherent
              itlb_trans_reload_din[5:0] <= tlb_reload_data_i[5:0];
              itlb_trans_reload_we       <= 1'b1;
  
              // Match register generation.
              // VPN
              itlb_match_reload_din[31:13] <= virt_addr_fetch_o[31:13];
              // PL1
              itlb_match_reload_din[1] <= tlb_reload_huge;
              // Valid
              itlb_match_reload_din[0] <= 1'b1;
              itlb_match_reload_we     <= 1'b1;
  
              tlb_reload_state <= TLB_READ;
            end
          end
        end // tlb get pte
  
        // Let the just written values propagate out on the read ports
        TLB_READ: begin
          tlb_reload_state <= TLB_IDLE;
        end
  
        default:
          tlb_reload_state <= TLB_IDLE;
      endcase
    end // @ clock
    */
  end
  else begin // SW reload
    assign tlb_reload_pagefault_o = 1'b0;
    assign tlb_reload_busy_o      = 1'b0;
    always @(posedge clk) begin
      tlb_reload_req_o      <= 1'b0;
      tlb_reload_addr_o     <= {OPTION_OPERAND_WIDTH{1'b0}};
      tlb_reload_pagefault  <= 1'b0;
      tlb_reload_huge       <= 1'b0;
      itlb_trans_reload_we  <= 1'b0;
      itlb_trans_reload_din <= {OPTION_OPERAND_WIDTH{1'b0}};
      itlb_match_reload_we  <= 1'b0;
      itlb_match_reload_din <= {OPTION_OPERAND_WIDTH{1'b0}};
    end
  end // HW/SW reload
  endgenerate

  // Enable for RAM blocks if:
  //  1) regular FETCH advance
  //  2) SPR access
  wire ram_re = (adv_i & enable_i) | (spr_immu_stb & ~spr_bus_we_i & ~spr_bus_ack_o);

  generate
  for (i = 0; i < OPTION_IMMU_WAYS; i=i+1) begin : itlb
    // ITLB match registers
    mor1kx_dpram_en_w1st_sclk
    #(
      .ADDR_WIDTH     (OPTION_IMMU_SET_WIDTH),
      .DATA_WIDTH     (OPTION_OPERAND_WIDTH),
      .CLEAR_ON_INIT  (OPTION_IMMU_CLEAR_ON_INIT)
    )
    itlb_match_regs
    (
      // common clock
      .clk    (clk),
      // port "a": 8KB pages
      .en_a   (ram_re | itlb_match_we[i]),
      .we_a   (itlb_match_we[i]),
      .addr_a (itlb_match_addr),
      .din_a  (itlb_match_din),
      .dout_a (itlb_match_dout[i]),
      // port "b": Huge pages
      .en_b   (ram_re | itlb_match_huge_we),
      .we_b   (itlb_match_huge_we),
      .addr_b (itlb_match_huge_addr),
      .din_b  (itlb_match_reload_din),
      .dout_b (itlb_match_huge_dout[i])
    );
  
    // ITLB translate registers
    mor1kx_dpram_en_w1st_sclk
    #(
      .ADDR_WIDTH     (OPTION_IMMU_SET_WIDTH),
      .DATA_WIDTH     (OPTION_OPERAND_WIDTH),
      .CLEAR_ON_INIT  (OPTION_IMMU_CLEAR_ON_INIT)
    )
    itlb_trans_regs
    (
      // common clock
      .clk    (clk),
      // port "a": 8KB pages
      .en_a   (ram_re | itlb_trans_we[i]),
      .we_a   (itlb_trans_we[i]),
      .addr_a (itlb_trans_addr),
      .din_a  (itlb_trans_din),
      .dout_a (itlb_trans_dout[i]),
      // port "b": Huge pages
      .en_b   (ram_re | itlb_trans_huge_we),
      .we_b   (itlb_trans_huge_we),
      .addr_b (itlb_trans_huge_addr),
      .din_b  (itlb_trans_reload_din),
      .dout_b (itlb_trans_huge_dout[i])
    );
  end
  endgenerate

endmodule // mor1kx_immu_marocchino
