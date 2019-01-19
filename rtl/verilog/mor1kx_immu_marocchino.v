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
//   Copyright (C) 2015 - 2018 Andrey Bacherov                     //
//                             avbacherov@opencores.org            //
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
  parameter OPTION_IMMU_SET_WIDTH      =  6,
  parameter OPTION_IMMU_WAYS           =  1,
  parameter OPTION_ICACHE_LIMIT_WIDTH  = 32,
  parameter OPTION_IMMU_CLEAR_ON_INIT  =  0
)
(
  // clock & reset
  input                                 cpu_clk,
  input                                 cpu_rst,

  // whole CPU pipe controls
  input                                 pipeline_flush_i,

  // IFETCH's stages advancing controls
  input                                 predict_miss_i,
  input                                 padv_s1_i,
  input                                 jr_gathering_target_i,
  output reg                            s1o_immu_rdy_o,
  output reg                            s1o_immu_upd_o,

  // configuration
  input                                 immu_enable_i,
  input                                 supervisor_mode_i,

  // address translation
  input      [OPTION_OPERAND_WIDTH-1:0] virt_addr_mux_i,
  input      [OPTION_OPERAND_WIDTH-1:0] virt_addr_s1o_i,
  output reg [OPTION_OPERAND_WIDTH-1:0] phys_addr_o,

  // flags
  output reg                            cache_inhibit_o,
  output reg                            tlb_miss_o,
  output reg                            pagefault_o,

  // HW reload
  output                                tlb_reload_req_o,
  input                                 tlb_reload_ack_i,
  output     [OPTION_OPERAND_WIDTH-1:0] tlb_reload_addr_o,
  input      [OPTION_OPERAND_WIDTH-1:0] tlb_reload_data_i,
  output                                tlb_reload_pagefault_o,
  input                                 tlb_reload_pagefault_clear_i,
  output                                tlb_reload_busy_o,

  // SPR interface
  input                          [15:0] spr_bus_addr_i,
  input                                 spr_bus_we_i,
  input                                 spr_bus_stb_i,
  input      [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_i,
  output reg [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_o,
  output                                spr_bus_ack_o
);

  localparam  WAYS_WIDTH = (OPTION_IMMU_WAYS < 2) ? 1 : 2;

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

  wire                             itlb_match_reload_we;
  wire  [OPTION_OPERAND_WIDTH-1:0] itlb_match_reload_din;

  wire                             itlb_trans_reload_we;
  wire  [OPTION_OPERAND_WIDTH-1:0] itlb_trans_reload_din;

  wire                             spr_immu_cs;
  reg                              itlb_match_spr_cs_r;
  reg                              itlb_trans_spr_cs_r;

  wire                       [1:0] spr_way_idx; // from SPR BUS
  reg             [WAYS_WIDTH-1:0] spr_way_idx_r;

  reg  [OPTION_IMMU_SET_WIDTH-1:0] spr_access_addr_r;

  reg                              immucr_spr_cs_r;
  reg   [OPTION_OPERAND_WIDTH-1:0] immucr;

  wire      [OPTION_IMMU_WAYS-1:0] way_hit;
  wire      [OPTION_IMMU_WAYS-1:0] way_huge_hit;

  wire                             tlb_reload_pagefault;
  wire                             tlb_reload_huge;

  // sxe: supervisor execute enable
  // uxe: user exexute enable
  reg                              sxe;
  reg                              uxe;

  genvar                           i;
  integer                          j;


  //---------------//
  // SPR interface //
  //---------------//

  //  we don't expect R/W-collisions for SPRbus vs Write-Back cycles since
  //    SPRbus access start 1-clock later than Write-Back
  //    thanks to MT(F)SPR processing logic (see OMAN)

  // Registering SPR BUS incoming signals.

  // SPR BUS strobe registering
  reg                              spr_bus_stb_r;
  reg                              spr_bus_we_r;
  reg                       [14:0] spr_bus_addr_r;
  reg [(OPTION_OPERAND_WIDTH-1):0] spr_bus_dat_r;
  // ---
  always @(posedge cpu_clk) begin
    if (cpu_rst)
      spr_bus_stb_r <= 1'b0;
    else if (spr_bus_ack_o)
      spr_bus_stb_r <= 1'b0;
    else
      spr_bus_stb_r <= spr_bus_stb_i;
  end // at clock
  // ---
  always @(posedge cpu_clk) begin
    spr_bus_we_r   <= spr_bus_we_i;
    spr_bus_addr_r <= spr_bus_addr_i[14:0];
    spr_bus_dat_r  <= spr_bus_dat_i;
  end


  // SPR BUS transaction states
  localparam [5:0] SPR_IMMU_WAIT  = 6'b000001,
                   SPR_IMMU_WRITE = 6'b000010,
                   SPR_IMMU_RINIT = 6'b000100,
                   SPR_IMMU_RMUX  = 6'b001000,
                   SPR_IMMU_ACK   = 6'b010000,
                   SPR_IMMU_RST   = 6'b100000;
  // SPR BUS transaction state register
  reg [5:0] spr_immu_state_r;
  // SPR BUS transaction particular strobes
  wire      spr_immu_we   = spr_immu_state_r[1];
  wire      spr_immu_re   = spr_immu_state_r[2];
  assign    spr_bus_ack_o = spr_immu_state_r[4];

  // overall IMMU "chip select"
  assign spr_immu_cs = spr_bus_stb_r & (spr_bus_addr_r[14:11] == `OR1K_SPR_IMMU_BASE); // `SPR_BASE

  assign spr_way_idx = {spr_bus_addr_r[10], spr_bus_addr_r[8]};

  // SPR processing cycle: states switching
  always @(posedge cpu_clk) begin
    if (cpu_rst) begin
      spr_immu_state_r <= SPR_IMMU_RST; // on cpu-reset
    end
    else begin
      // synthesis parallel_case
      case (spr_immu_state_r)
        // wait SPR BUS request
        SPR_IMMU_WAIT: begin
          if (spr_immu_cs)
            spr_immu_state_r <= spr_bus_we_r ? SPR_IMMU_WRITE : SPR_IMMU_RINIT; // on spr request take
        end
        // done write and start ACK
        SPR_IMMU_WRITE: spr_immu_state_r <= SPR_IMMU_ACK; // on write completion
        // drop "read" strobe and go to latching read values
        SPR_IMMU_RINIT: spr_immu_state_r <= SPR_IMMU_RMUX; // on read strobe completion
        // latch read data
        SPR_IMMU_RMUX:  spr_immu_state_r <= SPR_IMMU_ACK; // on read result latching
        // back to waiting
        SPR_IMMU_ACK,
        SPR_IMMU_RST:   spr_immu_state_r <= SPR_IMMU_WAIT; // generate ACK / doing reset
        // others
        default:;
      endcase
    end
  end // @ clock

  // SPR processing cycle: controls
  always @(posedge cpu_clk) begin
    // synthesis parallel_case
    case (spr_immu_state_r)
      // wait SPR BUS request
      SPR_IMMU_WAIT: begin
        if (spr_immu_cs) begin
          itlb_match_spr_cs_r <= (|spr_bus_addr_r[10:9]) & ~spr_bus_addr_r[7];
          itlb_trans_spr_cs_r <= (|spr_bus_addr_r[10:9]) &  spr_bus_addr_r[7];
          immucr_spr_cs_r     <= (`SPR_OFFSET(spr_bus_addr_r) == `SPR_OFFSET(`OR1K_SPR_IMMUCR_ADDR));
          spr_way_idx_r       <= spr_way_idx[WAYS_WIDTH-1:0];
          spr_access_addr_r   <= spr_bus_addr_r[OPTION_IMMU_SET_WIDTH-1:0];
        end
      end
      // do nothing
      SPR_IMMU_RINIT:;
      // latch read data
      SPR_IMMU_RMUX: begin
        spr_bus_dat_o  <= itlb_match_spr_cs_r ? itlb_match_dout[spr_way_idx_r] :
                          itlb_trans_spr_cs_r ? itlb_trans_dout[spr_way_idx_r] :
                          immucr_spr_cs_r     ? immucr                         :
                                                {OPTION_OPERAND_WIDTH{1'b0}};
      end
      // back to waiting
      SPR_IMMU_ACK,
      SPR_IMMU_RST: begin
        spr_bus_dat_o       <= {OPTION_OPERAND_WIDTH{1'b0}}; // on ack/rst
        itlb_match_spr_cs_r <= 1'b0; // on ack/rst
        itlb_trans_spr_cs_r <= 1'b0; // on ack/rst
        immucr_spr_cs_r     <= 1'b0; // on ack/rst
        spr_way_idx_r       <= {WAYS_WIDTH{1'b0}}; // on ack/rst
      end
      // others
      default:;
    endcase
  end // @ clock


  // IMMU Control Register
  always @(posedge cpu_clk) begin
    if (cpu_rst)
      immucr <= {OPTION_OPERAND_WIDTH{1'b0}};
    else if (immucr_spr_cs_r & spr_immu_we)
      immucr <= spr_bus_dat_r;
  end // @ clock


  // TAG virtual address (drived by IMMU's super-cache controller)
  reg  [OPTION_OPERAND_WIDTH-1:0] virt_addr_tag_r;


  // Calculate IMMU's output for super-cache
  generate
  for (i = 0; i < OPTION_IMMU_WAYS; i=i+1) begin : ways
    // 8KB page hit
    assign way_hit[i] = (itlb_match_dout[i][31:13] == virt_addr_tag_r[31:13]) & // address hit
                        ~(&itlb_match_huge_dout[i][1:0]) &                      // not valid huge
                        itlb_match_dout[i][0];                                  // valid bit
    // Huge page hit
    assign way_huge_hit[i] = (itlb_match_huge_dout[i][31:24] == virt_addr_tag_r[31:24]) & // address hit
                             itlb_match_huge_dout[i][1] & itlb_match_huge_dout[i][0];     // valid huge
  end
  endgenerate

  reg [OPTION_OPERAND_WIDTH-1:0] phys_addr;
  reg                            cache_inhibit;
  reg                            tlb_miss;

  always @(*) begin
    tlb_miss        = (~tlb_reload_pagefault); // initially "miss"
    phys_addr       = virt_addr_tag_r;
    sxe             = 1'b0;
    uxe             = 1'b0;
    cache_inhibit   = 1'b0;

    for (j = 0; j < OPTION_IMMU_WAYS; j=j+1) begin
      if (way_huge_hit[j] | way_hit[j])
        tlb_miss = 1'b0;

      if (way_huge_hit[j]) begin
        phys_addr       = {itlb_trans_huge_dout[j][31:24], virt_addr_tag_r[23:0]};
        sxe             = itlb_trans_huge_dout[j][6];
        uxe             = itlb_trans_huge_dout[j][7];
        cache_inhibit   = itlb_trans_huge_dout[j][1];
      end
      else if (way_hit[j])begin
        phys_addr       = {itlb_trans_dout[j][31:13], virt_addr_tag_r[12:0]};
        sxe             = itlb_trans_dout[j][6];
        uxe             = itlb_trans_dout[j][7];
        cache_inhibit   = itlb_trans_dout[j][1];
      end

      itlb_match_we[j] = 1'b0;
      if (itlb_match_reload_we & ~tlb_reload_huge)
        itlb_match_we[j] = 1'b1;
      if (j[WAYS_WIDTH-1:0] == spr_way_idx_r)
        itlb_match_we[j] = itlb_match_spr_cs_r & spr_immu_we;

      itlb_trans_we[j] = 1'b0;
      if (itlb_trans_reload_we & ~tlb_reload_huge)
        itlb_trans_we[j] = 1'b1;
      if (j[WAYS_WIDTH-1:0] == spr_way_idx_r)
        itlb_trans_we[j] = itlb_trans_spr_cs_r & spr_immu_we;
    end // loop by ways
  end

  wire pagefault = (supervisor_mode_i ? ~sxe : ~uxe) & (~tlb_reload_busy_o);


  // match 8KB input address
  //  a) SPR BUS read/write access
  //  b) Re-read after SPR BUS read/write access
  //  c) Regular IFETCH advance
  assign itlb_match_addr = itlb_match_spr_cs_r ? spr_access_addr_r :
                                                 virt_addr_s1o_i[(OPTION_IMMU_SET_WIDTH+13-1):13];
  // match huge address and write command
  assign itlb_match_huge_addr = virt_addr_s1o_i[(OPTION_IMMU_SET_WIDTH+24-1):24];
  assign itlb_match_huge_we   = itlb_match_reload_we & tlb_reload_huge;
  // match data in
  assign itlb_match_din = itlb_match_reload_we ? itlb_match_reload_din : spr_bus_dat_r;


  // translation 8KB input address
  //  a) SPR BUS read/write access
  //  b) Re-read after SPR BUS read/write access
  //  c) Regular IFETCH advance
  assign itlb_trans_addr = itlb_trans_spr_cs_r ? spr_access_addr_r :
                                                 virt_addr_s1o_i[(OPTION_IMMU_SET_WIDTH+13-1):13];
  // translation huge address and write command
  assign itlb_trans_huge_addr = virt_addr_s1o_i[(OPTION_IMMU_SET_WIDTH+24-1):24];
  assign itlb_trans_huge_we   = itlb_trans_reload_we & tlb_reload_huge;
  // translation data in
  assign itlb_trans_din = itlb_trans_reload_we ? itlb_trans_reload_din : spr_bus_dat_r;


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

    /*
    // local declarations
    reg                            tlb_reload_req_r; // HW reload
    reg [OPTION_OPERAND_WIDTH-1:0] tlb_reload_addr_r; // HW reload
    reg                            tlb_reload_pagefault_r; // HW reload
    reg                            tlb_reload_huge_r; // HW reload
    reg                            itlb_trans_reload_we_r;
    reg [OPTION_OPERAND_WIDTH-1:0] itlb_trans_reload_din_r; // HW reload
    reg                            itlb_match_reload_we_r; // HW reload
    reg [OPTION_OPERAND_WIDTH-1:0] itlb_match_reload_din_r; // HW reload

    // assignement connections to main code
    assign tlb_reload_req_o       = tlb_reload_req_r; // HW reload
    assign tlb_reload_addr_o      = tlb_reload_addr_r; // HW reload
    assign tlb_reload_pagefault   = tlb_reload_pagefault_r; // HW reload
    assign tlb_reload_huge        = tlb_reload_huge_r; // HW reload
    assign itlb_trans_reload_we   = itlb_trans_reload_we_r; // HW reload
    assign itlb_trans_reload_din  = itlb_trans_reload_din_r; // HW reload
    assign itlb_match_reload_we   = itlb_match_reload_we_r;
    assign itlb_match_reload_din  = itlb_match_reload_din_r; // HW reload

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

    reg [3:0] tlb_reload_state = TLB_IDLE;
    wire      do_reload;

    assign do_reload              = tlb_miss_o & (immucr[31:10] != 22'd0);
    assign tlb_reload_busy_o      = (tlb_reload_state != TLB_IDLE) | do_reload;
    assign tlb_reload_pagefault_o = tlb_reload_pagefault_r & ~tlb_reload_pagefault_clear_i;

    always @(posedge cpu_clk) begin
      if (cpu_rst)
        tlb_reload_pagefault_r <= 1'b0;
      else if(tlb_reload_pagefault_clear_i)
        tlb_reload_pagefault_r <= 1'b0;

      itlb_trans_reload_we_r  <= 1'b0;
      itlb_trans_reload_din_r <= {OPTION_OPERAND_WIDTH{1'b0}};
      itlb_match_reload_we_r  <= 1'b0;
      itlb_match_reload_din_r <= {OPTION_OPERAND_WIDTH{1'b0}};

      // synthesis parallel_case
      case (tlb_reload_state)
        TLB_IDLE: begin
          tlb_reload_huge_r <= 1'b0;
          tlb_reload_req_r  <= 1'b0;
          if (do_reload) begin
            tlb_reload_req_r  <= 1'b1;
            tlb_reload_addr_r <= {immucr[31:10],virt_addr_tag_r[31:24],2'b00};
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
          tlb_reload_huge_r <= 1'b0;
          if (tlb_reload_ack_i) begin
            if (tlb_reload_data_i[31:13] == 0) begin
              tlb_reload_pagefault_r <= 1'b1;
              tlb_reload_req_r       <= 1'b0;
              tlb_reload_state       <= TLB_IDLE;
            end
            else if (tlb_reload_data_i[9]) begin
              tlb_reload_huge_r <= 1'b1;
              tlb_reload_req_r  <= 1'b0;
              tlb_reload_state  <= TLB_GET_PTE;
            end
            else begin
              tlb_reload_addr_r <= {tlb_reload_data_i[31:13],virt_addr_tag_r[23:13],2'b00};
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
            tlb_reload_req_r <= 1'b0;
            // Check PRESENT bit
            if (~tlb_reload_data_i[10]) begin
              tlb_reload_pagefault_r <= 1'b1;
              tlb_reload_state       <= TLB_IDLE;
            end
            else begin
              // Translate register generation.
              // PPN
              itlb_trans_reload_din_r[31:13] <= tlb_reload_data_i[31:13];
              // UXE = X & U
              itlb_trans_reload_din_r[7] <= tlb_reload_data_i[8] & tlb_reload_data_i[6];
              // SXE = X
              itlb_trans_reload_din_r[6] <= tlb_reload_data_i[8];
              // Dirty, Accessed, Weakly-Ordered-Memory, Writeback cache,
              // Cache inhibit, Cache coherent
              itlb_trans_reload_din_r[5:0] <= tlb_reload_data_i[5:0];
              itlb_trans_reload_we_r       <= 1'b1;

              // Match register generation.
              // VPN
              itlb_match_reload_din_r[31:13] <= virt_addr_tag_r[31:13];
              // PL1
              itlb_match_reload_din_r[1] <= tlb_reload_huge_r;
              // Valid
              itlb_match_reload_din_r[0] <= 1'b1;
              itlb_match_reload_we_r     <= 1'b1;

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
    assign tlb_reload_pagefault_o = 1'b0; // SW reload
    assign tlb_reload_busy_o      = 1'b0; // SW reload
    assign tlb_reload_req_o       = 1'b0; // SW reload
    assign tlb_reload_addr_o      = {OPTION_OPERAND_WIDTH{1'b0}}; // SW reload
    assign tlb_reload_pagefault   = 1'b0; // SW reload
    assign tlb_reload_huge        = 1'b0; // SW reload
    assign itlb_trans_reload_we   = 1'b0; // SW reload
    assign itlb_trans_reload_din  = {OPTION_OPERAND_WIDTH{1'b0}}; // SW reload
    assign itlb_match_reload_we   = 1'b0; // SW reload
    assign itlb_match_reload_din  = {OPTION_OPERAND_WIDTH{1'b0}}; // SW reload
  end // HW/SW reload
  endgenerate

  // Read access for RAM blocks if:
  //  1) Read to update super-cache
  wire immu_cache_re;
  //  2) SPR read access
  // Overall:
  wire ram_re = immu_cache_re | spr_immu_re;

  generate
  for (i = 0; i < OPTION_IMMU_WAYS; i=i+1) begin : itlb
    // ITLB match registers
    mor1kx_dpram_en_w1st
    #(
      .ADDR_WIDTH     (OPTION_IMMU_SET_WIDTH),
      .DATA_WIDTH     (OPTION_OPERAND_WIDTH),
      .CLEAR_ON_INIT  (OPTION_IMMU_CLEAR_ON_INIT)
    )
    itlb_match_regs
    (
      // port "a": 8KB pages
      .clk_a  (cpu_clk),
      .en_a   (ram_re | itlb_match_we[i]),
      .we_a   (itlb_match_we[i]),
      .addr_a (itlb_match_addr),
      .din_a  (itlb_match_din),
      .dout_a (itlb_match_dout[i]),
      // port "b": Huge pages
      .clk_b  (cpu_clk),
      .en_b   (ram_re | itlb_match_huge_we),
      .we_b   (itlb_match_huge_we),
      .addr_b (itlb_match_huge_addr),
      .din_b  (itlb_match_reload_din),
      .dout_b (itlb_match_huge_dout[i])
    );

    // ITLB translate registers
    mor1kx_dpram_en_w1st
    #(
      .ADDR_WIDTH     (OPTION_IMMU_SET_WIDTH),
      .DATA_WIDTH     (OPTION_OPERAND_WIDTH),
      .CLEAR_ON_INIT  (OPTION_IMMU_CLEAR_ON_INIT)
    )
    itlb_trans_regs
    (
      // port "a": 8KB pages
      .clk_a  (cpu_clk),
      .en_a   (ram_re | itlb_trans_we[i]),
      .we_a   (itlb_trans_we[i]),
      .addr_a (itlb_trans_addr),
      .din_a  (itlb_trans_din),
      .dout_a (itlb_trans_dout[i]),
      // port "b": Huge pages
      .clk_b  (cpu_clk),
      .en_b   (ram_re | itlb_trans_huge_we),
      .we_b   (itlb_trans_huge_we),
      .addr_b (itlb_trans_huge_addr),
      .din_b  (itlb_trans_reload_din),
      .dout_b (itlb_trans_huge_dout[i])
    );
  end
  endgenerate


  // Extention to cache_inhibit
  //   Work around IMMU just for symmetric with DMMU?
  wire cache_inhibit_limit_immu_off; // state: OFF
  wire cache_inhibit_limit_immu_uon; // state: UPDATE & DMMU is ON
  wire cache_inhibit_limit_immu_uof; // state: UPDATE & DMMU is OFF
  // ---
  generate
  if (OPTION_ICACHE_LIMIT_WIDTH < OPTION_OPERAND_WIDTH) begin
    assign cache_inhibit_limit_immu_off =
      (virt_addr_mux_i[OPTION_OPERAND_WIDTH-1:OPTION_ICACHE_LIMIT_WIDTH] != 0);
    assign cache_inhibit_limit_immu_uon =
      (phys_addr[OPTION_OPERAND_WIDTH-1:OPTION_ICACHE_LIMIT_WIDTH] != 0);
    assign cache_inhibit_limit_immu_uof =
      (virt_addr_s1o_i[OPTION_OPERAND_WIDTH-1:OPTION_ICACHE_LIMIT_WIDTH] != 0);
  end
  else begin
    assign cache_inhibit_limit_immu_off = 1'b0;
    assign cache_inhibit_limit_immu_uon = 1'b0;
    assign cache_inhibit_limit_immu_uof = 1'b0;
  end
  endgenerate


  // states of IMMU super-cache FSM
  localparam [4:0] IMMU_CACHE_EMPTY = 5'b00001,
                   IMMU_CACHE_OFF   = 5'b00010,
                   IMMU_CACHE_RE    = 5'b00100,
                   IMMU_CACHE_UPD   = 5'b01000,
                   IMMU_CACHE_ON    = 5'b10000;
  // ---
  reg [4:0] immu_cache_state;

  // particular states:
  assign immu_cache_re  = immu_cache_state[2];
  wire   immu_cache_upd = immu_cache_state[3];

  // additional flags
  reg supervisor_mode_c; // "cached"
  reg hit_08Kb_r;
  reg hit_16Mb_r; // "huge"

  // most significant bits of last hit virtual address
  localparam  VIRT_ADDR_HIT_WIDTH    = OPTION_OPERAND_WIDTH - 13;
  localparam  VIRT_ADDR_HIT_MSB      = VIRT_ADDR_HIT_WIDTH  -  1;
  localparam  VIRT_ADDR_HIT_16MB_LSB = 24 - 13;
  // ---
  reg [VIRT_ADDR_HIT_MSB:0] virt_addr_hit_r;

  // check if IMMU's cache miss
  wire immu_cache_hit = (virt_addr_mux_i[(OPTION_OPERAND_WIDTH-1):24] ==
                         virt_addr_hit_r[VIRT_ADDR_HIT_MSB:VIRT_ADDR_HIT_16MB_LSB]) &
                        (hit_08Kb_r ? (virt_addr_mux_i[23:13] ==
                                       virt_addr_hit_r[VIRT_ADDR_HIT_16MB_LSB-1:0]) :
                                      hit_16Mb_r) &
                        (supervisor_mode_c == supervisor_mode_i);

  // IMMU's super-cache FSM
  always @(posedge cpu_clk) begin
    if (pipeline_flush_i) begin
      s1o_immu_upd_o    <= 1'b0;
      s1o_immu_rdy_o    <= 1'b0;
      supervisor_mode_c <= 1'b0;
      hit_08Kb_r        <= 1'b0;
      hit_16Mb_r        <= 1'b0;
      cache_inhibit_o   <= 1'b0;
      tlb_miss_o        <= 1'b0;
      pagefault_o       <= 1'b0;
      immu_cache_state  <= IMMU_CACHE_EMPTY; // reset / flush / predict-miss
    end
    else begin
      // synthesis parallel_case
      case (immu_cache_state)
        // waiting 1-st request after reset / flush / predict-miss
        IMMU_CACHE_EMPTY: begin
          if (padv_s1_i) begin
            s1o_immu_upd_o   <= 1'b1;
            immu_cache_state <= IMMU_CACHE_RE;
          end
        end // empty
        // Read IMMU's tables
        IMMU_CACHE_RE: begin
          if (predict_miss_i) begin
            s1o_immu_upd_o   <= 1'b0;
            immu_cache_state <= IMMU_CACHE_EMPTY;
          end
          else begin
            immu_cache_state <= IMMU_CACHE_UPD;
          end
        end // read
        // update cache output
        IMMU_CACHE_UPD: begin
          if (predict_miss_i) begin
            s1o_immu_upd_o   <= 1'b0;
            immu_cache_state <= IMMU_CACHE_EMPTY;
          end
          else begin
            if (immu_enable_i) begin
              supervisor_mode_c <= supervisor_mode_i;
              hit_08Kb_r        <= (|way_hit);
              hit_16Mb_r        <= (|way_huge_hit);
              cache_inhibit_o   <= cache_inhibit | cache_inhibit_limit_immu_uon; // UPD, IMMU-ON
              tlb_miss_o        <= tlb_miss;
              pagefault_o       <= pagefault;
              immu_cache_state  <= IMMU_CACHE_ON;
            end
            else begin
              supervisor_mode_c <= 1'b0;
              hit_08Kb_r        <= 1'b0;
              hit_16Mb_r        <= 1'b0;
              cache_inhibit_o   <= cache_inhibit_limit_immu_uof;// UPD, IMMU-OFF
              tlb_miss_o        <= 1'b0;
              pagefault_o       <= 1'b0;
              immu_cache_state  <= IMMU_CACHE_OFF;
            end
            s1o_immu_upd_o <= 1'b0;
            s1o_immu_rdy_o <= 1'b1;
          end
        end // update
        // IMMU is ON
        IMMU_CACHE_ON: begin
          if (padv_s1_i) begin
            if (jr_gathering_target_i) begin
              s1o_immu_rdy_o <= 1'b0;
            end
            else if (~immu_cache_hit) begin
              s1o_immu_upd_o   <= 1'b1;
              s1o_immu_rdy_o   <= 1'b0;
              immu_cache_state <= IMMU_CACHE_RE;
            end
            else begin
              s1o_immu_rdy_o <= 1'b1;
            end
          end // stage #1 advance
          else if (predict_miss_i) begin
            s1o_immu_rdy_o   <= 1'b0;
          end
          else if (spr_bus_ack_o | (~immu_enable_i)) begin // IMMU is ON
            s1o_immu_upd_o   <= s1o_immu_rdy_o;
            s1o_immu_rdy_o   <= 1'b0;
            immu_cache_state <= s1o_immu_rdy_o ? IMMU_CACHE_RE : IMMU_CACHE_EMPTY; // after SPR access / ON -> OFF
          end // Re-Read after SPR access
        end // rdy
        // IMMU is OFF
        IMMU_CACHE_OFF: begin
          if (padv_s1_i) begin
            if (jr_gathering_target_i) begin
              s1o_immu_rdy_o <= 1'b0;
            end
            else begin
              cache_inhibit_o <= cache_inhibit_limit_immu_off; // IMMU is OFF
              s1o_immu_rdy_o  <= 1'b1;
            end
          end // stage #1 advance
          else if (predict_miss_i) begin
            s1o_immu_rdy_o <= 1'b0;
          end
          else if (immu_enable_i) begin // OFF -> ON
            s1o_immu_upd_o   <= s1o_immu_rdy_o;
            s1o_immu_rdy_o   <= 1'b0;
            immu_cache_state <= s1o_immu_rdy_o ? IMMU_CACHE_RE : IMMU_CACHE_EMPTY; // OFF -> ON
          end
        end // off
        // do nothing by default
        default:;
      endcase
    end
  end // @ clock

  // Registering virtual address TAG
  always @(posedge cpu_clk) begin
    if (immu_cache_re)
      virt_addr_tag_r <= virt_addr_s1o_i;
  end // @ clock

  // IMMU's super-cache hit-address
  always @(posedge cpu_clk) begin
    if (immu_cache_upd)
      virt_addr_hit_r <= virt_addr_tag_r[(OPTION_OPERAND_WIDTH-1):13];
  end // @ clock

  // IMMU's physical address output
  always @(posedge cpu_clk) begin
    // synthesis parallel_case
    case (immu_cache_state)
      // update cache output
      IMMU_CACHE_UPD: begin
        phys_addr_o <= immu_enable_i ? phys_addr : virt_addr_tag_r; // update IMMU's output
      end // update
      // IMMU is ON
      IMMU_CACHE_ON: begin
        if (padv_s1_i)
          phys_addr_o <= hit_08Kb_r ?
                          {phys_addr_o[(OPTION_OPERAND_WIDTH-1):13],virt_addr_mux_i[12:0]} : // IMMU is ON
                          {phys_addr_o[(OPTION_OPERAND_WIDTH-1):24],virt_addr_mux_i[23:0]}; // IMMU is ON
      end // rdy
      // IMMU is OFF
      IMMU_CACHE_OFF: begin
        if (padv_s1_i)
          phys_addr_o <= virt_addr_mux_i; // IMMU is OFF
      end // off
      // do nothing by default
      default:;
    endcase
  end // @ clock

endmodule // mor1kx_immu_marocchino
