/////////////////////////////////////////////////////////////////////
//                                                                 //
//  mor1kx_dmmu_marocchino                                         //
//                                                                 //
//  Description:                                                   //
//    Data MMU implementation                                      //
//    Tightly coupled with MAROCCHINO LSU                          //
//    Based on mor1kx_dmmu                                         //
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

module mor1kx_dmmu_marocchino
#(
  parameter FEATURE_DMMU_HW_TLB_RELOAD  = "NONE",
  parameter OPTION_OPERAND_WIDTH        = 32,
  parameter OPTION_DMMU_SET_WIDTH       =  6,
  parameter OPTION_DMMU_WAYS            =  1,
  parameter OPTION_DMMU_CLEAR_ON_INIT   =  0
)
(
  // clocks and resest
  input                                 clk,
  input                                 rst,

  // pipe controls
  input                                 lsu_takes_ls_i,
  input                                 pipeline_flush_i,

  // exceptions
  input                                 lsu_excepts_any_i,

  // configuration
  input                                 enable_i,
  input                                 supervisor_mode_i,

  // commnads
  input                                 lsu_store_i,
  input                                 lsu_load_i,

  // address translation
  input      [OPTION_OPERAND_WIDTH-1:0] virt_addr_i,
  input      [OPTION_OPERAND_WIDTH-1:0] virt_addr_cmd_i,
  output     [OPTION_OPERAND_WIDTH-1:0] phys_addr_cmd_o,

  // flags
  output reg                            cache_inhibit_o,
  output reg                            tlb_miss_o,
  output                                pagefault_o,

  // HW reload
  output reg                            tlb_reload_req_o,
  output                                tlb_reload_busy_o,
  input                                 tlb_reload_ack_i,
  output reg [OPTION_OPERAND_WIDTH-1:0] tlb_reload_addr_o,
  input      [OPTION_OPERAND_WIDTH-1:0] tlb_reload_data_i,
  output                                tlb_reload_pagefault_o,
  input                                 tlb_reload_pagefault_clear_i,

  // SPR interface
  input                          [15:0] spr_bus_addr_i,
  input                                 spr_bus_we_i,
  input                                 spr_bus_stb_i,
  input      [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_i,
  output reg [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_o,
  output reg                            spr_bus_ack_o
);

  wire  [OPTION_OPERAND_WIDTH-1:0] dtlb_match_dout[OPTION_DMMU_WAYS-1:0];
  wire [OPTION_DMMU_SET_WIDTH-1:0] dtlb_match_addr;
  reg       [OPTION_DMMU_WAYS-1:0] dtlb_match_we;
  wire  [OPTION_OPERAND_WIDTH-1:0] dtlb_match_din;

  wire  [OPTION_OPERAND_WIDTH-1:0] dtlb_match_huge_dout[OPTION_DMMU_WAYS-1:0];
  wire [OPTION_DMMU_SET_WIDTH-1:0] dtlb_match_huge_addr;
  wire                             dtlb_match_huge_we;

  wire  [OPTION_OPERAND_WIDTH-1:0] dtlb_trans_dout[OPTION_DMMU_WAYS-1:0];
  wire [OPTION_DMMU_SET_WIDTH-1:0] dtlb_trans_addr;
  reg       [OPTION_DMMU_WAYS-1:0] dtlb_trans_we;
  wire  [OPTION_OPERAND_WIDTH-1:0] dtlb_trans_din;

  wire  [OPTION_OPERAND_WIDTH-1:0] dtlb_trans_huge_dout[OPTION_DMMU_WAYS-1:0];
  wire [OPTION_DMMU_SET_WIDTH-1:0] dtlb_trans_huge_addr;
  wire                             dtlb_trans_huge_we;

  reg                              dtlb_match_reload_we;
  reg   [OPTION_OPERAND_WIDTH-1:0] dtlb_match_reload_din;

  reg                              dtlb_trans_reload_we;
  reg   [OPTION_OPERAND_WIDTH-1:0] dtlb_trans_reload_din;

  reg                              dtlb_match_spr_cs_r;
  reg                              dtlb_trans_spr_cs_r;

  wire                             spr_dmmu_cs;
  reg                              spr_dmmu_we_r;  // write on next posedge clock
  reg                              spr_dmmu_re_r;  // read on next posedge clock
  reg                              spr_dmmu_mux_r; // mux read output and latch it

  reg                              dmmucr_spr_cs_r;
  reg   [OPTION_OPERAND_WIDTH-1:0] dmmucr;

  reg                        [1:0] spr_way_idx_r;

  wire      [OPTION_DMMU_WAYS-1:0] way_hit;
  wire      [OPTION_DMMU_WAYS-1:0] way_huge_hit;

  reg                              tlb_reload_pagefault;
  reg                              tlb_reload_huge;

  // ure: user read enable
  // uwe: user write enable
  // sre: supervisor read enable
  // swe: supervisor write enable
  reg                              ure;
  reg                              uwe;
  reg                              sre;
  reg                              swe;

  genvar                           i;


  // Enable for RAM blocks if:
  //  1) regular LSU advance
  //     (we don't care about exceptions here, because
  //      we force local enable-r OFF if an exception is asserted)
  //  2) SPR access
  wire ram_re = (lsu_takes_ls_i & enable_i) | spr_dmmu_re_r;


  // Stored "DMMU enable" and "Supevisor Mode" flags
  // (for masking DMMU output flags, but not for advancing)
  reg enable_r;
  reg supervisor_mode_r;
  reg cmd_store_r, cmd_load_r;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      enable_r          <= 1'b0;
      supervisor_mode_r <= 1'b0;
      cmd_store_r       <= 1'b0;
      cmd_load_r        <= 1'b0;
    end
    else if (lsu_excepts_any_i | pipeline_flush_i | spr_dmmu_cs) begin
      enable_r          <= 1'b0;
      supervisor_mode_r <= 1'b0;
      cmd_store_r       <= 1'b0;
      cmd_load_r        <= 1'b0;
    end
    else if (lsu_takes_ls_i) begin
      if (enable_i) begin
        enable_r          <= 1'b1;
        supervisor_mode_r <= supervisor_mode_i;
        cmd_store_r       <= lsu_store_i;
        cmd_load_r        <= lsu_load_i;
      end
      else begin
        enable_r          <= 1'b0;
        supervisor_mode_r <= 1'b0;
        cmd_store_r       <= 1'b0;
        cmd_load_r        <= 1'b0;
      end
    end
  end // @ clock


  //---------------//
  // SPR interface //
  //---------------//

  //   We don't expect R/W-collisions for SPRbus vs LSU advance
  // because we execute l.mt(f)spr after pipeline stalling (see OMAN)

  assign spr_dmmu_cs = spr_bus_stb_i & (`SPR_BASE(spr_bus_addr_i) == `OR1K_SPR_DMMU_BASE);

  // SPR processing cycle
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      dtlb_match_spr_cs_r <= 1'b0;
      dtlb_trans_spr_cs_r <= 1'b0;
      dmmucr_spr_cs_r     <= 1'b0;
      spr_way_idx_r       <= 2'd0;
      spr_bus_ack_o       <= 1'b0;
      spr_dmmu_we_r       <= 1'b0;
      spr_dmmu_re_r       <= 1'b0;
      spr_dmmu_mux_r      <= 1'b0;
      spr_bus_dat_o       <= {OPTION_OPERAND_WIDTH{1'b0}};
    end
    else if (spr_bus_ack_o) begin
      dtlb_match_spr_cs_r <= 1'b0;
      dtlb_trans_spr_cs_r <= 1'b0;
      dmmucr_spr_cs_r     <= 1'b0;
      spr_way_idx_r       <= 2'd0;
      spr_bus_ack_o       <= 1'b0;
      spr_dmmu_we_r       <= 1'b0;
      spr_dmmu_re_r       <= 1'b0;
      spr_dmmu_mux_r      <= 1'b0;
      spr_bus_dat_o       <= {OPTION_OPERAND_WIDTH{1'b0}};
    end
    else if (spr_dmmu_mux_r) begin
      dtlb_match_spr_cs_r <= dtlb_match_spr_cs_r;
      dtlb_trans_spr_cs_r <= dtlb_trans_spr_cs_r;
      dmmucr_spr_cs_r     <= dmmucr_spr_cs_r;
      spr_way_idx_r       <= spr_way_idx_r;
      spr_dmmu_we_r       <= 1'b0;
      spr_dmmu_re_r       <= 1'b0;
      spr_dmmu_mux_r      <= 1'b0;
      spr_bus_ack_o       <= 1'b1;
      spr_bus_dat_o       <= dtlb_match_spr_cs_r ? dtlb_match_dout[spr_way_idx_r] :
                             dtlb_trans_spr_cs_r ? dtlb_trans_dout[spr_way_idx_r] :
                             dmmucr_spr_cs_r     ? dmmucr                         :
                                                   {OPTION_OPERAND_WIDTH{1'b0}};
    end
    else if (spr_dmmu_re_r) begin
      dtlb_match_spr_cs_r <= dtlb_match_spr_cs_r;
      dtlb_trans_spr_cs_r <= dtlb_trans_spr_cs_r;
      dmmucr_spr_cs_r     <= dmmucr_spr_cs_r;
      spr_way_idx_r       <= spr_way_idx_r;
      spr_dmmu_we_r       <= 1'b0;
      spr_dmmu_re_r       <= 1'b0;
      spr_dmmu_mux_r      <= 1'b1;
      spr_bus_ack_o       <= 1'b0;
      spr_bus_dat_o       <= {OPTION_OPERAND_WIDTH{1'b0}};
    end
    else if (spr_dmmu_cs) begin
      dtlb_match_spr_cs_r <= (|spr_bus_addr_i[10:9]) & ~spr_bus_addr_i[7];
      dtlb_trans_spr_cs_r <= (|spr_bus_addr_i[10:9]) &  spr_bus_addr_i[7];
      dmmucr_spr_cs_r     <= (`SPR_OFFSET(spr_bus_addr_i) == `SPR_OFFSET(`OR1K_SPR_DMMUCR_ADDR));
      spr_way_idx_r       <= {spr_bus_addr_i[10], spr_bus_addr_i[8]};
      spr_dmmu_we_r       <= spr_bus_we_i;
      spr_dmmu_re_r       <= ~spr_bus_we_i;
      spr_dmmu_mux_r      <= 1'b0;
      spr_bus_ack_o       <= spr_bus_we_i; // write on next posedge of clock and finish
      spr_bus_dat_o       <= {OPTION_OPERAND_WIDTH{1'b0}};
    end
  end // @ clock


  // Process DMMU Control Register
  //  # DMMUCR proc
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      dmmucr <= {OPTION_OPERAND_WIDTH{1'b0}};
    else if (dmmucr_spr_cs_r & spr_dmmu_we_r)
      dmmucr <= spr_bus_dat_i;
  end


  generate
  for (i = 0; i < OPTION_DMMU_WAYS; i=i+1) begin : ways
    // 8KB page hit
    assign way_hit[i] = (dtlb_match_dout[i][31:13] == virt_addr_cmd_i[31:13]) & // address match
                        ~(&dtlb_match_huge_dout[i][1:0]) &                      // ~ huge valid
                         dtlb_match_dout[i][0] &                                // valid bit
                         enable_r;                                              // mmu enabled
    // Huge page hit
    assign way_huge_hit[i] = (dtlb_match_huge_dout[i][31:24] == virt_addr_cmd_i[31:24]) & // address match
                             (&dtlb_match_huge_dout[i][1:0]) &                            // ~ huge valid
                             enable_r;                                                    // mmu enabled
  end
  endgenerate


  reg [OPTION_OPERAND_WIDTH-1:0] phys_addr;

  integer j;

  always @(*) begin
    tlb_miss_o      = ~tlb_reload_pagefault & enable_r;
    phys_addr       = virt_addr_cmd_i;
    ure             = 1'b0;
    uwe             = 1'b0;
    sre             = 1'b0;
    swe             = 1'b0;
    cache_inhibit_o = 1'b0;

    for (j = 0; j < OPTION_DMMU_WAYS; j=j+1) begin
      if (way_huge_hit[j] | way_hit[j])
        tlb_miss_o = 1'b0;

      if (way_huge_hit[j]) begin
        phys_addr       = {dtlb_trans_huge_dout[j][31:24], virt_addr_cmd_i[23:0]};
        ure             = dtlb_trans_huge_dout[j][6];
        uwe             = dtlb_trans_huge_dout[j][7];
        sre             = dtlb_trans_huge_dout[j][8];
        swe             = dtlb_trans_huge_dout[j][9];
        cache_inhibit_o = dtlb_trans_huge_dout[j][1];
      end
      else if (way_hit[j])begin
        phys_addr       = {dtlb_trans_dout[j][31:13], virt_addr_cmd_i[12:0]};
        ure             = dtlb_trans_dout[j][6];
        uwe             = dtlb_trans_dout[j][7];
        sre             = dtlb_trans_dout[j][8];
        swe             = dtlb_trans_dout[j][9];
        cache_inhibit_o = dtlb_trans_dout[j][1];
      end

      dtlb_match_we[j] = 1'b0;
      if (dtlb_match_reload_we)
        dtlb_match_we[j] = 1'b1;
      if (j == spr_way_idx_r)
        dtlb_match_we[j] = dtlb_match_spr_cs_r & spr_dmmu_we_r;

      dtlb_trans_we[j] = 1'b0;
      if (dtlb_trans_reload_we)
        dtlb_trans_we[j] = 1'b1;
      if (j == spr_way_idx_r)
        dtlb_trans_we[j] = dtlb_trans_spr_cs_r & spr_dmmu_we_r;
    end // loop by ways
  end // always

  assign pagefault_o = (supervisor_mode_r ? ((~swe & cmd_store_r) | (~sre & cmd_load_r)) :
                                            ((~uwe & cmd_store_r) | (~ure & cmd_load_r))) &
                       ~tlb_reload_busy_o & enable_r;

 `ifdef SIM_SMPL_SOC // MAROCCHINO_TODO
  assign phys_addr_cmd_o = phys_addr;
 `else
  assign phys_addr_cmd_o = {phys_addr[OPTION_OPERAND_WIDTH-1:2],2'd0};
 `endif


  // match 8KB input address
  assign dtlb_match_addr =
    (dtlb_match_spr_cs_r & (spr_dmmu_we_r | spr_dmmu_re_r)) ? spr_bus_addr_i[OPTION_DMMU_SET_WIDTH-1:0] :
                                                              virt_addr_i[13+(OPTION_DMMU_SET_WIDTH-1):13];
  // match huge address and write command
  assign dtlb_match_huge_addr = virt_addr_i[24+(OPTION_DMMU_SET_WIDTH-1):24];
  assign dtlb_match_huge_we   = dtlb_match_reload_we & tlb_reload_huge;
  // match data in
  assign dtlb_match_din = dtlb_match_reload_we ? dtlb_match_reload_din : spr_bus_dat_i;


  // translation 8KB input address
  assign dtlb_trans_addr =
    (dtlb_trans_spr_cs_r & (spr_dmmu_we_r | spr_dmmu_re_r)) ? spr_bus_addr_i[OPTION_DMMU_SET_WIDTH-1:0] :
                                                              virt_addr_i[13+(OPTION_DMMU_SET_WIDTH-1):13];
  // translation huge address and write command
  assign dtlb_trans_huge_addr = virt_addr_i[24+(OPTION_DMMU_SET_WIDTH-1):24];
  assign dtlb_trans_huge_we   = dtlb_trans_reload_we & tlb_reload_huge;
  // translation data in
  assign dtlb_trans_din = dtlb_trans_reload_we ? dtlb_trans_reload_din : spr_bus_dat_i;

  /*
  localparam [3:0] TLB_IDLE             = 4'b0001,
                   TLB_GET_PTE_POINTER  = 4'b0010,
                   TLB_GET_PTE          = 4'b0100,
                   TLB_READ             = 4'b1000;*/

  generate
  /* verilator lint_off WIDTH */
  if (FEATURE_DMMU_HW_TLB_RELOAD != "NONE") begin
  /* verilator lint_on WIDTH */

    initial begin
      $display("DMMU ERROR: HW TLB reload is not implemented in MAROCCHINO");
      $finish();
    end
    /*
    // Hardware TLB reload
    // Compliant with the suggestion outlined in this thread:
    // http://lists.openrisc.net/pipermail/openrisc/2013-July/001806.html
    //
    // PTE layout:
    // | 31 ... 13 | 12 |  11  |   10  | 9 | 8 | 7 | 6 | 5 | 4 | 3 | 2 | 1 | 0 |
    // |    PPN    | Reserved  |PRESENT| L | X | W | U | D | A |WOM|WBC|CI |CC |
    //
    // Where X/W/U maps into SWE/SRE/UWE/URE like this:
    // X | W | U    SWE | SRE | UWE | URE
    // ----------   ---------------------
    // x | 0 | 0  =  0  |  1  |  0  |  0
    // x | 0 | 1  =  0  |  1  |  0  |  1
    // x | 1 | 0  =  1  |  1  |  0  |  0
    // x | 1 | 1  =  1  |  1  |  1  |  1

    reg [3:0] tlb_reload_state = TLB_IDLE;
    wire      do_reload;

    assign do_reload = enable_r & tlb_miss_o & (dmmucr[31:10] != 0) & (cmd_load_r | cmd_store_r);

    assign tlb_reload_busy_o = enable_r & (tlb_reload_state != TLB_IDLE) | do_reload;

    assign tlb_reload_pagefault_o = tlb_reload_pagefault & ~tlb_reload_pagefault_clear_i;

    always @(posedge clk) begin
      if (tlb_reload_pagefault_clear_i)
        tlb_reload_pagefault  <= 1'b0;

      dtlb_trans_reload_we  <= 1'b0;
      dtlb_trans_reload_din <= {OPTION_OPERAND_WIDTH{1'b0}};
      dtlb_match_reload_we  <= 1'b0;
      dtlb_match_reload_din <= {OPTION_OPERAND_WIDTH{1'b0}};

      case (tlb_reload_state)
        TLB_IDLE: begin
          tlb_reload_huge   <= 1'b0;
          tlb_reload_req_o  <= 1'b0;
          if (do_reload) begin
            tlb_reload_req_o  <= 1'b1;
            tlb_reload_addr_o <= {dmmucr[31:10], virt_addr_cmd_i[31:24], 2'b00};
            tlb_reload_state  <= TLB_GET_PTE_POINTER;
          end
        end

        //
        // Here we get the pointer to the PTE table, next is to fetch
        // the actual pte from the offset in the table.
        // The offset is calculated by:
        // ((virt_addr_match >> PAGE_BITS) & (PTE_CNT-1)) << 2
        // Where PAGE_BITS is 13 (8 kb page) and PTE_CNT is 2048
        // (number of PTEs in the PTE table)
        //
        TLB_GET_PTE_POINTER: begin
          tlb_reload_huge <= 1'b0;
          if (tlb_reload_ack_i) begin
            if (tlb_reload_data_i[31:13] == 0) begin
              tlb_reload_pagefault  <= 1'b1;
              tlb_reload_req_o      <= 1'b0;
              tlb_reload_state      <= TLB_IDLE;
            end
            else if (tlb_reload_data_i[9]) begin
              tlb_reload_huge   <= 1'b1;
              tlb_reload_req_o  <= 1'b0;
              tlb_reload_state  <= TLB_GET_PTE;
            end
            else begin
              tlb_reload_addr_o <= {tlb_reload_data_i[31:13], virt_addr_cmd_i[23:13], 2'b00};
              tlb_reload_state  <= TLB_GET_PTE;
            end
          end
        end

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
              dtlb_trans_reload_din[31:13] <= tlb_reload_data_i[31:13];
              // SWE = W
              dtlb_trans_reload_din[9] <= tlb_reload_data_i[7];
              // SRE = 1
              dtlb_trans_reload_din[8] <= 1'b1;
              // UWE = W & U
              dtlb_trans_reload_din[7] <= tlb_reload_data_i[7] & tlb_reload_data_i[6];
              // URE = U
              dtlb_trans_reload_din[6] <= tlb_reload_data_i[6];
              // Dirty, Accessed, Weakly-Ordered-Memory, Writeback cache,
              // Cache inhibit, Cache coherent
              dtlb_trans_reload_din[5:0] <= tlb_reload_data_i[5:0];
              dtlb_trans_reload_we <= 1'b1;
              // Match register generation.
              // VPN
              dtlb_match_reload_din[31:13] <= virt_addr_cmd_i[31:13];
              // Valid
              dtlb_match_reload_din[0]  <= 1'b1;
              dtlb_match_reload_we      <= 1'b1;
              // ---
              tlb_reload_state <= TLB_READ;
            end
          end
        end

        // Let the just written values propagate out on the read ports
        TLB_READ: begin
          tlb_reload_state <= TLB_IDLE;
        end

        default:
          tlb_reload_state <= TLB_IDLE;
      endcase

      // Abort if enable deasserts in the middle of a reload
      if (~enable_r | (dmmucr[31:10] == 0))
        tlb_reload_state <= TLB_IDLE;
    end
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
      dtlb_trans_reload_we  <= 1'b0;
      dtlb_trans_reload_din <= {OPTION_OPERAND_WIDTH{1'b0}};
      dtlb_match_reload_we  <= 1'b0;
      dtlb_match_reload_din <= {OPTION_OPERAND_WIDTH{1'b0}};
    end
  end // HW/SW reload
  endgenerate


  generate
  for (i = 0; i < OPTION_DMMU_WAYS; i=i+1) begin : dtlb
     // DTLB match registers
    mor1kx_dpram_en_w1st_sclk
    #(
      .ADDR_WIDTH     (OPTION_DMMU_SET_WIDTH),
      .DATA_WIDTH     (OPTION_OPERAND_WIDTH),
      .CLEAR_ON_INIT  (OPTION_DMMU_CLEAR_ON_INIT)
    )
    dtlb_match_regs
    (
      // common clock
      .clk    (clk),
      // port "a": 8KB pages
      .en_a   (ram_re | dtlb_match_we[i]),
      .we_a   (dtlb_match_we[i]),
      .addr_a (dtlb_match_addr),
      .din_a  (dtlb_match_din),
      .dout_a (dtlb_match_dout[i]),
      // port "b": Huge pages
      .en_b   (ram_re | dtlb_match_huge_we),
      .we_b   (dtlb_match_huge_we),
      .addr_b (dtlb_match_huge_addr),
      .din_b  (dtlb_match_reload_din),
      .dout_b (dtlb_match_huge_dout[i])
    );

    mor1kx_dpram_en_w1st_sclk
    #(
      .ADDR_WIDTH     (OPTION_DMMU_SET_WIDTH),
      .DATA_WIDTH     (OPTION_OPERAND_WIDTH),
      .CLEAR_ON_INIT  (OPTION_DMMU_CLEAR_ON_INIT)
    )
    dtlb_trans_regs
    (
      // common clock
      .clk    (clk),
      // port "a": 8KB pages
      .en_a   (ram_re | dtlb_trans_we[i]),
      .we_a   (dtlb_trans_we[i]),
      .addr_a (dtlb_trans_addr),
      .din_a  (dtlb_trans_din),
      .dout_a (dtlb_trans_dout[i]),
      // port "b": Huge pages
      .en_b   (ram_re | dtlb_trans_huge_we),
      .we_b   (dtlb_trans_huge_we),
      .addr_b (dtlb_trans_huge_addr),
      .din_b  (dtlb_trans_reload_din),
      .dout_b (dtlb_trans_huge_dout[i])
     );
  end
  endgenerate

endmodule // mor1kx_dmmu_marocchino
