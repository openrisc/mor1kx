/////////////////////////////////////////////////////////////////////
//                                                                 //
//  mor1kx_ocb_marocchino                                          //
//  Order Control Buffer for MAROCCHINO pipeline                   //
//                                                                 //
//  Author: Andrey Bacherov                                        //
//          avbacherov@opencores.org                               //
//                                                                 //
//  TODO: OCB length is fixed by 8 taps. Parametrization?          //
//                                                                 //
/////////////////////////////////////////////////////////////////////
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


//-------------------------------//
// A Tap of Order Control Buffer //
//-------------------------------//

module ocb_tap
#(
  parameter DATA_SIZE = 2
)
(
  // clocks, resets and other controls
  input                      clk,
  input                      rst,
  input                      flush_i,  // flush pipe
  input                      push_i,
  // value at reset/flush
  input      [DATA_SIZE-1:0] default_value_i,
  // data inputs
  input      [DATA_SIZE-1:0] prev_tap_out_i,
  input      [DATA_SIZE-1:0] forwarded_value_i,
  input                      use_forwarded_value_i,
  // data ouputs
  output reg [DATA_SIZE-1:0] out_o
);

  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      out_o <= default_value_i;
    else if(flush_i)
      out_o <= default_value_i;
    else if(push_i)
      out_o <= use_forwarded_value_i ? forwarded_value_i :
                                       prev_tap_out_i;
  end // @clock

endmodule // ocb_tap



//---------------------------------------------------------------//
// Order Control Buffer                                          //
//   all outputs could be analized simultaneously for example to //
//   detect data dependancy                                      //
//---------------------------------------------------------------//

module mor1kx_ocb_marocchino
#(
  parameter NUM_TAPS    = 7, // 8-th is in Write-Back stage
  parameter NUM_OUTS    = 7, // must be at least 1
  parameter DATA_SIZE   = 2
)
(
  // clocks, resets and other input controls
  input                  clk,
  input                  rst,
  input                  pipeline_flush_i, // flush pipe
  input                  padv_decode_i,    // write: advance DECODE
  input                  padv_wb_i,        // read:  advance WB
  // value at reset/flush
  input  [DATA_SIZE-1:0] default_value_i,
  // data input
  input  [DATA_SIZE-1:0] ocbi_i,
  // "OCB is empty" flag
  output                 empty_o,
  // "OCB is full" flag
  //   (a) external control logic must stop the "writing without reading"
  //       operation if OCB is full
  //   (b) however, the "writing + reading" is possible
  //       because it just pushes OCB and keeps it full
  output                 full_o,
  // ouput layout
  // { out[n-1], out[n-2], ... out[0] } : DECODE (entrance) -> EXECUTE (exit)
  output [DATA_SIZE*NUM_OUTS-1:0] ocbo_o
);

  genvar k, m;

  // "pointers"
  reg   [NUM_TAPS:0] ptr_curr; // on current active tap
  reg [NUM_TAPS-1:0] ptr_prev; // on previous active tap

  // pointers are zero: tap #0 (output) is active
  wire ptr_curr_0 = ptr_curr[0];
  wire ptr_prev_0 = ptr_prev[0];

  // "OCB is empty" flag
  assign empty_o = ptr_curr_0 & ptr_prev_0;

  // "OCB is full" flag
  //  # no more availaible taps, pointer is out of range
  assign full_o = ptr_curr[NUM_TAPS];

  // control to increment/decrement pointers
  wire rd_only = ~padv_decode_i &  padv_wb_i;
  wire wr_only =  padv_decode_i & ~padv_wb_i;
  wire wr_rd   =  padv_decode_i &  padv_wb_i;


  // operation algorithm:
  //-----------------------------------------------------------------------------
  // read only    | push: tap[k-1] <= tap[k], tap[num_taps-1] <= reset_value;
  //              | update pointers: if(~ptr_prev_0) ptr_prev <= (ptr_prev >> 1);
  //              |                  if(~ptr_curr_0) ptr_curr <= (ptr_curr >> 1);
  //-----------------------------------------------------------------------------
  // write only   | tap[ptr_curr] <= ocbi_i
  //              | ptr_prev <= ptr_curr;
  //              | ptr_curr <= (ptr_curr << 1);
  //-----------------------------------------------------------------------------
  // read & write | push: tap[k-1] <= tap[k]
  //              |       tap[ptr_prev] <= ocbi_i;
  //-----------------------------------------------------------------------------


  wire ptr_curr_inc = wr_only; // increment pointer on current tap
  wire ptr_curr_dec = rd_only & ~ptr_curr_0; // decrement ...
  wire ptr_prev_dec = rd_only & ~ptr_prev_0; // decrement ... previous ...

  // update pointer on current tap
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      ptr_curr <= {{NUM_TAPS{1'b0}},1'b1};
    else if(pipeline_flush_i)
      ptr_curr <= {{NUM_TAPS{1'b0}},1'b1};
    else if(ptr_curr_inc)
      ptr_curr <= (ptr_curr << 1);
    else if(ptr_curr_dec)
      ptr_curr <= (ptr_curr >> 1);
  end // @clock

  // update pointer on previous tap
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      ptr_prev <= {{(NUM_TAPS-1){1'b0}},1'b1};
    else if(pipeline_flush_i)
      ptr_prev <= {{(NUM_TAPS-1){1'b0}},1'b1};
    else if(ptr_curr_inc)
      ptr_prev <= ptr_curr[NUM_TAPS-1:0];
    else if(ptr_prev_dec)
      ptr_prev <= (ptr_prev >> 1);
  end // @clock


  // enable signals for taps
  wire [NUM_TAPS-1:0] en_curr_tap = {NUM_TAPS{wr_only}} & ptr_curr[NUM_TAPS-1:0];
  wire [NUM_TAPS-1:0] push_taps =
    en_curr_tap |           // tap[ptr_curr] <= ocbi_i (note: by wr_only)
    {NUM_TAPS{padv_wb_i}};  // tap[k-1] <= tap[k]

  // control for forwarding multiplexors
  wire [NUM_TAPS-1:0] use_forwarded_value =
    en_curr_tap |                   // tap[ptr_curr] <= ocbi_i (note: by wr_only)
    ({NUM_TAPS{wr_rd}} & ptr_prev); // tap[ptr_prev] <= ocbi_i;


  // declare interconnection (one extra than taps number for input)
  wire [DATA_SIZE-1:0] ocb_bus[0:NUM_TAPS];

  // taps placement
  generate
  for (k = 0; k < NUM_TAPS; k = k + 1) begin : tap_k
    ocb_tap
    #(
      .DATA_SIZE              (DATA_SIZE)
    )
    u_tap_k
    (
      .clk                    (clk),
      .rst                    (rst),
      .flush_i                (pipeline_flush_i),
      .push_i                 (push_taps[k]),
      .default_value_i        (default_value_i),
      .prev_tap_out_i         (ocb_bus[k+1]),
      .forwarded_value_i      (ocbi_i),
      .use_forwarded_value_i  (use_forwarded_value[k]),
      .out_o                  (ocb_bus[k])
    );
  end
  endgenerate

  // outputs assignement
  generate
  for (m = 0; m < NUM_OUTS; m = m + 1) begin : out_m
    assign ocbo_o [(DATA_SIZE*(m+1)-1):(DATA_SIZE*m)] = ocb_bus[m];
  end
  endgenerate

  // and assign input of all queue:
  assign ocb_bus[NUM_TAPS] = default_value_i;

endmodule // mor1kx_ocb_marocchino



//---------------------------------//
// Reservation Station with 2 taps //
//---------------------------------//

module mor1kx_rsrvs_marocchino
#(
  parameter OPTION_OPERAND_WIDTH = 32,
  parameter OPC_WIDTH            =  1, // width of additional attributes
  parameter DEST_EXT_ADDR_WIDTH  =  3, // log2(Re-Ordering buffer width)
  // Reservation station is used at input of modules:
  //  1CLK: only parameter RSRVS-1CLK must be set to "1"
  //  MCLK: only parameter RSRVS-MCLK must be set to "1"
  //  LSU : RSRVS-1CLK and RSRVS-MCLK parameters must be set to "0"
  parameter RSRVS_1CLK           = 0,
  parameter RSRVS_MCLK           = 0,
  // Packed operands for various reservation stations:
  //  # LSU : {   x,    x, rfb1, rfa1}
  //  # 1CLK: {   x,    x, rfb1, rfa1}
  //  # MCLK: {rfb2, rfa2, rfb1, rfa1}
  parameter DCOD_RFXX_WIDTH      = 64, // (2 * OPTION_OPERAND_WIDTH) for LSU; etc...
  // OMAN-to-DECODE hazards layout for various reservation stations:
  //  # LSU : {   x,    x,    x,    x, d2b1, d2a1, d1b1, d1a1 }
  //  # 1CLK: {   x,    x,    x,    x, d2b1, d2a1, d1b1, d1a1 }
  //  # MCLK: {d2b2, d2a2, d1b2, d1a2, d2b1, d2a1, d1b1, d1a1 }
  parameter BUSY_HAZARDS_FLAGS_WIDTH =  4, //: for LSU and 1CLK;  8: for MCLK
  parameter BUSY_HAZARDS_ADDRS_WIDTH = 12, // (4 * DEST_EXT_ADDR_WIDTH) for LSU; etc...
  // BUSY-to-EXECUTE pass hazards data layout for various reservation stations:
  // (it is also layout for WB-resolving hazards)
  //  # LSU : { d2_wr, d1_wr, ext_bits }
  //  # 1CLK: { d2_wr, d1_wr, ext_bits }
  //  # MCLK: { d2_wr, d1_wr, ext_bits }
  parameter BUSY2EXEC_PASS_DATA_WIDTH = 5,
  // EXEC-to-DECODE hazards layout for various reservation stations:
  //  # LSU : {   x,    x,    x,    x, d2b1, d2a1, d1b1, d1a1 }
  //  # 1CLK: {   x,    x,    x,    x, d2b1, d2a1, d1b1, d1a1 }
  //  # MCLK: {d2b2, d2a2, d1b2, d1a2, d2b1, d2a1, d1b1, d1a1 }
  parameter EXE2DEC_HAZARDS_FLAGS_WIDTH = 4 //: for LSU;  4: for 1CLK;  8: for MCLK
)
(
  // clocks and resets
  input                                     clk,
  input                                     rst,

  // pipeline control signals
  input                                     pipeline_flush_i,
  input                                     padv_decode_i,
  input                                     taking_op_i,      // a unit is taking input for execution

  // input data from DECODE
  input             [(DCOD_RFXX_WIDTH-1):0] dcod_rfxx_i,

  // OMAN-to-DECODE hazards
  //  # combined flag
  input                                     omn2dec_a_hazard_i,
  //  # hazards flags
  input    [(BUSY_HAZARDS_FLAGS_WIDTH-1):0] busy_hazards_flags_i,
  //  # hasards addresses
  input    [(BUSY_HAZARDS_ADDRS_WIDTH-1):0] busy_hazards_addrs_i,

  // EXEC-to-DECODE hazards
  //  # combined flag
  input                                     exe2dec_a_hazard_i,
  //  # hazards flags
  input [(EXE2DEC_HAZARDS_FLAGS_WIDTH-1):0] exe2dec_hazards_flags_i,

  // Hazard could be passed from DECODE to EXECUTE
  //  ## packed input
  input   [(BUSY2EXEC_PASS_DATA_WIDTH-1):0] busy2exec_pass_data_i,
  //  ## passing only with writting back
  input                                     padv_wb_i,

  // Hazard could be resolving
  //  ## packed input
  input   [(BUSY2EXEC_PASS_DATA_WIDTH-1):0] wb2exe_hazards_data_i,
  //  ## forwarding results
  input        [(OPTION_OPERAND_WIDTH-1):0] wb_result1_i,
  input        [(OPTION_OPERAND_WIDTH-1):0] wb_result2_i,


  // Processing of LSU's WB-miss
  input                                     wb_rfd1_wb_lsu_miss_i,

  // command and its additional attributes
  input                                     dcod_op_i,    // request the unit command
  input                   [(OPC_WIDTH-1):0] dcod_opc_i,   // additional attributes for command

  // outputs
  //   command attributes from busy stage
  output                  [(OPC_WIDTH-1):0] busy_opc_o,
  //   combined D1XX hazards
  output                                    exec_wb2exe_hazard_d1xx_o,
  //   command and its additional attributes
  output                                    exec_op_o,    // request the unit command
  output                  [(OPC_WIDTH-1):0] exec_opc_o,   // additional attributes for command
  //   operands
  output       [(OPTION_OPERAND_WIDTH-1):0] exec_rfa1_o,
  output       [(OPTION_OPERAND_WIDTH-1):0] exec_rfb1_o,
  //  ## for MCLK
  output       [(OPTION_OPERAND_WIDTH-1):0] exec_rfa2_o,
  output       [(OPTION_OPERAND_WIDTH-1):0] exec_rfb2_o,
  //   unit-is-busy flag
  output                                    unit_busy_o
);

  /**** parameters for fields extruction ****/

  //  # operands layouts for various reservation stations:
  //  # LSU : {   x,    x, rfb1, rfa1}
  //  # 1CLK: {   x,    x, rfb1, rfa1}
  //  # MCLK: {rfb2, rfa2, rfb1, rfa1}
  //    A1
  localparam  RFA1_LSB = 0;
  localparam  RFA1_MSB = OPTION_OPERAND_WIDTH - 1;
  //    B1
  localparam  RFB1_LSB = OPTION_OPERAND_WIDTH;
  localparam  RFB1_MSB = 2 * OPTION_OPERAND_WIDTH - 1;
  //    A2
  localparam  RFA2_LSB = 2 * OPTION_OPERAND_WIDTH;
  localparam  RFA2_MSB = 3 * OPTION_OPERAND_WIDTH - 1;
  //    B2
  localparam  RFB2_LSB = 3 * OPTION_OPERAND_WIDTH;
  localparam  RFB2_MSB = 4 * OPTION_OPERAND_WIDTH - 1;

  //  # hazards layouts for various reservation stations:
  //  # LSU : {   x,    x,    x,    x, d2b1, d2a1, d1b1, d1a1 }
  //  # 1CLK: {   x,    x,    x,    x, d2b1, d2a1, d1b1, d1a1 }
  //  # MCLK: {d2b2, d2a2, d1b2, d1a2, d2b1, d2a1, d1b1, d1a1 }

  // d1a1 related
  localparam  HAZARD_D1A1_FLG_POS = 0;
  localparam  HAZARD_D1A1_ADR_LSB = 0;
  localparam  HAZARD_D1A1_ADR_MSB = DEST_EXT_ADDR_WIDTH - 1;
  // d1b1 related
  localparam  HAZARD_D1B1_FLG_POS = 1;
  localparam  HAZARD_D1B1_ADR_LSB = DEST_EXT_ADDR_WIDTH;
  localparam  HAZARD_D1B1_ADR_MSB = 2 * DEST_EXT_ADDR_WIDTH - 1;
  // d2a1 related
  localparam  HAZARD_D2A1_FLG_POS = 2;
  localparam  HAZARD_D2A1_ADR_LSB = 2 * DEST_EXT_ADDR_WIDTH;
  localparam  HAZARD_D2A1_ADR_MSB = 3 * DEST_EXT_ADDR_WIDTH - 1;
  // d2b1 related
  localparam  HAZARD_D2B1_FLG_POS = 3;
  localparam  HAZARD_D2B1_ADR_LSB = 3 * DEST_EXT_ADDR_WIDTH;
  localparam  HAZARD_D2B1_ADR_MSB = 4 * DEST_EXT_ADDR_WIDTH - 1;
  // d1a2 related
  localparam  HAZARD_D1A2_FLG_POS = 4;
  localparam  HAZARD_D1A2_ADR_LSB = 4 * DEST_EXT_ADDR_WIDTH;
  localparam  HAZARD_D1A2_ADR_MSB = 5 * DEST_EXT_ADDR_WIDTH - 1;
  // d1b2 related
  localparam  HAZARD_D1B2_FLG_POS = 5;
  localparam  HAZARD_D1B2_ADR_LSB = 5 * DEST_EXT_ADDR_WIDTH;
  localparam  HAZARD_D1B2_ADR_MSB = 6 * DEST_EXT_ADDR_WIDTH - 1;
  // d2a2 related
  localparam  HAZARD_D2A2_FLG_POS = 6;
  localparam  HAZARD_D2A2_ADR_LSB = 6 * DEST_EXT_ADDR_WIDTH;
  localparam  HAZARD_D2A2_ADR_MSB = 7 * DEST_EXT_ADDR_WIDTH - 1;
  // d2b2 related
  localparam  HAZARD_D2B2_FLG_POS = 7;
  localparam  HAZARD_D2B2_ADR_LSB = 7 * DEST_EXT_ADDR_WIDTH;
  localparam  HAZARD_D2B2_ADR_MSB = 8 * DEST_EXT_ADDR_WIDTH - 1;


  // BUSY-to-EXECUTE pass hazards data layout for various reservation stations:
  //  # LSU : { d2_wr, d1_wr, ext_bits }
  //  # 1CLK: { d2_wr, d1_wr, ext_bits }
  //  # MCLK: { d2_wr, d1_wr, ext_bits }
  //    ## extention bits
  localparam  BUSY2EXEC_PASS_EXT_LSB      = 0;
  localparam  BUSY2EXEC_PASS_EXT_MSB      = DEST_EXT_ADDR_WIDTH - 1;
  //    ## write to D1 request
  localparam  BUSY2EXEC_PASS_RFD1_WB_POS  = BUSY2EXEC_PASS_EXT_MSB     + 1;
  //    ## write to D2 request
  localparam  BUSY2EXEC_PASS_RFD2_WB_POS  = BUSY2EXEC_PASS_RFD1_WB_POS + 1;


  // unpack data common for all resevation stations
  wire [(DEST_EXT_ADDR_WIDTH-1):0] exec_ext_adr;
  assign exec_ext_adr = busy2exec_pass_data_i[BUSY2EXEC_PASS_EXT_MSB:BUSY2EXEC_PASS_EXT_LSB];
  wire   exec_rfd1_wb = busy2exec_pass_data_i[BUSY2EXEC_PASS_RFD1_WB_POS];
  wire   exec_rfd2_wb = busy2exec_pass_data_i[BUSY2EXEC_PASS_RFD2_WB_POS];
  // ---
  wire [(DEST_EXT_ADDR_WIDTH-1):0] wb_ext_adr;
  assign wb_ext_adr = wb2exe_hazards_data_i[BUSY2EXEC_PASS_EXT_MSB:BUSY2EXEC_PASS_EXT_LSB];
  wire   wb_rfd1_wb = wb2exe_hazards_data_i[BUSY2EXEC_PASS_RFD1_WB_POS];
  wire   wb_rfd2_wb = wb2exe_hazards_data_i[BUSY2EXEC_PASS_RFD2_WB_POS];


  // execute: command and attributes latches
  reg                 exec_op_r;
  reg [OPC_WIDTH-1:0] exec_opc_r;


  /**** BUSY stage ****/


  // DECODE->BUSY transfer
  wire dcod_pushing_busy = padv_decode_i & dcod_op_i &            // DECODE pushing BUSY: Latch DECODE output ...
                           ((exec_op_r & (~taking_op_i)) |        // DECODE pushing BUSY: ... if EXECUTE is busy or ...
                            omn2dec_a_hazard_i           |        // DECODE pushing BUSY: ... if an OMAN-to-DECODE hazard or ...
                            (exe2dec_a_hazard_i & (~padv_wb_i))); // DECODE pushing BUSY: ... if an EXECUTE-to-DECODE couldn't be passed.

  // busy pushing execute
  wire busy_pushing_exec;

  // busy: command and additional attributes
  reg                 busy_op_r;
  reg [OPC_WIDTH-1:0] busy_opc_r;

  // latch command and its attributes
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      busy_op_r  <= 1'b0;
      busy_opc_r <= {OPC_WIDTH{1'b0}};
    end
    else if (pipeline_flush_i) begin
      busy_op_r  <= 1'b0;
      busy_opc_r <= {OPC_WIDTH{1'b0}};
    end
    else if (dcod_pushing_busy) begin
      busy_op_r  <= dcod_op_i;
      busy_opc_r <= dcod_opc_i;
    end
    else if (busy_pushing_exec) begin
      busy_op_r  <= 1'b0;
      busy_opc_r <= {OPC_WIDTH{1'b0}};
    end
  end // @clock

  // output from busy stage
  //  ## command attributes from busy stage
  assign busy_opc_o  = busy_opc_r;
  //  ## unit-is-busy flag
  assign unit_busy_o = busy_op_r;



  // busy: processing hazards wires (and regs) used across whole module
  // # common for all types of reservation station
  //  ## d1a1 related
  reg                                 busy_hazard_d1a1_r;
  reg       [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d1a1_adr_r;
  wire                                busy_d1a1_pass2exec;
  wire                                busy_d1a1_muxing_wb;
  //  ## d1b1 related
  reg                                 busy_hazard_d1b1_r;
  reg       [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d1b1_adr_r;
  wire                                busy_d1b1_pass2exec;
  wire                                busy_d1b1_muxing_wb;
  //  ## d2a1 related
  reg                                 busy_hazard_d2a1_r;
  reg       [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d2a1_adr_r;
  wire                                busy_d2a1_pass2exec;
  wire                                busy_d2a1_muxing_wb;
  //  ## d2b1 related
  reg                                 busy_hazard_d2b1_r;
  reg       [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d2b1_adr_r;
  wire                                busy_d2b1_pass2exec;
  wire                                busy_d2b1_muxing_wb;
  // # exclusively for MCLK reservation station
  //  ## d1a2 related
  wire                                busy_hazard_d1a2_w;
  wire                                busy_d1a2_pass2exec;
  wire                                busy_d1a2_muxing_wb;
  //  ## d1b2 related
  wire                                busy_hazard_d1b2_w;
  wire                                busy_d1b2_pass2exec;
  wire                                busy_d1b2_muxing_wb;
  //  ## d2a2 related
  wire                                busy_hazard_d2a2_w;
  wire                                busy_d2a2_pass2exec;
  wire                                busy_d2a2_muxing_wb;
  //  ## d2b2 related
  wire                                busy_hazard_d2b2_w;
  wire                                busy_d2b2_pass2exec;
  wire                                busy_d2b2_muxing_wb;

  // busy: operands
  //   ## registers for operands A & B
  reg      [OPTION_OPERAND_WIDTH-1:0] busy_rfa1_r;
  reg      [OPTION_OPERAND_WIDTH-1:0] busy_rfb1_r;
  //   ## multiplexed with forwarded value from WB
  wire     [OPTION_OPERAND_WIDTH-1:0] busy_rfa1;
  wire     [OPTION_OPERAND_WIDTH-1:0] busy_rfb1;
  wire     [OPTION_OPERAND_WIDTH-1:0] busy_rfa2_w; // makes sense in MCLK only
  wire     [OPTION_OPERAND_WIDTH-1:0] busy_rfb2_w; // makes sense in MCLK only

  // latches for common part
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      // d1a1 related
      busy_hazard_d1a1_r     <= 1'b0;
      busy_hazard_d1a1_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
      // d1b1 related
      busy_hazard_d1b1_r     <= 1'b0;
      busy_hazard_d1b1_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
      // d2a1 related
      busy_hazard_d2a1_r     <= 1'b0;
      busy_hazard_d2a1_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
      // d2b1 related
      busy_hazard_d2b1_r     <= 1'b0;
      busy_hazard_d2b1_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
    end
    else if (pipeline_flush_i) begin
      // d1a1 related
      busy_hazard_d1a1_r     <= 1'b0;
      busy_hazard_d1a1_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
      // d1b1 related
      busy_hazard_d1b1_r     <= 1'b0;
      busy_hazard_d1b1_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
      // d2a1 related
      busy_hazard_d2a1_r     <= 1'b0;
      busy_hazard_d2a1_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
      // d2b1 related
      busy_hazard_d2b1_r     <= 1'b0;
      busy_hazard_d2b1_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
    end
    else if (dcod_pushing_busy) begin
      // d1a1 related
      busy_hazard_d1a1_r     <= busy_hazards_flags_i[HAZARD_D1A1_FLG_POS];
      busy_hazard_d1a1_adr_r <= busy_hazards_addrs_i[HAZARD_D1A1_ADR_MSB:HAZARD_D1A1_ADR_LSB];
      // d1b1 related
      busy_hazard_d1b1_r     <= busy_hazards_flags_i[HAZARD_D1B1_FLG_POS];
      busy_hazard_d1b1_adr_r <= busy_hazards_addrs_i[HAZARD_D1B1_ADR_MSB:HAZARD_D1B1_ADR_LSB];
      // d2a1 related
      busy_hazard_d2a1_r     <= busy_hazards_flags_i[HAZARD_D2A1_FLG_POS];
      busy_hazard_d2a1_adr_r <= busy_hazards_addrs_i[HAZARD_D2A1_ADR_MSB:HAZARD_D2A1_ADR_LSB];
      // d2b1 related
      busy_hazard_d2b1_r     <= busy_hazards_flags_i[HAZARD_D2B1_FLG_POS];
      busy_hazard_d2b1_adr_r <= busy_hazards_addrs_i[HAZARD_D2B1_ADR_MSB:HAZARD_D2B1_ADR_LSB];
    end
    else begin
      // d1a1 related
      if (busy_d1a1_muxing_wb | busy_pushing_exec) begin
        busy_hazard_d1a1_r     <= 1'b0;
        busy_hazard_d1a1_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
      end
      // d1b1 related
      if (busy_d1b1_muxing_wb | busy_pushing_exec) begin
        busy_hazard_d1b1_r     <= 1'b0;
        busy_hazard_d1b1_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
      end
      // d2a1 related
      if (busy_d2a1_muxing_wb | busy_pushing_exec) begin
        busy_hazard_d2a1_r     <= 1'b0;
        busy_hazard_d2a1_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
      end
      // d2b1 related
      if (busy_d2b1_muxing_wb | busy_pushing_exec) begin
        busy_hazard_d2b1_r     <= 1'b0;
        busy_hazard_d2b1_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
      end
    end
  end // @clock

  // d1a1 related
  assign busy_d1a1_pass2exec = busy_hazard_d1a1_r & exec_rfd1_wb & (busy_hazard_d1a1_adr_r == exec_ext_adr) & padv_wb_i;
  assign busy_d1a1_muxing_wb = busy_hazard_d1a1_r & wb_rfd1_wb   & (busy_hazard_d1a1_adr_r == wb_ext_adr);
  // d1b1 related
  assign busy_d1b1_pass2exec = busy_hazard_d1b1_r & exec_rfd1_wb & (busy_hazard_d1b1_adr_r == exec_ext_adr) & padv_wb_i;
  assign busy_d1b1_muxing_wb = busy_hazard_d1b1_r & wb_rfd1_wb   & (busy_hazard_d1b1_adr_r == wb_ext_adr);
  // d2a1 related
  assign busy_d2a1_pass2exec = busy_hazard_d2a1_r & exec_rfd2_wb & (busy_hazard_d2a1_adr_r == exec_ext_adr) & padv_wb_i;
  assign busy_d2a1_muxing_wb = busy_hazard_d2a1_r & wb_rfd2_wb   & (busy_hazard_d2a1_adr_r == wb_ext_adr);
  // d2b1 related
  assign busy_d2b1_pass2exec = busy_hazard_d2b1_r & exec_rfd2_wb & (busy_hazard_d2b1_adr_r == exec_ext_adr) & padv_wb_i;
  assign busy_d2b1_muxing_wb = busy_hazard_d2b1_r & wb_rfd2_wb   & (busy_hazard_d2b1_adr_r == wb_ext_adr);

  // forwarding operands A1 & B1
  always @(posedge clk) begin
    if (dcod_pushing_busy) begin
      busy_rfa1_r <= dcod_rfxx_i[RFA1_MSB:RFA1_LSB];
      busy_rfb1_r <= dcod_rfxx_i[RFB1_MSB:RFB1_LSB];
    end
    else begin
      // complete forwarding for operand A1
      if (busy_d1a1_muxing_wb | busy_d2a1_muxing_wb)
        busy_rfa1_r <= busy_rfa1;
      // complete forwarding for operand B1
      if (busy_d1b1_muxing_wb | busy_d2b1_muxing_wb)
        busy_rfb1_r <= busy_rfb1;
    end
  end // @clock
  //---
  //  operand A1
  assign busy_rfa1 = busy_hazard_d1a1_r ? wb_result1_i :
                     busy_hazard_d2a1_r ? wb_result2_i : busy_rfa1_r;
  //  operand B1
  assign busy_rfb1 = busy_hazard_d1b1_r ? wb_result1_i :
                     busy_hazard_d2b1_r ? wb_result2_i : busy_rfb1_r;


  // exclusive latches for MCLK reservation station
  generate
  /* verilator lint_off WIDTH */
  if (RSRVS_MCLK == 1) begin : busy_mclk_enabled
  /* verilator lint_on WIDTH */
    // d1a2 related
    reg                                 busy_hazard_d1a2_r;
    reg       [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d1a2_adr_r;
    // d1b2 related
    reg                                 busy_hazard_d1b2_r;
    reg       [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d1b2_adr_r;
    // d2a2 related
    reg                                 busy_hazard_d2a2_r;
    reg       [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d2a2_adr_r;
    // d2b2 related
    reg                                 busy_hazard_d2b2_r;
    reg       [DEST_EXT_ADDR_WIDTH-1:0] busy_hazard_d2b2_adr_r;
    // ---
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst) begin
        // d1a2 related
        busy_hazard_d1a2_r     <= 1'b0;
        busy_hazard_d1a2_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
        // d1b2 related
        busy_hazard_d1b2_r     <= 1'b0;
        busy_hazard_d1b2_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
        // d2a2 related
        busy_hazard_d2a2_r     <= 1'b0;
        busy_hazard_d2a2_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
        // d2b2 related
        busy_hazard_d2b2_r     <= 1'b0;
        busy_hazard_d2b2_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
      end
      else if (pipeline_flush_i) begin
        // d1a2 related
        busy_hazard_d1a2_r     <= 1'b0;
        busy_hazard_d1a2_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
        // d1b2 related
        busy_hazard_d1b2_r     <= 1'b0;
        busy_hazard_d1b2_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
        // d2a2 related
        busy_hazard_d2a2_r     <= 1'b0;
        busy_hazard_d2a2_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
        // d2b2 related
        busy_hazard_d2b2_r     <= 1'b0;
        busy_hazard_d2b2_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
      end
      else if (dcod_pushing_busy) begin
        // d1a2 related
        busy_hazard_d1a2_r     <= busy_hazards_flags_i[HAZARD_D1A2_FLG_POS];
        busy_hazard_d1a2_adr_r <= busy_hazards_addrs_i[HAZARD_D1A2_ADR_MSB:HAZARD_D1A2_ADR_LSB];
        // d1b2 related
        busy_hazard_d1b2_r     <= busy_hazards_flags_i[HAZARD_D1B2_FLG_POS];
        busy_hazard_d1b2_adr_r <= busy_hazards_addrs_i[HAZARD_D1B2_ADR_MSB:HAZARD_D1B2_ADR_LSB];
        // d2a2 related
        busy_hazard_d2a2_r     <= busy_hazards_flags_i[HAZARD_D2A2_FLG_POS];
        busy_hazard_d2a2_adr_r <= busy_hazards_addrs_i[HAZARD_D2A2_ADR_MSB:HAZARD_D2A2_ADR_LSB];
        // d2b2 related
        busy_hazard_d2b2_r     <= busy_hazards_flags_i[HAZARD_D2B2_FLG_POS];
        busy_hazard_d2b2_adr_r <= busy_hazards_addrs_i[HAZARD_D2B2_ADR_MSB:HAZARD_D2B2_ADR_LSB];
      end
      else begin
        // d1a2 related
        if (busy_d1a2_muxing_wb | busy_pushing_exec) begin
          busy_hazard_d1a2_r     <= 1'b0;
          busy_hazard_d1a2_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
        end
        // d1b2 related
        if (busy_d1b2_muxing_wb | busy_pushing_exec) begin
          busy_hazard_d1b2_r     <= 1'b0;
          busy_hazard_d1b2_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
        end
        // d2a2 related
        if (busy_d2a2_muxing_wb | busy_pushing_exec) begin
          busy_hazard_d2a2_r     <= 1'b0;
          busy_hazard_d2a2_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
        end
        // d2b2 related
        if (busy_d2b2_muxing_wb | busy_pushing_exec) begin
          busy_hazard_d2b2_r     <= 1'b0;
          busy_hazard_d2b2_adr_r <= {DEST_EXT_ADDR_WIDTH{1'b0}};
        end
      end
    end // @clock
    // ---
    // d1a2 related
    assign busy_hazard_d1a2_w  = busy_hazard_d1a2_r; // MCLK
    assign busy_d1a2_pass2exec = busy_hazard_d1a2_r & exec_rfd1_wb & (busy_hazard_d1a2_adr_r == exec_ext_adr) & padv_wb_i;
    assign busy_d1a2_muxing_wb = busy_hazard_d1a2_r & wb_rfd1_wb   & (busy_hazard_d1a2_adr_r == wb_ext_adr);
    // d1b2 related
    assign busy_hazard_d1b2_w  = busy_hazard_d1b2_r; // MCLK
    assign busy_d1b2_pass2exec = busy_hazard_d1b2_r & exec_rfd1_wb & (busy_hazard_d1b2_adr_r == exec_ext_adr) & padv_wb_i;
    assign busy_d1b2_muxing_wb = busy_hazard_d1b2_r & wb_rfd1_wb   & (busy_hazard_d1b2_adr_r == wb_ext_adr);
    // d2a2 related
    assign busy_hazard_d2a2_w  = busy_hazard_d2a2_r; // MCLK
    assign busy_d2a2_pass2exec = busy_hazard_d2a2_r & exec_rfd2_wb & (busy_hazard_d2a2_adr_r == exec_ext_adr) & padv_wb_i;
    assign busy_d2a2_muxing_wb = busy_hazard_d2a2_r & wb_rfd2_wb   & (busy_hazard_d2a2_adr_r == wb_ext_adr);
    // d2b2 related
    assign busy_hazard_d2b2_w  = busy_hazard_d2b2_r; // MCLK
    assign busy_d2b2_pass2exec = busy_hazard_d2b2_r & exec_rfd2_wb & (busy_hazard_d2b2_adr_r == exec_ext_adr) & padv_wb_i;
    assign busy_d2b2_muxing_wb = busy_hazard_d2b2_r & wb_rfd2_wb   & (busy_hazard_d2b2_adr_r == wb_ext_adr);

    // A2 & B2 operands
    reg [OPTION_OPERAND_WIDTH-1:0] busy_rfa2_r;
    reg [OPTION_OPERAND_WIDTH-1:0] busy_rfb2_r;
    // ---
    always @(posedge clk) begin
      if (dcod_pushing_busy) begin
        busy_rfa2_r <= dcod_rfxx_i[RFA2_MSB:RFA2_LSB];
        busy_rfb2_r <= dcod_rfxx_i[RFB2_MSB:RFB2_LSB];
      end
      else begin
        // complete forwarding for operand A2
        if (busy_d1a2_muxing_wb | busy_d2a2_muxing_wb)
          busy_rfa2_r <= busy_rfa2_w;
        // complete forwarding for operand B2
        if (busy_d1b2_muxing_wb | busy_d2b2_muxing_wb)
          busy_rfb2_r <= busy_rfb2_w;
      end
    end // @clock
    // ---
    //  operand A2
    assign busy_rfa2_w = busy_hazard_d1a2_r ? wb_result1_i :
                         busy_hazard_d2a2_r ? wb_result2_i : busy_rfa2_r;
    //  operand B2
    assign busy_rfb2_w = busy_hazard_d1b2_r ? wb_result1_i :
                         busy_hazard_d2b2_r ? wb_result2_i : busy_rfb2_r;
  end
  else begin : busy_mclk_disabled
    // d1a2 related
    assign busy_hazard_d1a2_w  = 1'b0; // not MCLK
    assign busy_d1a2_pass2exec = 1'b0; // not MCLK
    assign busy_d1a2_muxing_wb = 1'b0; // not MCLK
    // d1b2 related
    assign busy_hazard_d1b2_w  = 1'b0; // not MCLK
    assign busy_d1b2_pass2exec = 1'b0; // not MCLK
    assign busy_d1b2_muxing_wb = 1'b0; // not MCLK
    // d2a2 related
    assign busy_hazard_d2a2_w  = 1'b0; // not MCLK
    assign busy_d2a2_pass2exec = 1'b0; // not MCLK
    assign busy_d2a2_muxing_wb = 1'b0; // not MCLK
    // d2b2 related
    assign busy_hazard_d2b2_w  = 1'b0; // not MCLK
    assign busy_d2b2_pass2exec = 1'b0; // not MCLK
    assign busy_d2b2_muxing_wb = 1'b0; // not MCLK
    // operands
    assign busy_rfa2_w         = {OPTION_OPERAND_WIDTH{1'b0}}; // not MCLK
    assign busy_rfb2_w         = {OPTION_OPERAND_WIDTH{1'b0}}; // not MCLK
  end
  endgenerate // BUSY-MCLK


  // busy pushing execute: no more hazards in BUSY
  wire busy_free_of_hazards = ((~busy_hazard_d1a1_r) | busy_d1a1_muxing_wb | busy_d1a1_pass2exec) &
                              ((~busy_hazard_d1b1_r) | busy_d1b1_muxing_wb | busy_d1b1_pass2exec) &
                              ((~busy_hazard_d2a1_r) | busy_d2a1_muxing_wb | busy_d2a1_pass2exec) &
                              ((~busy_hazard_d2b1_r) | busy_d2b1_muxing_wb | busy_d2b1_pass2exec) &
                              ((~busy_hazard_d1a2_w) | busy_d1a2_muxing_wb | busy_d1a2_pass2exec) &
                              ((~busy_hazard_d1b2_w) | busy_d1b2_muxing_wb | busy_d1b2_pass2exec) &
                              ((~busy_hazard_d2a2_w) | busy_d2a2_muxing_wb | busy_d2a2_pass2exec) &
                              ((~busy_hazard_d2b2_w) | busy_d2b2_muxing_wb | busy_d2b2_pass2exec);


  /**** EXECUTE stage latches ****/


  // DECODE->EXECUTE transfer
  wire   dcod_pushing_exec = padv_decode_i & dcod_op_i  &       // DECODE pushing EXECUTE: New command ...
                             (~exec_op_r | taking_op_i) &       // DECODE pushing EXECUTE: ... and unit is free ...
                             (~omn2dec_a_hazard_i)      &       // DECODE pushing EXECUTE: ... and no waiting for resolving hazards ...
                             (~exe2dec_a_hazard_i | padv_wb_i); // DECODE pushing EXECUTE: ... forwarding from WB if required.

  // BUSY->EXECUTE transfer
  assign busy_pushing_exec = unit_busy_o          &       // BUSY pushing EXECUTE: There is pending instruction ...
                             busy_free_of_hazards &       // BUSY pushing EXECUTE: ... and hazards are resolved or could be passed ...
                             (~exec_op_r | taking_op_i);  // BUSY pushing EXECUTE: ... and EXECUTE is free.


  // --- execute: command and attributes latches ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      exec_op_r  <= 1'b0;
      exec_opc_r <= {OPC_WIDTH{1'b0}};
    end
    else if (pipeline_flush_i) begin
      exec_op_r  <= 1'b0;
      exec_opc_r <= {OPC_WIDTH{1'b0}};
    end
    else if (dcod_pushing_exec) begin
      exec_op_r  <= dcod_op_i;
      exec_opc_r <= dcod_opc_i;
    end
    else if (busy_pushing_exec) begin
      exec_op_r  <= busy_op_r;
      exec_opc_r <= busy_opc_r;
    end
    else if (taking_op_i) begin
      exec_op_r  <= 1'b0;
      exec_opc_r <= {OPC_WIDTH{1'b0}};
    end
  end // @clock

  // OP/OPC outputs with maskign by D1 related hazards and LSU load miss
  // ---
  wire exe2dec_hazard_d1xx = exe2dec_hazards_flags_i[HAZARD_D1A1_FLG_POS] |
                             exe2dec_hazards_flags_i[HAZARD_D1B1_FLG_POS] |
                             ((RSRVS_MCLK == 1) ? exe2dec_hazards_flags_i[HAZARD_D1A2_FLG_POS] : 1'b0) |
                             ((RSRVS_MCLK == 1) ? exe2dec_hazards_flags_i[HAZARD_D1B2_FLG_POS] : 1'b0);
  // ---
  wire busy_d1xx_pass2exec = busy_d1a1_pass2exec | busy_d1b1_pass2exec |
                             busy_d1a2_pass2exec | busy_d1b2_pass2exec;
  // ---
  reg    exec_hazard_d1xx_r;
  assign exec_wb2exe_hazard_d1xx_o = exec_hazard_d1xx_r;
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      exec_hazard_d1xx_r <= 1'b0;
    else if (pipeline_flush_i)
      exec_hazard_d1xx_r <= 1'b0;
    else if (dcod_pushing_exec)
      exec_hazard_d1xx_r <= exe2dec_hazard_d1xx;
    else if (busy_pushing_exec)
      exec_hazard_d1xx_r <= busy_d1xx_pass2exec;
    else if (exec_hazard_d1xx_r & (~wb_rfd1_wb_lsu_miss_i))
      exec_hazard_d1xx_r <= 1'b0;
  end // @clock
  // ---
  //   We don't block OP/OPC for 1-CLOCK reservation station
  // because 1-clock output goes directly to WB
  // and in next turn WB already blocked by wb-lsu-valid-miss.
  //   So, we just minimize logic for 1-CLOCK.
  wire   exec_op_en = ((RSRVS_1CLK == 1) ? 1'b1 : ~(exec_hazard_d1xx_r & wb_rfd1_wb_lsu_miss_i));
  assign exec_op_o  = exec_op_r  & exec_op_en;
  assign exec_opc_o = exec_opc_r & {OPC_WIDTH{exec_op_en}};


  // execute: hazards for all reservation station types
  reg exec_hazard_d1a1_r;
  reg exec_hazard_d1b1_r;
  reg exec_hazard_d2a1_r;
  reg exec_hazard_d2b1_r;
  // take into accaunt speculative WB for LSU
  // it makes sense for D1-related hazards only
  wire exec_hazard_d1a1 = exec_hazard_d1a1_r & (~wb_rfd1_wb_lsu_miss_i);
  wire exec_hazard_d1b1 = exec_hazard_d1b1_r & (~wb_rfd1_wb_lsu_miss_i);

  // execute: operands
  //   ## registers
  reg  [OPTION_OPERAND_WIDTH-1:0] exec_rfa1_r;
  reg  [OPTION_OPERAND_WIDTH-1:0] exec_rfb1_r;
  //   ## multiplexed with forwarded value from WB
  wire [OPTION_OPERAND_WIDTH-1:0] exec_rfa1;
  wire [OPTION_OPERAND_WIDTH-1:0] exec_rfb1;
  //   ## for MCLK
  wire [OPTION_OPERAND_WIDTH-1:0] exec_rfa2_w;
  wire [OPTION_OPERAND_WIDTH-1:0] exec_rfb2_w;

  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      exec_hazard_d1a1_r <= 1'b0;
      exec_hazard_d1b1_r <= 1'b0;
      exec_hazard_d2a1_r <= 1'b0;
      exec_hazard_d2b1_r <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      exec_hazard_d1a1_r <= 1'b0;
      exec_hazard_d1b1_r <= 1'b0;
      exec_hazard_d2a1_r <= 1'b0;
      exec_hazard_d2b1_r <= 1'b0;
    end
    else if (dcod_pushing_exec) begin
      exec_hazard_d1a1_r <= exe2dec_hazards_flags_i[HAZARD_D1A1_FLG_POS];
      exec_hazard_d1b1_r <= exe2dec_hazards_flags_i[HAZARD_D1B1_FLG_POS];
      exec_hazard_d2a1_r <= exe2dec_hazards_flags_i[HAZARD_D2A1_FLG_POS];
      exec_hazard_d2b1_r <= exe2dec_hazards_flags_i[HAZARD_D2B1_FLG_POS];
    end
    else if (busy_pushing_exec) begin
      exec_hazard_d1a1_r <= busy_d1a1_pass2exec;
      exec_hazard_d1b1_r <= busy_d1b1_pass2exec;
      exec_hazard_d2a1_r <= busy_d2a1_pass2exec;
      exec_hazard_d2b1_r <= busy_d2b1_pass2exec;
    end
    else if (exec_hazard_d1a1 | exec_hazard_d1b1 | exec_hazard_d2a1_r | exec_hazard_d2b1_r) begin
      // at the stage either A1-hazard or B1-hazard takes place,
      // but not both, so we process them at the same time
      exec_hazard_d1a1_r <= 1'b0;
      exec_hazard_d1b1_r <= 1'b0;
      exec_hazard_d2a1_r <= 1'b0;
      exec_hazard_d2b1_r <= 1'b0;
    end
  end // @clock
  // ---
  always @(posedge clk) begin
    if (dcod_pushing_exec) begin
      exec_rfa1_r <= dcod_rfxx_i[RFA1_MSB:RFA1_LSB];
      exec_rfb1_r <= dcod_rfxx_i[RFB1_MSB:RFB1_LSB];
    end
    else if (busy_pushing_exec) begin
      exec_rfa1_r <= busy_rfa1;
      exec_rfb1_r <= busy_rfb1;
    end
    else if (exec_hazard_d1a1 | exec_hazard_d1b1 | exec_hazard_d2a1_r | exec_hazard_d2b1_r) begin
      exec_rfa1_r <= exec_rfa1;
      exec_rfb1_r <= exec_rfb1;
    end
  end // @clock
  // last forward (from WB)
  //  operand A1
  assign exec_rfa1 = exec_hazard_d1a1_r ? wb_result1_i :
                     exec_hazard_d2a1_r ? wb_result2_i : exec_rfa1_r;
  //  operand B1
  assign exec_rfb1 = exec_hazard_d1b1_r ? wb_result1_i :
                     exec_hazard_d2b1_r ? wb_result2_i : exec_rfb1_r;

  //  ## for MCLK
  generate
  /* verilator lint_off WIDTH */
  if (RSRVS_MCLK == 1) begin : exec_mclk_enabled
  /* verilator lint_on WIDTH */
    // hazard flags and destination addresses
    reg exec_hazard_d1a2_r;
    reg exec_hazard_d1b2_r;
    reg exec_hazard_d2a2_r;
    reg exec_hazard_d2b2_r;
    // take into accaunt speculative WB for LSU
    // it makes sense for D!-related hazards only
    wire exec_hazard_d1a2 = exec_hazard_d1a2_r & (~wb_rfd1_wb_lsu_miss_i);
    wire exec_hazard_d1b2 = exec_hazard_d1b2_r & (~wb_rfd1_wb_lsu_miss_i);
    // registers for operands A & B
    reg [OPTION_OPERAND_WIDTH-1:0] exec_rfa2_r;
    reg [OPTION_OPERAND_WIDTH-1:0] exec_rfb2_r;
    // ---
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst) begin
        exec_hazard_d1a2_r <= 1'b0;
        exec_hazard_d1b2_r <= 1'b0;
        exec_hazard_d2a2_r <= 1'b0;
        exec_hazard_d2b2_r <= 1'b0;
      end
      else if (pipeline_flush_i) begin
        exec_hazard_d1a2_r <= 1'b0;
        exec_hazard_d1b2_r <= 1'b0;
        exec_hazard_d2a2_r <= 1'b0;
        exec_hazard_d2b2_r <= 1'b0;
      end
      else if (dcod_pushing_exec) begin
        exec_hazard_d1a2_r <= exe2dec_hazards_flags_i[HAZARD_D1A2_FLG_POS];
        exec_hazard_d1b2_r <= exe2dec_hazards_flags_i[HAZARD_D1B2_FLG_POS];
        exec_hazard_d2a2_r <= exe2dec_hazards_flags_i[HAZARD_D2A2_FLG_POS];
        exec_hazard_d2b2_r <= exe2dec_hazards_flags_i[HAZARD_D2B2_FLG_POS];
      end
      else if (busy_pushing_exec) begin
        exec_hazard_d1a2_r <= busy_d1a2_pass2exec;
        exec_hazard_d1b2_r <= busy_d1b2_pass2exec;
        exec_hazard_d2a2_r <= busy_d2a2_pass2exec;
        exec_hazard_d2b2_r <= busy_d2b2_pass2exec;
      end
      else if (exec_hazard_d1a2 | exec_hazard_d1b2 | exec_hazard_d2a2_r | exec_hazard_d2b2_r) begin
        // at the stage either A2-hazard or B2-hazard takes place,
        // but not both, so we process them at the same time
        exec_hazard_d1a2_r <= 1'b0;
        exec_hazard_d1b2_r <= 1'b0;
        exec_hazard_d2a2_r <= 1'b0;
        exec_hazard_d2b2_r <= 1'b0;
      end
    end // @clock
    // ---
    always @(posedge clk) begin
      if (dcod_pushing_exec) begin
        exec_rfa2_r <= dcod_rfxx_i[RFA2_MSB:RFA2_LSB];
        exec_rfb2_r <= dcod_rfxx_i[RFB2_MSB:RFB2_LSB];
      end
      else if (busy_pushing_exec) begin
        exec_rfa2_r <= busy_rfa2_w;
        exec_rfb2_r <= busy_rfb2_w;
      end
      else if (exec_hazard_d1a2 | exec_hazard_d1b2 | exec_hazard_d2a2_r | exec_hazard_d2b2_r) begin
        exec_rfa2_r <= exec_rfa2_w;
        exec_rfb2_r <= exec_rfb2_w;
      end
    end // @clock
    // last forward (from WB)
    //  operand A2
    assign exec_rfa2_w = exec_hazard_d1a2_r ? wb_result1_i :
                         exec_hazard_d2a2_r ? wb_result2_i : exec_rfa2_r;
    //  operand B2
    assign exec_rfb2_w = exec_hazard_d1b2_r ? wb_result1_i :
                         exec_hazard_d2b2_r ? wb_result2_i : exec_rfb2_r;
  end
  else begin : exec_mclk_disabled
    assign exec_rfa2_w  = {OPTION_OPERAND_WIDTH{1'b0}}; // not MCLK
    assign exec_rfb2_w  = {OPTION_OPERAND_WIDTH{1'b0}}; // not MCLK
  end
  endgenerate // EXEC-MCLK

  // outputs
  //   operands
  assign exec_rfa1_o = exec_rfa1;
  assign exec_rfb1_o = exec_rfb1;
  //   for MCLK
  assign exec_rfa2_o = exec_rfa2_w;
  assign exec_rfb2_o = exec_rfb2_w;

endmodule // mor1kx_rsrvs_marocchino
