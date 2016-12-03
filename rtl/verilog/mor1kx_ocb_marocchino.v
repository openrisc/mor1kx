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
  parameter DATA_SIZE   = 2,
  parameter RESET_VALUE = {DATA_SIZE{1'b0}}
)
(
  // clocks, resets and other controls
  input                      clk,
  input                      rst,
  input                      flush_i,  // flush pipe
  input                      push_i,
  // data inputs
  input      [DATA_SIZE-1:0] prev_tap_out_i,
  input      [DATA_SIZE-1:0] forwarded_value_i,
  input                      use_forwarded_value_i,
  // data ouputs
  output reg [DATA_SIZE-1:0] out_o
);

  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      out_o <= RESET_VALUE;
    else if(flush_i)
      out_o <= RESET_VALUE;
    else if(push_i)
      out_o <= use_forwarded_value_i ? forwarded_value_i :
                                       prev_tap_out_i;
  end // posedge clock

endmodule // ocb_tap



//---------------------------------------------------------------//
// Order Control Buffer                                          //
//   all outputs could be analized simultaneously for example to //
//   detect data dependancy                                      //
//---------------------------------------------------------------//

module mor1kx_ocb_marocchino
#(
  parameter DATA_SIZE   = 2,
  parameter RESET_VALUE = {DATA_SIZE{1'b0}}
)
(
  // clocks, resets and other input controls
  input                  clk,
  input                  rst,
  input                  pipeline_flush_i, // flush pipe
  input                  padv_decode_i,    // write: advance DECODE
  input                  padv_wb_i,        // read:  advance WB
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
  // data ouputs
  output [DATA_SIZE-1:0] ocbo00_o, // OCB output
  output [DATA_SIZE-1:0] ocbo01_o, // ...
  output [DATA_SIZE-1:0] ocbo02_o, // ...
  output [DATA_SIZE-1:0] ocbo03_o, // ...
  output [DATA_SIZE-1:0] ocbo04_o, // ...
  output [DATA_SIZE-1:0] ocbo05_o, // ...
  output [DATA_SIZE-1:0] ocbo06_o, // ...
  output [DATA_SIZE-1:0] ocbo07_o  // OCB entrance
);

  localparam NUM_TAPS = 8;

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
  end // posedge clock

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
  end // posedge clock


  // enable signals for taps
  wire [NUM_TAPS-1:0] en_curr_tap = {NUM_TAPS{wr_only}} & ptr_curr[NUM_TAPS-1:0];
  wire [NUM_TAPS-1:0] push_taps =
    en_curr_tap |           // tap[ptr_curr] <= ocbi_i (note: by wr_only)
    {NUM_TAPS{padv_wb_i}};  // tap[k-1] <= tap[k]

  // control for forwarding multiplexors
  wire [NUM_TAPS-1:0] use_forwarded_value =
    en_curr_tap |                   // tap[ptr_curr] <= ocbi_i (note: by wr_only)
    ({NUM_TAPS{wr_rd}} & ptr_prev); // tap[ptr_prev] <= ocbi_i;


  // taps
  //   tap #00
  ocb_tap
  #(
    .DATA_SIZE    (DATA_SIZE),
    .RESET_VALUE  (RESET_VALUE)
  )
  u_tap_00
  (
    .clk                    (clk),
    .rst                    (rst),
    .flush_i                (pipeline_flush_i),
    .push_i                 (push_taps[0]),
    .prev_tap_out_i         (ocbo01_o),
    .forwarded_value_i      (ocbi_i),
    .use_forwarded_value_i  (use_forwarded_value[0]),
    .out_o                  (ocbo00_o)
  );

  //   tap #01
  ocb_tap
  #(
    .DATA_SIZE    (DATA_SIZE),
    .RESET_VALUE  (RESET_VALUE)
  )
  u_tap_01
  (
    .clk                    (clk),
    .rst                    (rst),
    .flush_i                (pipeline_flush_i),
    .push_i                 (push_taps[1]),
    .prev_tap_out_i         (ocbo02_o),
    .forwarded_value_i      (ocbi_i),
    .use_forwarded_value_i  (use_forwarded_value[1]),
    .out_o                  (ocbo01_o)
  );

  //   tap #02
  ocb_tap
  #(
    .DATA_SIZE    (DATA_SIZE),
    .RESET_VALUE  (RESET_VALUE)
  )
  u_tap_02
  (
    .clk                    (clk),
    .rst                    (rst),
    .flush_i                (pipeline_flush_i),
    .push_i                 (push_taps[2]),
    .prev_tap_out_i         (ocbo03_o),
    .forwarded_value_i      (ocbi_i),
    .use_forwarded_value_i  (use_forwarded_value[2]),
    .out_o                  (ocbo02_o)
  );

  //   tap #03
  ocb_tap
  #(
    .DATA_SIZE    (DATA_SIZE),
    .RESET_VALUE  (RESET_VALUE)
  )
  u_tap_03
  (
    .clk                    (clk),
    .rst                    (rst),
    .flush_i                (pipeline_flush_i),
    .push_i                 (push_taps[3]),
    .prev_tap_out_i         (ocbo04_o),
    .forwarded_value_i      (ocbi_i),
    .use_forwarded_value_i  (use_forwarded_value[3]),
    .out_o                  (ocbo03_o)
  );

  //   tap #04
  ocb_tap
  #(
    .DATA_SIZE    (DATA_SIZE),
    .RESET_VALUE  (RESET_VALUE)
  )
  u_tap_04
  (
    .clk                    (clk),
    .rst                    (rst),
    .flush_i                (pipeline_flush_i),
    .push_i                 (push_taps[4]),
    .prev_tap_out_i         (ocbo05_o),
    .forwarded_value_i      (ocbi_i),
    .use_forwarded_value_i  (use_forwarded_value[4]),
    .out_o                  (ocbo04_o)
  );

  //   tap #05
  ocb_tap
  #(
    .DATA_SIZE    (DATA_SIZE),
    .RESET_VALUE  (RESET_VALUE)
  )
  u_tap_05
  (
    .clk                    (clk),
    .rst                    (rst),
    .flush_i                (pipeline_flush_i),
    .push_i                 (push_taps[5]),
    .prev_tap_out_i         (ocbo06_o),
    .forwarded_value_i      (ocbi_i),
    .use_forwarded_value_i  (use_forwarded_value[5]),
    .out_o                  (ocbo05_o)
  );

  //   tap #06
  ocb_tap
  #(
    .DATA_SIZE    (DATA_SIZE),
    .RESET_VALUE  (RESET_VALUE)
  )
  u_tap_06
  (
    .clk                    (clk),
    .rst                    (rst),
    .flush_i                (pipeline_flush_i),
    .push_i                 (push_taps[6]),
    .prev_tap_out_i         (ocbo07_o),
    .forwarded_value_i      (ocbi_i),
    .use_forwarded_value_i  (use_forwarded_value[6]),
    .out_o                  (ocbo06_o)
  );

  //   tap #07 (entrance)
  ocb_tap
  #(
    .DATA_SIZE    (DATA_SIZE),
    .RESET_VALUE  (RESET_VALUE)
  )
  u_tap_07
  (
    .clk                    (clk),
    .rst                    (rst),
    .flush_i                (pipeline_flush_i),
    .push_i                 (push_taps[7]),
    .prev_tap_out_i         (RESET_VALUE),
    .forwarded_value_i      (ocbi_i),
    .use_forwarded_value_i  (use_forwarded_value[7]),
    .out_o                  (ocbo07_o)
  );

endmodule // mor1kx_ocb_marocchino



//---------------------------------//
// Reservation Station with 2 taps //
//---------------------------------//

module mor1kx_rsrvs_marocchino
#(
  parameter OPTION_OPERAND_WIDTH = 32,
  parameter OPC_WIDTH            =  1, // width of additional attributes
  parameter DEST_REG_ADDR_WIDTH  =  8, // OPTION_RF_ADDR_WIDTH + log2(Re-Ordering buffer width)
  parameter DEST_FLAG_ADDR_WIDTH =  3, // log2(Re-Ordering buffer width)
  // Reservation station is used at input of modules:
  //  1CLK: only parameter RSRVS-1CLK must be set to "1"
  //  MCLK: only parameter RSRVS-MCLK must be set to "1"
  //  LSU : both RSRVS-1CLK and RSRVS-MCLK parameters must be set to "0"
  parameter RSRVS_1CLK           = 0,
  parameter RSRVS_MCLK           = 0,
  // Packed operands for various reservation stations:
  //  # LSU : {   x,    x, rfb1, rfa1}
  //  # 1CLK: {   x,    x, rfb1, rfa1}
  //  # MCLK: {rfb2, rfa2, rfb1, rfa1}
  parameter DCOD_RFXX_WIDTH      = 64, // (2 * OPTION_OPERAND_WIDTH) for LSU; etc...
  // OMAN-to-DECODE hazards layout for various reservation stations:
  //  # LSU : {   x,    x,    x,    x, d2b1, d2a1, d1b1, d1a1 }
  //  # 1CLK: {   x,    x, carr, flag, d2b1, d2a1, d1b1, d1a1 }
  //  # MCLK: {d2b2, d2a2, d1b2, d1a2, d2b1, d2a1, d1b1, d1a1 }
  parameter BUSY_HAZARDS_FLAGS_WIDTH =  4, //: for LSU;  6: for 1CLK;  8: for MCLK
  parameter BUSY_HAZARDS_ADDRS_WIDTH = 32, // (4 * DEST_REG_ADDR_WIDTH) for LSU; etc...
  // EXEC-to-DECODE hazards layout for various reservation stations:
  //  # LSU : {   x,    x,    x,    x, d2b1, d2a1, d1b1, d1a1 }
  //  # 1CLK: {   x,    x,    x,    x, d2b1, d2a1, d1b1, d1a1 }
  //  # MCLK: {d2b2, d2a2, d1b2, d1a2, d2b1, d2a1, d1b1, d1a1 }
  parameter EXE2DEC_HAZARDS_FLAGS_WIDTH =  4 //: for LSU;  4: for 1CLK;  8: for MCLK
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
  //  ## FLAG or CARRY
  input                                     exec_flag_wb_i,         // EXECUTE instruction is writting FLAG
  input                                     exec_carry_wb_i,        // EXECUTE instruction is writting CARRY
  input        [(DEST_FLAG_ADDR_WIDTH-1):0] exec_flag_carry_adr_i,  // CARRY identifier
  //  ## A or B operand
  input                                     exec_rfd1_wb_i,          // EXECUTE instruction is writting RF
  input         [(DEST_REG_ADDR_WIDTH-1):0] exec_rfd1_adr_i,         // A or B operand
  //  ## for MCLK
  input                                     exec_rfd2_wb_i,          // EXECUTE instruction is writting RF
  input         [(DEST_REG_ADDR_WIDTH-1):0] exec_rfd2_adr_i,         // low part of A or B operand
  //  ## passing only with writting back
  input                                     padv_wb_i,

  // Hazard could be resolving
  //  ## FLAG or CARRY
  input                                     wb_flag_wb_i,           // WB instruction is writting FLAG
  input                                     wb_carry_wb_i,          // WB instruction is writting CARRY
  input        [(DEST_FLAG_ADDR_WIDTH-1):0] wb_flag_carry_adr_i,    // FLAG or CARRY identifier
  //  ## A or B operand
  input                                     wb_rfd1_wb_i,           // WB instruction is writting RF
  input         [(DEST_REG_ADDR_WIDTH-1):0] wb_rfd1_adr_i,          // A or B operand
  input        [(OPTION_OPERAND_WIDTH-1):0] wb_result1_i,
  //  ## for MCLK
  input                                     wb_rfd2_wb_i,            // WB instruction is writting RF
  input         [(DEST_REG_ADDR_WIDTH-1):0] wb_rfd2_adr_i,           // low part of A or B operand
  input        [(OPTION_OPERAND_WIDTH-1):0] wb_result2_i,

  // command and its additional attributes
  input                                     dcod_op_i,    // request the unit command
  input                   [(OPC_WIDTH-1):0] dcod_opc_i,   // additional attributes for command

  // outputs
  //   command attributes from busy stage
  output                  [(OPC_WIDTH-1):0] busy_opc_o,
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
  //  # 1CLK: {   x,    x, carr, flag, d2b1, d2a1, d1b1, d1a1 }
  //  # MCLK: {d2b2, d2a2, d1b2, d1a2, d2b1, d2a1, d1b1, d1a1 }

  // d1a1 related
  localparam  HAZARD_D1A1_FLG_POS = 0;
  localparam  HAZARD_D1A1_ADR_LSB = 0;
  localparam  HAZARD_D1A1_ADR_MSB = DEST_REG_ADDR_WIDTH - 1;
  // d1b1 related
  localparam  HAZARD_D1B1_FLG_POS = 1;
  localparam  HAZARD_D1B1_ADR_LSB = DEST_REG_ADDR_WIDTH;
  localparam  HAZARD_D1B1_ADR_MSB = 2 * DEST_REG_ADDR_WIDTH - 1;
  // d2a1 related
  localparam  HAZARD_D2A1_FLG_POS = 2;
  localparam  HAZARD_D2A1_ADR_LSB = 2 * DEST_REG_ADDR_WIDTH;
  localparam  HAZARD_D2A1_ADR_MSB = 3 * DEST_REG_ADDR_WIDTH - 1;
  // d2b1 related
  localparam  HAZARD_D2B1_FLG_POS = 3;
  localparam  HAZARD_D2B1_ADR_LSB = 3 * DEST_REG_ADDR_WIDTH;
  localparam  HAZARD_D2B1_ADR_MSB = 4 * DEST_REG_ADDR_WIDTH - 1;
  // d1a2 related
  localparam  HAZARD_D1A2_FLG_POS = 4;
  localparam  HAZARD_D1A2_ADR_LSB = 4 * DEST_REG_ADDR_WIDTH;
  localparam  HAZARD_D1A2_ADR_MSB = 5 * DEST_REG_ADDR_WIDTH - 1;
  // d1b2 related
  localparam  HAZARD_D1B2_FLG_POS = 5;
  localparam  HAZARD_D1B2_ADR_LSB = 5 * DEST_REG_ADDR_WIDTH;
  localparam  HAZARD_D1B2_ADR_MSB = 6 * DEST_REG_ADDR_WIDTH - 1;
  // d2a2 related
  localparam  HAZARD_D2A2_FLG_POS = 6;
  localparam  HAZARD_D2A2_ADR_LSB = 6 * DEST_REG_ADDR_WIDTH;
  localparam  HAZARD_D2A2_ADR_MSB = 7 * DEST_REG_ADDR_WIDTH - 1;
  // d2b2 related
  localparam  HAZARD_D2B2_FLG_POS = 7;
  localparam  HAZARD_D2B2_ADR_LSB = 7 * DEST_REG_ADDR_WIDTH;
  localparam  HAZARD_D2B2_ADR_MSB = 8 * DEST_REG_ADDR_WIDTH - 1;
  // FLAG related
  localparam  HAZARD_FLAG_FLG_POS = 4;
  localparam  HAZARD_FLAG_ADR_LSB = 4 * DEST_REG_ADDR_WIDTH;
  localparam  HAZARD_FLAG_ADR_MSB = HAZARD_FLAG_ADR_LSB + DEST_FLAG_ADDR_WIDTH - 1;
  // CARRY related
  localparam  HAZARD_CARR_FLG_POS = 5;
  localparam  HAZARD_CARR_ADR_LSB = HAZARD_FLAG_ADR_MSB + 1;
  localparam  HAZARD_CARR_ADR_MSB = HAZARD_CARR_ADR_LSB + DEST_FLAG_ADDR_WIDTH - 1;



  /**** BUSY stage ****/

  // DECODE->BUSY transfer
  wire dcod_pushing_busy = padv_decode_i & dcod_op_i &            // DECODE pushing BUSY: Latch DECODE output ...
                           ((exec_op_o & (~taking_op_i)) |        // DECODE pushing BUSY: ... if EXECUTE is busy or ...
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
  end // posedge clock

  // output from busy stage
  //  ## command attributes from busy stage
  assign busy_opc_o  = busy_opc_r;
  //  ## unit-is-busy flag
  assign unit_busy_o = busy_op_r;



  // busy: processing hazards wires (and regs) used across whole module
  // # common for all types of reservation station
  //  ## d1a1 related
  reg                                 busy_hazard_d1a1_r;
  reg       [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_d1a1_adr_r;
  wire                                busy_d1a1_pass2exec;
  wire                                busy_d1a1_muxing_wb;
  //  ## d1b1 related
  reg                                 busy_hazard_d1b1_r;
  reg       [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_d1b1_adr_r;
  wire                                busy_d1b1_pass2exec;
  wire                                busy_d1b1_muxing_wb;
  //  ## d2a1 related
  reg                                 busy_hazard_d2a1_r;
  reg       [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_d2a1_adr_r;
  wire                                busy_d2a1_pass2exec;
  wire                                busy_d2a1_muxing_wb;
  //  ## d2b1 related
  reg                                 busy_hazard_d2b1_r;
  reg       [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_d2b1_adr_r;
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
  // # exclusively for 1CLK reservation station
  //  ## FLAG related
  wire                                busy_hazard_f_w;
  wire                                busy_hazard_f_done;
  //  ## CARRY related
  wire                                busy_hazard_c_w;
  wire                                busy_hazard_c_done;

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
      busy_hazard_d1a1_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
      // d1b1 related
      busy_hazard_d1b1_r     <= 1'b0;
      busy_hazard_d1b1_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
      // d2a1 related
      busy_hazard_d2a1_r     <= 1'b0;
      busy_hazard_d2a1_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
      // d2b1 related
      busy_hazard_d2b1_r     <= 1'b0;
      busy_hazard_d2b1_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
    end
    else if (pipeline_flush_i) begin
      // d1a1 related
      busy_hazard_d1a1_r     <= 1'b0;
      busy_hazard_d1a1_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
      // d1b1 related
      busy_hazard_d1b1_r     <= 1'b0;
      busy_hazard_d1b1_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
      // d2a1 related
      busy_hazard_d2a1_r     <= 1'b0;
      busy_hazard_d2a1_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
      // d2b1 related
      busy_hazard_d2b1_r     <= 1'b0;
      busy_hazard_d2b1_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
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
        busy_hazard_d1a1_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
      end
      // d1b1 related
      if (busy_d1b1_muxing_wb | busy_pushing_exec) begin
        busy_hazard_d1b1_r     <= 1'b0;
        busy_hazard_d1b1_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
      end
      // d2a1 related
      if (busy_d2a1_muxing_wb | busy_pushing_exec) begin
        busy_hazard_d2a1_r     <= 1'b0;
        busy_hazard_d2a1_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
      end
      // d2b1 related
      if (busy_d2b1_muxing_wb | busy_pushing_exec) begin
        busy_hazard_d2b1_r     <= 1'b0;
        busy_hazard_d2b1_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
      end
    end
  end // @clock

  // d1a1 related
  assign busy_d1a1_pass2exec = busy_hazard_d1a1_r & exec_rfd1_wb_i & (busy_hazard_d1a1_adr_r == exec_rfd1_adr_i) & padv_wb_i;
  assign busy_d1a1_muxing_wb = busy_hazard_d1a1_r & wb_rfd1_wb_i & (busy_hazard_d1a1_adr_r == wb_rfd1_adr_i);
  // d1b1 related
  assign busy_d1b1_pass2exec = busy_hazard_d1b1_r & exec_rfd1_wb_i & (busy_hazard_d1b1_adr_r == exec_rfd1_adr_i) & padv_wb_i;
  assign busy_d1b1_muxing_wb = busy_hazard_d1b1_r & wb_rfd1_wb_i & (busy_hazard_d1b1_adr_r == wb_rfd1_adr_i);
  // d2a1 related
  assign busy_d2a1_pass2exec = busy_hazard_d2a1_r & exec_rfd2_wb_i & (busy_hazard_d2a1_adr_r == exec_rfd2_adr_i) & padv_wb_i;
  assign busy_d2a1_muxing_wb = busy_hazard_d2a1_r & wb_rfd2_wb_i & (busy_hazard_d2a1_adr_r == wb_rfd2_adr_i);
  // d2b1 related
  assign busy_d2b1_pass2exec = busy_hazard_d2b1_r & exec_rfd2_wb_i & (busy_hazard_d2b1_adr_r == exec_rfd2_adr_i) & padv_wb_i;
  assign busy_d2b1_muxing_wb = busy_hazard_d2b1_r & wb_rfd2_wb_i & (busy_hazard_d2b1_adr_r == wb_rfd2_adr_i);

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
  assign busy_rfa1 = busy_d1a1_muxing_wb ? wb_result1_i :
                     busy_d2a1_muxing_wb ? wb_result2_i : busy_rfa1_r;
  //  operand B1
  assign busy_rfb1 = busy_d1b1_muxing_wb ? wb_result1_i :
                     busy_d2b1_muxing_wb ? wb_result2_i : busy_rfb1_r;


  // exclusive latches for MCLK reservation station
  generate
  /* verilator lint_off WIDTH */
  if (RSRVS_MCLK == 1) begin : busy_mclk_enabled
  /* verilator lint_on WIDTH */
    // d1a2 related
    reg                                 busy_hazard_d1a2_r;
    reg       [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_d1a2_adr_r;
    // d1b2 related
    reg                                 busy_hazard_d1b2_r;
    reg       [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_d1b2_adr_r;
    // d2a2 related
    reg                                 busy_hazard_d2a2_r;
    reg       [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_d2a2_adr_r;
    // d2b2 related
    reg                                 busy_hazard_d2b2_r;
    reg       [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_d2b2_adr_r;
    // ---
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst) begin
        // d1a2 related
        busy_hazard_d1a2_r     <= 1'b0;
        busy_hazard_d1a2_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
        // d1b2 related
        busy_hazard_d1b2_r     <= 1'b0;
        busy_hazard_d1b2_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
        // d2a2 related
        busy_hazard_d2a2_r     <= 1'b0;
        busy_hazard_d2a2_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
        // d2b2 related
        busy_hazard_d2b2_r     <= 1'b0;
        busy_hazard_d2b2_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
      end
      else if (pipeline_flush_i) begin
        // d1a2 related
        busy_hazard_d1a2_r     <= 1'b0;
        busy_hazard_d1a2_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
        // d1b2 related
        busy_hazard_d1b2_r     <= 1'b0;
        busy_hazard_d1b2_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
        // d2a2 related
        busy_hazard_d2a2_r     <= 1'b0;
        busy_hazard_d2a2_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
        // d2b2 related
        busy_hazard_d2b2_r     <= 1'b0;
        busy_hazard_d2b2_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
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
          busy_hazard_d1a2_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
        end
        // d1b2 related
        if (busy_d1b2_muxing_wb | busy_pushing_exec) begin
          busy_hazard_d1b2_r     <= 1'b0;
          busy_hazard_d1b2_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
        end
        // d2a2 related
        if (busy_d2a2_muxing_wb | busy_pushing_exec) begin
          busy_hazard_d2a2_r     <= 1'b0;
          busy_hazard_d2a2_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
        end
        // d2b2 related
        if (busy_d2b2_muxing_wb | busy_pushing_exec) begin
          busy_hazard_d2b2_r     <= 1'b0;
          busy_hazard_d2b2_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
        end
      end
    end // @clock
    // ---
    // d1a2 related
    assign busy_hazard_d1a2_w  = busy_hazard_d1a2_r; // MCLK
    assign busy_d1a2_pass2exec = busy_hazard_d1a2_r & exec_rfd1_wb_i & (busy_hazard_d1a2_adr_r == exec_rfd1_adr_i) & padv_wb_i;
    assign busy_d1a2_muxing_wb = busy_hazard_d1a2_r & wb_rfd1_wb_i & (busy_hazard_d1a2_adr_r == wb_rfd1_adr_i);
    // d1b2 related
    assign busy_hazard_d1b2_w  = busy_hazard_d1b2_r; // MCLK
    assign busy_d1b2_pass2exec = busy_hazard_d1b2_r & exec_rfd1_wb_i & (busy_hazard_d1b2_adr_r == exec_rfd1_adr_i) & padv_wb_i;
    assign busy_d1b2_muxing_wb = busy_hazard_d1b2_r & wb_rfd1_wb_i & (busy_hazard_d1b2_adr_r == wb_rfd1_adr_i);
    // d2a2 related
    assign busy_hazard_d2a2_w  = busy_hazard_d2a2_r; // MCLK
    assign busy_d2a2_pass2exec = busy_hazard_d2a2_r & exec_rfd2_wb_i & (busy_hazard_d2a2_adr_r == exec_rfd2_adr_i) & padv_wb_i;
    assign busy_d2a2_muxing_wb = busy_hazard_d2a2_r & wb_rfd2_wb_i & (busy_hazard_d2a2_adr_r == wb_rfd2_adr_i);
    // d2b2 related
    assign busy_hazard_d2b2_w  = busy_hazard_d2b2_r; // MCLK
    assign busy_d2b2_pass2exec = busy_hazard_d2b2_r & exec_rfd2_wb_i & (busy_hazard_d2b2_adr_r == exec_rfd2_adr_i) & padv_wb_i;
    assign busy_d2b2_muxing_wb = busy_hazard_d2b2_r & wb_rfd2_wb_i & (busy_hazard_d2b2_adr_r == wb_rfd2_adr_i);

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
    assign busy_rfa2_w = busy_d1a2_muxing_wb ? wb_result1_i :
                         busy_d2a2_muxing_wb ? wb_result2_i : busy_rfa2_r;
    //  operand B2
    assign busy_rfb2_w = busy_d1b2_muxing_wb ? wb_result1_i :
                         busy_d2b2_muxing_wb ? wb_result2_i : busy_rfb2_r;
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

  // FLAG and CARRY processing exclusively for 1CLK reservation station
  generate
  /* verilator lint_off WIDTH */
  if (RSRVS_1CLK == 1) begin : carry_flag_enabled
  /* verilator lint_on WIDTH */
    // FLAG
    reg                            busy_hazard_f_r;
    reg [DEST_FLAG_ADDR_WIDTH-1:0] busy_hazard_f_adr_r;
    // CARRY
    reg                            busy_hazard_c_r;
    reg [DEST_FLAG_ADDR_WIDTH-1:0] busy_hazard_c_adr_r;
    // ---
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst) begin
        // FLAG
        busy_hazard_f_r     <= 1'b0;
        busy_hazard_f_adr_r <= {DEST_FLAG_ADDR_WIDTH{1'b0}};
        // CARRY
        busy_hazard_c_r     <= 1'b0;
        busy_hazard_c_adr_r <= {DEST_FLAG_ADDR_WIDTH{1'b0}};
      end
      else if (pipeline_flush_i) begin
        // FLAG
        busy_hazard_f_r     <= 1'b0;
        busy_hazard_f_adr_r <= {DEST_FLAG_ADDR_WIDTH{1'b0}};
        // CARRY
        busy_hazard_c_r     <= 1'b0;
        busy_hazard_c_adr_r <= {DEST_FLAG_ADDR_WIDTH{1'b0}};
      end
      else if (dcod_pushing_busy) begin
        // FLAG
        busy_hazard_f_r     <= busy_hazards_flags_i[HAZARD_FLAG_FLG_POS];
        busy_hazard_f_adr_r <= busy_hazards_addrs_i[HAZARD_FLAG_ADR_MSB:HAZARD_FLAG_ADR_LSB];
        // CARRY
        busy_hazard_c_r     <= busy_hazards_flags_i[HAZARD_CARR_FLG_POS];
        busy_hazard_c_adr_r <= busy_hazards_addrs_i[HAZARD_CARR_ADR_MSB:HAZARD_CARR_ADR_LSB];
      end
      else begin
        // FLAG
        if (busy_hazard_f_done) begin
          busy_hazard_f_r     <= 1'b0;
          busy_hazard_f_adr_r <= {DEST_FLAG_ADDR_WIDTH{1'b0}};
        end
        // CARRY
        if (busy_hazard_c_done) begin
          busy_hazard_c_r     <= 1'b0;
          busy_hazard_c_adr_r <= {DEST_FLAG_ADDR_WIDTH{1'b0}};
        end
      end
    end // @clock
    // ---
    // FLAG
    assign busy_hazard_f_w    = busy_hazard_f_r;
    assign busy_hazard_f_done = busy_hazard_f_r &
                                ((exec_flag_wb_i & (busy_hazard_f_adr_r == exec_flag_carry_adr_i) & padv_wb_i) |
                                 (wb_flag_wb_i   & (busy_hazard_f_adr_r == wb_flag_carry_adr_i)));
    // CARRY
    assign busy_hazard_c_w    = busy_hazard_c_r;
    assign busy_hazard_c_done = busy_hazard_c_r &
                                ((exec_carry_wb_i & (busy_hazard_c_adr_r == exec_flag_carry_adr_i) & padv_wb_i) |
                                 (wb_carry_wb_i   & (busy_hazard_c_adr_r == wb_flag_carry_adr_i)));
  end
  else begin : carry_flag_disabled
    // FLAG
    assign busy_hazard_f_w    = 1'b0; // not 1CLK
    assign busy_hazard_f_done = 1'b0; // not 1CLK
    // CARRY
    assign busy_hazard_c_w    = 1'b0; // not 1CLK
    assign busy_hazard_c_done = 1'b0; // not 1CLK
  end
  endgenerate

  // busy pushing execute: no more hazards in BUSY
  wire busy_free_of_hazards = ((~busy_hazard_d1a1_r) | busy_d1a1_muxing_wb | busy_d1a1_pass2exec) &
                              ((~busy_hazard_d1b1_r) | busy_d1b1_muxing_wb | busy_d1b1_pass2exec) &
                              ((~busy_hazard_d2a1_r) | busy_d2a1_muxing_wb | busy_d2a1_pass2exec) &
                              ((~busy_hazard_d2b1_r) | busy_d2b1_muxing_wb | busy_d2b1_pass2exec) &
                              ((~busy_hazard_d1a2_w) | busy_d1a2_muxing_wb | busy_d1a2_pass2exec) &
                              ((~busy_hazard_d1b2_w) | busy_d1b2_muxing_wb | busy_d1b2_pass2exec) &
                              ((~busy_hazard_d2a2_w) | busy_d2a2_muxing_wb | busy_d2a2_pass2exec) &
                              ((~busy_hazard_d2b2_w) | busy_d2b2_muxing_wb | busy_d2b2_pass2exec) &
                              ((~busy_hazard_f_w)    | busy_hazard_f_done)                        &
                              ((~busy_hazard_c_w)    | busy_hazard_c_done);


  /**** EXECUTE stage latches ****/

  // DECODE->EXECUTE transfer
  wire   dcod_pushing_exec = padv_decode_i & dcod_op_i  &       // DECODE pushing EXECUTE: New command ...
                             (~exec_op_o | taking_op_i) &       // DECODE pushing EXECUTE: ... and unit is free ...
                             (~omn2dec_a_hazard_i)      &       // DECODE pushing EXECUTE: ... and no waiting for resolving hazards ...
                             (~exe2dec_a_hazard_i | padv_wb_i); // DECODE pushing EXECUTE: ... forwarding from WB if required.

  // BUSY->EXECUTE transfer
  assign busy_pushing_exec = unit_busy_o          &       // BUSY pushing EXECUTE: There is pending instruction ...
                             busy_free_of_hazards &       // BUSY pushing EXECUTE: ... and hazards are resolved or could be passed ...
                             (~exec_op_o | taking_op_i);  // BUSY pushing EXECUTE: ... and EXECUTE is free.



  // execute: command and attributes
  reg                 exec_op_r;
  reg [OPC_WIDTH-1:0] exec_opc_r;

  // ---
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
  end // posedge clock

  // outputs
  //   command and its additional attributes
  assign exec_op_o  = exec_op_r;
  assign exec_opc_o = exec_opc_r;



  // execute: operands for all reservation station types
  reg exec_hazard_d1a1_r;
  reg exec_hazard_d1b1_r;
  reg exec_hazard_d2a1_r;
  reg exec_hazard_d2b1_r;

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
    else if (exec_hazard_d1a1_r | exec_hazard_d1b1_r | exec_hazard_d2a1_r | exec_hazard_d2b1_r | taking_op_i) begin
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
    else if (exec_hazard_d1a1_r | exec_hazard_d1b1_r | exec_hazard_d2a1_r | exec_hazard_d2b1_r) begin
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
      else if (exec_hazard_d1a2_r | exec_hazard_d1b2_r | exec_hazard_d2a2_r | exec_hazard_d2b2_r | taking_op_i) begin
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
      else if (exec_hazard_d1a2_r | exec_hazard_d1b2_r | exec_hazard_d2a2_r | exec_hazard_d2b2_r) begin
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
