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
  parameter USE_OPC              =  0, // use additional attributes for command
  parameter OPC_WIDTH            =  1, // width of additional attributes
  parameter DEST_REG_ADDR_WIDTH  =  8, // OPTION_RF_ADDR_WIDTH + log2(Re-Ordering buffer width)
  // Activate the part for tracking and resolving FLAG and CARRY hazards
  // Actually, it makes sense for 1-clock executive unit only
  parameter USE_RSVRS_FLAG_CARRY =  0,
  parameter DEST_FLAG_ADDR_WIDTH =  3  // log2(Re-Ordering buffer width)
)
(
  // clocks and resets
  input                                 clk,
  input                                 rst,

  // pipeline control signals
  input                                 pipeline_flush_i,
  input                                 padv_decode_i,
  input                                 taking_op_i,      // a unit is taking input for execution

  // input data from DECODE
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_rfa_i,
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_rfb_i,

  // OMAN-to-DECODE hazards
  //  combined flag
  input                                 omn2dec_hazards_i,      // OR-combined hazards
  //  by FLAG and CARRY
  input                                 busy_hazard_f_i,     // by operand FLAG
  input      [DEST_FLAG_ADDR_WIDTH-1:0] busy_hazard_f_adr_i, // hazard address of FLAG
  input                                 busy_hazard_c_i,     // by operand CARRY
  input      [DEST_FLAG_ADDR_WIDTH-1:0] busy_hazard_c_adr_i, // hazard address of CARRY
  //  by operands
  input                                 busy_hazard_a_i,     // by operand A
  input       [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_a_adr_i, // hazard by destination register for operand A
  input                                 busy_hazard_b_i,     // by operand B
  input       [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_b_adr_i, // hazard by destination register for operand B

  // EXEC-to-DECODE hazards
  //  combined flag
  input                                 exe2dec_hazards_i,      // OR-combined hazards
  //  by operands
  input                                 exe2dec_hazard_a_i,     // by operand A
  input                                 exe2dec_hazard_b_i,     // by operand B

  // Data for hazards resolving
  //  hazard could be passed from DECODE to EXECUTE
  input                                 exec_flag_wb_i,         // EXECUTE instruction is writting FLAG
  input                                 exec_carry_wb_i,        // EXECUTE instruction is writting CARRY
  input      [DEST_FLAG_ADDR_WIDTH-1:0] exec_flag_carry_adr_i,  // CARRY identifier
  input                                 exec_rf_wb_i,           // EXECUTE instruction is writting RF
  input       [DEST_REG_ADDR_WIDTH-1:0] exec_rfd_adr_i,         // A or B operand
  input                                 padv_wb_i,
  //  hazard could be resolving
  input                                 wb_flag_wb_i,           // WB instruction is writting FLAG
  input                                 wb_carry_wb_i,          // WB instruction is writting CARRY
  input      [DEST_FLAG_ADDR_WIDTH-1:0] wb_flag_carry_adr_i,    // FLAG or CARRY identifier
  input                                 wb_rf_wb_i,             // WB instruction is writting RF
  input       [DEST_REG_ADDR_WIDTH-1:0] wb_rfd_adr_i,           // A or B operand
  input      [OPTION_OPERAND_WIDTH-1:0] wb_result_i,

  // command and its additional attributes
  input                                 dcod_op_i,    // request the unit command
  input                 [OPC_WIDTH-1:0] dcod_opc_i,   // additional attributes for command

  // outputs
  //   command attributes from busy stage
  output                [OPC_WIDTH-1:0] busy_opc_o,
  //   command and its additional attributes
  output                                exec_op_o,    // request the unit command
  output                [OPC_WIDTH-1:0] exec_opc_o,   // additional attributes for command
  //   operands
  output     [OPTION_OPERAND_WIDTH-1:0] exec_rfa_o,
  output     [OPTION_OPERAND_WIDTH-1:0] exec_rfb_o,
  //   unit-is-busy flag
  output                                unit_busy_o
);

  /**** BUSY stage latches ****/

  // busy: command
  reg                                 busy_op_r;
  // busy: operands
  //   ## registers for operands A & B
  reg      [OPTION_OPERAND_WIDTH-1:0] busy_rfa_r;
  reg      [OPTION_OPERAND_WIDTH-1:0] busy_rfb_r;
  //   ## multiplexed with forwarded value from WB
  wire     [OPTION_OPERAND_WIDTH-1:0] busy_rfa;
  wire     [OPTION_OPERAND_WIDTH-1:0] busy_rfb;
  //   ## controls for forwarding multiplexors (only WB could be muxed)
  wire                                busy_rfa_muxing_wb;
  wire                                busy_rfb_muxing_wb;
  //   ## indicators that a hazard could be passed to EXECUTE
  wire                                busy_rfa_pass2exec;
  wire                                busy_rfb_pass2exec;
  //   ## hazard flags and destination addresses
  reg                                 busy_hazard_a_r;
  reg       [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_a_adr_r;
  reg                                 busy_hazard_b_r;
  reg       [DEST_REG_ADDR_WIDTH-1:0] busy_hazard_b_adr_r;
  // busy pushing execute
  wire                                busy_free_of_hazards;
  wire                                busy_pushing_exec;


  // DECODE->BUSY transfer
  wire dcod_pushing_busy = padv_decode_i & dcod_op_i &            // DECODE pushing BUSY: Latch DECODE output ...
                           ((exec_op_o & (~taking_op_i)) |        // DECODE pushing BUSY: ... if EXECUTE is busy or ...
                            omn2dec_hazards_i            |        // DECODE pushing BUSY: ... if an OMAN-to-DECODE hazard or ...
                            (exe2dec_hazards_i & (~padv_wb_i)));  // DECODE pushing BUSY: ... if an EXECUTE-to-DECODE couldn't be passed.

  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      busy_op_r  <= 1'b0;
    else if (pipeline_flush_i)
      busy_op_r  <= 1'b0;
    else if (dcod_pushing_busy)
      busy_op_r  <= dcod_op_i;
    else if (busy_pushing_exec)
      busy_op_r  <= 1'b0;
  end // posedge clock
  // ---
  wire [OPC_WIDTH-1:0] busy_opc_w;
  // ---
  generate
  /* verilator lint_off WIDTH */
  if (USE_OPC != 0) begin : busy_opc_enabled
  /* verilator lint_on WIDTH */
    // busy: additional command attributes
    reg [OPC_WIDTH-1:0] busy_opc_r;
    // ---
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        busy_opc_r <= {OPC_WIDTH{1'b0}};
      else if (pipeline_flush_i)
        busy_opc_r <= {OPC_WIDTH{1'b0}};
      else if (dcod_pushing_busy)
        busy_opc_r <= dcod_opc_i;
      else if (busy_pushing_exec)
        busy_opc_r <= {OPC_WIDTH{1'b0}};
    end // posedge clock
    // ---
    assign busy_opc_w = busy_opc_r;
  end
  else begin : busy_opc_disabled
    assign busy_opc_w = {OPC_WIDTH{1'b0}};
  end
  endgenerate
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      // operand A
      busy_hazard_a_r     <= 1'b0;
      busy_hazard_a_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
      // operand B
      busy_hazard_b_r     <= 1'b0;
      busy_hazard_b_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
    end
    else if (pipeline_flush_i) begin
      // operand A
      busy_hazard_a_r     <= 1'b0;
      busy_hazard_a_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
      // operand B
      busy_hazard_b_r     <= 1'b0;
      busy_hazard_b_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
    end
    else if (dcod_pushing_busy) begin
      // operand A
      busy_hazard_a_r     <= busy_hazard_a_i;
      busy_hazard_a_adr_r <= busy_hazard_a_adr_i;
      // operand B
      busy_hazard_b_r     <= busy_hazard_b_i;
      busy_hazard_b_adr_r <= busy_hazard_b_adr_i;
    end
    else begin
      // complete forwarding for operand A
      if (busy_rfa_muxing_wb | busy_pushing_exec) begin
        busy_hazard_a_r     <= 1'b0;
        busy_hazard_a_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
      end
      // complete forwarding for operand B
      if (busy_rfb_muxing_wb | busy_pushing_exec) begin
        busy_hazard_b_r     <= 1'b0;
        busy_hazard_b_adr_r <= {DEST_REG_ADDR_WIDTH{1'b0}};
      end
    end
  end // @clock
  // ---
  always @(posedge clk) begin
    if (dcod_pushing_busy) begin
      busy_rfa_r <= dcod_rfa_i;
      busy_rfb_r <= dcod_rfb_i;
    end
    else begin
      // complete forwarding for operand A
      if (busy_rfa_muxing_wb)
        busy_rfa_r <= busy_rfa;
      // complete forwarding for operand B
      if (busy_rfb_muxing_wb)
        busy_rfb_r <= busy_rfb;
    end
  end // @clock
  // controls for forwarding multiplexors (only WB could be muxed)
  assign busy_rfa_muxing_wb = busy_hazard_a_r & wb_rf_wb_i & (busy_hazard_a_adr_r == wb_rfd_adr_i);
  assign busy_rfb_muxing_wb = busy_hazard_b_r & wb_rf_wb_i & (busy_hazard_b_adr_r == wb_rfd_adr_i);
  // last forward (from WB)
  assign busy_rfa = busy_rfa_muxing_wb ? wb_result_i : busy_rfa_r;
  assign busy_rfb = busy_rfb_muxing_wb ? wb_result_i : busy_rfb_r;

  // output from busy stage
  //  ## command attributes from busy stage
  assign busy_opc_o  = busy_opc_w;
  //  ## unit-is-busy flag
  assign unit_busy_o = busy_op_r;

  // FLAG and CARRY processing
  // FLAG
  wire busy_hazard_f_w;
  wire busy_hazard_f_done;
  // CARRY
  wire busy_hazard_c_w;
  wire busy_hazard_c_done;
  // ---
  generate
  /* verilator lint_off WIDTH */
  if (USE_RSVRS_FLAG_CARRY != 0) begin : carry_flag_enabled
  /* verilator lint_on WIDTH */
    reg                            busy_hazard_f_r;
    reg [DEST_FLAG_ADDR_WIDTH-1:0] busy_hazard_f_adr_r;
    reg                            busy_hazard_c_r;
    reg [DEST_FLAG_ADDR_WIDTH-1:0] busy_hazard_c_adr_r;
    // ---
    assign busy_hazard_f_w = busy_hazard_f_r;
    assign busy_hazard_c_w = busy_hazard_c_r;
    // ---
    assign busy_hazard_f_done = busy_hazard_f_r &
                                ((exec_flag_wb_i & (busy_hazard_f_adr_r == exec_flag_carry_adr_i) & padv_wb_i) |
                                 (wb_flag_wb_i   & (busy_hazard_f_adr_r == wb_flag_carry_adr_i)));
    assign busy_hazard_c_done = busy_hazard_c_r &
                                ((exec_carry_wb_i & (busy_hazard_c_adr_r == exec_flag_carry_adr_i) & padv_wb_i) |
                                 (wb_carry_wb_i   & (busy_hazard_c_adr_r == wb_flag_carry_adr_i)));
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
        busy_hazard_f_r     <= busy_hazard_f_i;
        busy_hazard_f_adr_r <= busy_hazard_f_adr_i;
        // CARRY
        busy_hazard_c_r     <= busy_hazard_c_i;
        busy_hazard_c_adr_r <= busy_hazard_c_adr_i;
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
  end
  else begin : carry_flag_disabled
    // FLAG
    assign busy_hazard_f_w    = 1'b0;
    assign busy_hazard_f_done = 1'b0;
    // CARRY
    assign busy_hazard_c_w    = 1'b0;
    assign busy_hazard_c_done = 1'b0;
  end
  endgenerate

  // busy pushing execute
  //  # indicators that a hazard could be passed to EXECUTE
  assign busy_rfa_pass2exec = busy_hazard_a_r & exec_rf_wb_i & (busy_hazard_a_adr_r == exec_rfd_adr_i) & padv_wb_i;
  assign busy_rfb_pass2exec = busy_hazard_b_r & exec_rf_wb_i & (busy_hazard_b_adr_r == exec_rfd_adr_i) & padv_wb_i;
  //  # no more hazards in BUSY
  assign busy_free_of_hazards = ((~busy_hazard_a_r) | busy_rfa_muxing_wb | busy_rfa_pass2exec) &
                                ((~busy_hazard_b_r) | busy_rfb_muxing_wb | busy_rfb_pass2exec) &
                                ((~busy_hazard_f_w) | busy_hazard_f_done)                      &
                                ((~busy_hazard_c_w) | busy_hazard_c_done);


  /**** EXECUTE stage latches ****/

  // execute:
  reg                                 exec_op_r;
  // execute: operands
  //   ## registers
  reg      [OPTION_OPERAND_WIDTH-1:0] exec_rfa_r;
  reg      [OPTION_OPERAND_WIDTH-1:0] exec_rfb_r;
  //   ## multiplexed with forwarded value from WB
  wire     [OPTION_OPERAND_WIDTH-1:0] exec_rfa;
  wire     [OPTION_OPERAND_WIDTH-1:0] exec_rfb;
  // execute hazard flags
  reg                                 exec_hazard_a_r;
  reg                                 exec_hazard_b_r;

  // DECODE->EXECUTE transfer
  wire   dcod_pushing_exec = padv_decode_i & dcod_op_i  &       // DECODE pushing EXECUTE: New command ...
                             (~exec_op_o | taking_op_i) &       // DECODE pushing EXECUTE: ... and unit is free ...
                             (~omn2dec_hazards_i)       &       // DECODE pushing EXECUTE: ... and no waiting for resolving hazards ...
                             (~exe2dec_hazards_i | padv_wb_i);  // DECODE pushing EXECUTE: ... forwarding from WB if required.

  // BUSY->EXECUTE transfer
  assign busy_pushing_exec = unit_busy_o          &       // BUSY pushing EXECUTE: There is pending instruction ...
                             busy_free_of_hazards &       // BUSY pushing EXECUTE: ... and hazards are resolved or could be passed ...
                             (~exec_op_o | taking_op_i);  // BUSY pushing EXECUTE: ... and EXECUTE is free.

  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      exec_op_r  <= 1'b0;
    else if (pipeline_flush_i)
      exec_op_r  <= 1'b0;
    else if (dcod_pushing_exec)
      exec_op_r  <= dcod_op_i;
    else if (busy_pushing_exec)
      exec_op_r  <= busy_op_r;
    else if (taking_op_i)
      exec_op_r  <= 1'b0;
  end // posedge clock
  //---
  wire [OPC_WIDTH-1:0] exec_opc_w;
  //---
  generate
  /* verilator lint_off WIDTH */
  if (USE_OPC != 0) begin : exec_opc_enabled
  /* verilator lint_on WIDTH */
    // execute: additional command attributes
    reg [OPC_WIDTH-1:0] exec_opc_r;
    // ---
    always @(posedge clk `OR_ASYNC_RST) begin
      if (rst)
        exec_opc_r <= {OPC_WIDTH{1'b0}};
      else if (pipeline_flush_i)
        exec_opc_r <= {OPC_WIDTH{1'b0}};
      else if (dcod_pushing_exec)
        exec_opc_r <= dcod_opc_i;
      else if (busy_pushing_exec)
        exec_opc_r <= busy_opc_w;
      else if (taking_op_i)
        exec_opc_r <= {OPC_WIDTH{1'b0}};
    end // posedge clock
    // ---
    assign exec_opc_w = exec_opc_r;
  end
  else begin : exec_opc_disabled
    assign exec_opc_w = {OPC_WIDTH{1'b0}};
  end
  endgenerate
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      exec_hazard_a_r <= 1'b0;
      exec_hazard_b_r <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      exec_hazard_a_r <= 1'b0;
      exec_hazard_b_r <= 1'b0;
    end
    else if (dcod_pushing_exec) begin
      exec_hazard_a_r <= exe2dec_hazard_a_i;
      exec_hazard_b_r <= exe2dec_hazard_b_i;
    end
    else if (busy_pushing_exec) begin
      exec_hazard_a_r <= busy_rfa_pass2exec;
      exec_hazard_b_r <= busy_rfb_pass2exec;
    end
    else if (exec_hazard_a_r | exec_hazard_b_r | taking_op_i) begin
      // at the stage either A-hazard or B-hazard takes place,
      // but not both, so we process them at the same time
      exec_hazard_a_r <= 1'b0;
      exec_hazard_b_r <= 1'b0;
    end
  end // @clock
  // ---
  always @(posedge clk) begin
    if (dcod_pushing_exec) begin
      exec_rfa_r <= dcod_rfa_i;
      exec_rfb_r <= dcod_rfb_i;
    end
    else if (busy_pushing_exec) begin
      exec_rfa_r <= busy_rfa;
      exec_rfb_r <= busy_rfb;
    end
    else if (exec_hazard_a_r | exec_hazard_b_r) begin
      exec_rfa_r <= exec_rfa;
      exec_rfb_r <= exec_rfb;
    end
  end // @clock
  // last forward (from WB)
  assign exec_rfa = exec_hazard_a_r ? wb_result_i : exec_rfa_r;
  assign exec_rfb = exec_hazard_b_r ? wb_result_i : exec_rfb_r;

  // outputs
  //   command and its additional attributes
  assign exec_op_o  = exec_op_r;
  assign exec_opc_o = exec_opc_w;
  //   operands
  assign exec_rfa_o = exec_rfa;
  assign exec_rfb_o = exec_rfb;

endmodule // mor1kx_rsrvs_marocchino
