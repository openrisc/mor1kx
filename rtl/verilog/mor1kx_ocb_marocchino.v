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
// Reservation Station with 2 Taps //
//---------------------------------//

module mor1kx_rsrvs_marocchino
#(
  parameter OPTION_OPERAND_WIDTH = 32,
  parameter OPC_WIDTH            =  1 // width of OPC - additional attributes for command
)
(
  // clocks and resets
  input                                 clk,
  input                                 rst,

  // pipeline control signals in
  input                                 pipeline_flush_i,
  input                                 padv_decode_i,
  input                                 take_op_i,         // a unit takes input for execution

  // input data
  //   from DECODE
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_rfa_i,
  input      [OPTION_OPERAND_WIDTH-1:0] dcod_rfb_i,
  //   forwarding from WB
  input                                 exe2dec_hazard_a_i,
  input                                 exe2dec_hazard_b_i,
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

  // busy command and its additional attributes
  reg                                 busy_op_r;
  reg                 [OPC_WIDTH-1:0] busy_opc_r;
  // busy operands
  //   ## registers
  reg      [OPTION_OPERAND_WIDTH-1:0] busy_rfa_r;
  reg      [OPTION_OPERAND_WIDTH-1:0] busy_rfb_r;
  //   ## multiplexed with forwarded value from WB
  wire     [OPTION_OPERAND_WIDTH-1:0] busy_rfa;
  wire     [OPTION_OPERAND_WIDTH-1:0] busy_rfb;
  // busy hazard flags
  reg                                 busy_hazard_a_r;
  reg                                 busy_hazard_b_r;

  // busy stage advance enable
  wire busy_padv = (padv_decode_i & dcod_op_i & exec_op_o) | take_op_i;

  // busy stage latches decode output
  wire busy_latches_dcod = exec_op_o & (~take_op_i);

  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      busy_op_r  <= 1'b0;
      busy_opc_r <= {OPC_WIDTH{1'b0}};
    end
    else if (pipeline_flush_i) begin
      busy_op_r  <= 1'b0;
      busy_opc_r <= {OPC_WIDTH{1'b0}};
    end
    else if (busy_padv) begin
      busy_op_r  <= dcod_op_i  & busy_latches_dcod;
      busy_opc_r <= dcod_opc_i & {OPC_WIDTH{busy_latches_dcod}};
    end
  end // posedge clock
  // ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      busy_hazard_a_r <= 1'b0;
      busy_hazard_b_r <= 1'b0;
    end
    else if (pipeline_flush_i) begin
      busy_hazard_a_r <= 1'b0;
      busy_hazard_b_r <= 1'b0;
    end
    else if (busy_padv) begin
      busy_hazard_a_r <= exe2dec_hazard_a_i & busy_latches_dcod;
      busy_hazard_b_r <= exe2dec_hazard_b_i & busy_latches_dcod;
    end
    else if (busy_hazard_a_r | busy_hazard_b_r) begin // complete forwarding from WB
      busy_hazard_a_r <= 1'b0;
      busy_hazard_b_r <= 1'b0;
    end
  end // @clock
  // ---
  always @(posedge clk) begin
    if (busy_padv) begin
      busy_rfa_r <= dcod_rfa_i;
      busy_rfb_r <= dcod_rfb_i;
    end
    else if (busy_hazard_a_r | busy_hazard_b_r) begin // complete forwarding from WB
      busy_rfa_r <= busy_rfa;
      busy_rfb_r <= busy_rfb;
    end
  end // @clock
  // last forward (from WB)
  assign busy_rfa = busy_hazard_a_r ? wb_result_i : busy_rfa_r;
  assign busy_rfb = busy_hazard_b_r ? wb_result_i : busy_rfb_r;

  // output from busy stage
  //  ## command attributes from busy stage
  assign busy_opc_o  = busy_opc_r;
  //  ## unit-is-busy flag
  assign unit_busy_o = busy_op_r;


  /**** EXECUTE stage latches ****/

  // execute command and its additional attributes
  reg                                 exec_op_r;
  reg                 [OPC_WIDTH-1:0] exec_opc_r;
  // execute operands
  //   ## registers
  reg      [OPTION_OPERAND_WIDTH-1:0] exec_rfa_r;
  reg      [OPTION_OPERAND_WIDTH-1:0] exec_rfb_r;
  //   ## multiplexed with forwarded value from WB
  wire     [OPTION_OPERAND_WIDTH-1:0] exec_rfa;
  wire     [OPTION_OPERAND_WIDTH-1:0] exec_rfb;
  // execute hazard flags
  reg                                 exec_hazard_a_r;
  reg                                 exec_hazard_b_r;

  // execute stage advance enable
  wire exec_padv = (padv_decode_i & dcod_op_i & (~exec_op_o)) | take_op_i;

  // execute stage latches DECODE output
  wire exec_latches_dcod = padv_decode_i & dcod_op_i;
  // execute stage latches BUSY stage output
  wire exec_latches_busy = take_op_i & busy_op_r;

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
    else if (exec_padv) begin
      exec_op_r  <= exec_latches_dcod ? dcod_op_i :
                    exec_latches_busy ? busy_op_r :
                                        1'b0;
      exec_opc_r <= exec_latches_dcod ? dcod_opc_i :
                    exec_latches_busy ? busy_opc_r :
                                        {OPC_WIDTH{1'b0}};
    end
  end // posedge clock
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
    else if (exec_padv) begin
      // pay attantion that BUSY output is forwarded already
      // so, only DECODE stage flags make sense here
      exec_hazard_a_r <= exe2dec_hazard_a_i & exec_latches_dcod;
      exec_hazard_b_r <= exe2dec_hazard_b_i & exec_latches_dcod;
    end
    else if (exec_hazard_a_r | exec_hazard_b_r) begin // complete forwarding from WB
      exec_hazard_a_r <= 1'b0;
      exec_hazard_b_r <= 1'b0;
    end
  end // @clock
  // ---
  always @(posedge clk) begin
    if (exec_padv) begin
      exec_rfa_r <= exec_latches_dcod ? dcod_rfa_i :
                    exec_latches_busy ? busy_rfa   :
                                        {OPTION_OPERAND_WIDTH{1'b0}};
      exec_rfb_r <= exec_latches_dcod ? dcod_rfb_i :
                    exec_latches_busy ? busy_rfb   :
                                        {OPTION_OPERAND_WIDTH{1'b0}};
    end
    else if (exec_hazard_a_r | exec_hazard_b_r) begin // complete forwarding from WB
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
  assign exec_opc_o = exec_opc_r;
  //   operands
  assign exec_rfa_o = exec_rfa;
  assign exec_rfb_o = exec_rfb;

endmodule // mor1kx_rsrvs_marocchino
