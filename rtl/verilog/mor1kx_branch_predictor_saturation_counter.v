/******************************************************************************
 This Source Code Form is subject to the terms of the
 Open Hardware Description License, v. 1.0. If a copy
 of the OHDL was not distributed with this file, You
 can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

 Description: Branch prediction module
 Generates a predicted flag output and compares that to the real flag
 when it comes back in the following pipeline stage.
 Signals are deliberately not named after the pipeline stage they belong to,
 in order to keep this module generic.

 Copyright (C) 2013 Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>

 ******************************************************************************/

`include "mor1kx-defines.v"

module mor1kx_branch_predictor_saturation_counter
  #(
    parameter OPTION_OPERAND_WIDTH = 32
    )
   (
    input clk,
    input rst,

    // Signals belonging to the stage where the branch is predicted.
    output predicted_flag_o,     //result of predictor

    input execute_op_bf_i,       // prev insn was bf
    input execute_op_bnf_i,      // prev insn was bnf
    input op_bf_i,               // cur insn is bf
    input op_bnf_i,              // cur insn is bnf
    input padv_decode_i,         // pipeline is moved
    input flag_i,                // prev predicated flag

    // Signals belonging to the stage where the branch is resolved.
    input prev_op_brcond_i,      // prev op was cond brn
    input branch_mispredict_i    // prev brn was mispredicted
    );

   localparam [1:0]
      STATE_STRONGLY_NOT_TAKEN = 2'b00,
      STATE_WEAKLY_NOT_TAKEN   = 2'b01,
      STATE_WEAKLY_TAKEN       = 2'b10,
      STATE_STRONGLY_TAKEN     = 2'b11;

   reg [1:0] state = STATE_WEAKLY_TAKEN;

   assign predicted_flag_o = (state[1] && op_bf_i) || (!state[1] && op_bnf_i);
   wire brn_taken = (execute_op_bf_i && flag_i) || (execute_op_bnf_i && !flag_i);
 
   always @(posedge clk) begin
      if (rst) begin
         // set default state to STATE_WEAKLY_TAKEN
         state <= STATE_WEAKLY_TAKEN;
      end else begin
         // if previous insn was cond brn and pipe is not stalled
         if (prev_op_brcond_i && padv_decode_i) begin
            // if brn was not taken
            if (!brn_taken) begin
               // change fsm state:
               //   STATE_STRONGLY_TAKEN -> STATE_WEAKLY_TAKEN
               //   STATE_WEAKLY_TAKEN -> STATE_WEAKLY_NOT_TAKEN
               //   STATE_WEAKLY_NOT_TAKEN -> STATE_STRONGLY_NOT_TAKEN
               //   STATE_STRONGLY_NOT_TAKEN -> STATE_STRONGLY_NOT_TAKEN
               state <= (state == STATE_STRONGLY_TAKEN) ? STATE_WEAKLY_TAKEN :
                        (state == STATE_WEAKLY_TAKEN)   ? STATE_WEAKLY_NOT_TAKEN
                                                        : STATE_STRONGLY_NOT_TAKEN;
            // if brn was taken
            end else begin
               // change fsm state:
               //   STATE_STRONGLY_NOT_TAKEN -> STATE_WEAKLY_NOT_TAKEN
               //   STATE_WEAKLY_NOT_TAKEN -> STATE_WEAKLY_TAKEN
               //   STATE_WEAKLY_TAKEN -> STATE_STRONGLY_TAKEN
               //   STATE_STRONGLY_TAKEN -> STATE_STRONGLY_TAKEN
               state <= (state == STATE_STRONGLY_NOT_TAKEN) ? STATE_WEAKLY_NOT_TAKEN :
                        (state == STATE_WEAKLY_NOT_TAKEN)   ? STATE_WEAKLY_TAKEN
                                                            : STATE_STRONGLY_TAKEN;
            end
         end
      end
   end
endmodule
