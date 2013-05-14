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

module mor1kx_branch_prediction
  #(
    parameter OPTION_OPERAND_WIDTH = 32
    )
   (
    input 	clk,
    input 	rst,

    // Signals belonging to the stage where the branch is predicted.
    input 	op_bf_i,
    input 	op_bnf_i,
    input [9:0] immjbr_upper_i,
    output 	predicted_flag_o,

    // Signals belonging to the stage where the branch is resolved.
    input 	prev_op_brcond_i,
    input 	prev_predicted_flag_i,
    input 	flag_i,

    // Branch misprediction indicator
    output 	branch_mispredict_o
    );

   // Compare the real flag with the previously predicted flag and signal a
   // misprediction in case of a mismatch.
   assign branch_mispredict_o = prev_op_brcond_i &
				(flag_i != prev_predicted_flag_i);

   // Static branch prediction - backward branches are predicted as taken,
   // forward branches as not taken.
   assign predicted_flag_o = op_bf_i & immjbr_upper_i[9] |
			     op_bnf_i & !immjbr_upper_i[9];

endmodule
