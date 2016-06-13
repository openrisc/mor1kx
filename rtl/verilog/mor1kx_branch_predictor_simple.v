/******************************************************************************
 This Source Code Form is subject to the terms of the
 Open Hardware Description License, v. 1.0. If a copy
 of the OHDL was not distributed with this file, You
 can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

 Description: Simple branch predictor implementation
 We assume flag to be "true" if instruction is bf and it jumps backwords
 or if instruction is bnf and it jumps forward.

 Copyright (C) 2013 Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>

 ******************************************************************************/

`include "mor1kx-defines.v"

module mor1kx_branch_predictor_simple
   (
    // Signals belonging to the stage where the branch is predicted.
    input op_bf_i,               // branch if flag
    input op_bnf_i,              // branch if not flag
    input [9:0] immjbr_upper_i,  // branch offset
    output predicted_flag_o      //result of predictor
    );
   
   // Static branch prediction - backward branches are predicted as taken,
   // forward branches as not taken.
   assign predicted_flag_o = op_bf_i & immjbr_upper_i[9] |
                             op_bnf_i & !immjbr_upper_i[9];

endmodule
