/* ****************************************************************************
  This source describes Open Hardware and is licensed under the CERN-OHLW v2

  You may redistribute and modify this documentation and make products
  using it under the terms of the CERN-OHL-W v2 (https:/cern.ch/cern-ohl).
  This documentation is distributed WITHOUT ANY EXPRESS OR IMPLIED
  WARRANTY, INCLUDING OF MERCHANTABILITY, SATISFACTORY QUALITY
  AND FITNESS FOR A PARTICULAR PURPOSE. Please see the CERN-OHL-W v2
  for applicable conditions.

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
