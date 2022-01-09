/* ****************************************************************************
  SPDX-License-Identifier: CERN-OHL-W-2.0

  Description: mor1kx formal multiclock alu operation checker

  Checks that an operation f_op_i finishes within a number of clock
  cycles.  The completion of the operation is signaled by asserting
  f_op_valid_i.  This is used to validate multi operation ALU operations
  like multiply, divide and shift.

  Copyright (C) 2021 Stafford Horne <shorne@gmail.com>

***************************************************************************** */

module f_multiclock_op
#(
  parameter STABLE_WIDTH = 32,
  parameter OP_MAX_CLOCKS = 32
 )
 (
  input clk,
  input f_op_i,
  input f_op_valid_i,
  input decode_valid_i,
  input [STABLE_WIDTH-1:0] f_stable_i,
  input f_past_valid
);

   reg [5:0] f_op_count;
   reg f_op;
   initial f_op_count = 0;
   initial f_op = 0;

   //Valid multiplication output is seen after 32 clocks
   always @(posedge clk) begin
      if (f_past_valid) begin
	  // If we have slow operations decode_valid will
	  // go low to stall after the operation starts.
	  if (f_op | f_op_valid_i)
	     assume (!decode_valid_i);
	  else
	     assume (decode_valid_i);

	  // Start counting when we see the operation start
	  if ($rose(f_op_i)) begin
	     f_op <= 1;
	     f_op_count <= 1;
	  end else if (f_op_valid_i) // Stop when the op is done
	     f_op <= 0;

	  if (f_op) begin
	     f_op_count <= f_op_count + 1;
	     assume (f_op_i);
	     assume ($stable(f_stable_i));
	  end

	  // Ensure the operation completes never going beyond max count
	  assert (f_op_count <= (OP_MAX_CLOCKS + 1));
      end
   end
endmodule

