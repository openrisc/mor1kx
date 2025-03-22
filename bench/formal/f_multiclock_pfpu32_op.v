/* ****************************************************************************
  SPDX-License-Identifier: CERN-OHL-W-2.0

  Description: mor1kx formal multiclock pfpu32 operation checker

  Checks that an pfpu32 operation finishes within a number of clock cycles.
  The completion of the operation is signaled by asserting result_rdy_i.

***************************************************************************** */

module f_multiclock_pfpu32_op
#(
  parameter OP_MAX_CLOCKS = 3
) (
  input clk,
  input flush_i,
  input adv_i,
  input result_rdy_i,
  input start_i,
  input f_initialized,
);

  reg [5:0] f_op_count;
  reg f_op;
  initial f_op_count = 0;
  initial f_op = 0;

  // Valid output is seen after OP_MAX_CLOCKS cycles.
  always @(posedge clk) begin
    if (f_initialized) begin
      if (flush_i)
        // The pipeline is being flushed. The results of any operations in
        // flight will not be reported. Stop counting.
        f_op <= 0;
      else if (adv_i & start_i) begin
        // A new operation is starting. Start/reset the counter.
        f_op <= 1;
        f_op_count <= 1;
      end else if (result_rdy_i)
        // Result is ready. Stop counting.
        f_op <= 0;
      else if (f_op) begin
        // Operation is continuing to run. Continue counting.
        f_op_count <= f_op_count + 1;
        assume (adv_i);
      end

      // Ensure the operation cycle count never goes beyond max count.
      assert (f_op_count <= OP_MAX_CLOCKS);
    end
  end
endmodule
