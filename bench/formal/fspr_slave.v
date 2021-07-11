`include "mor1kx-defines.v"

module fspr_slave
  #(
    parameter OPTION_OPERAND_WIDTH = 32
    )
   (
    input                            clk,
    input                            rst,
    // SPR interface
    input [15:0] 		      spr_bus_addr_i,
    input 			      spr_bus_we_i,
    input 			      spr_bus_stb_i,
    input [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_i,
    input [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_o,
    input 			      spr_bus_ack_o
    );

`ifdef FORMAL

    reg f_past_valid = 0;
    initial f_past_valid = 0;
    always @(posedge clk)
       f_past_valid <= 1'b1;
    always @(*)
       if (!f_past_valid)
          assert (rst);

    initial assume (rst);

//~~~~~~~~~~~~~~~~Assumption wrt SPR MASTER~~~~~~~~~~~~~~~~~

    //For every strobe assume unique address
    always @(posedge clk)
       if (!$past(rst) && f_past_valid && $rose(spr_bus_stb_i))
          assume ($changed(spr_bus_addr_i));

    //SPR read/write signals should be stable if stb is
    //continuously high for two clock cycles.
    always @(posedge clk)
       if (f_past_valid && !$past(rst) && $past(spr_bus_stb_i)
           && spr_bus_stb_i)
          assume (spr_bus_we_i == $past(spr_bus_we_i));

//~~~~~~~~~~~~~~~~~~SPR slave Assertions~~~~~~~~~~~~~~~~~~~~

    //For any spr read request cache shouldn't acknowledge.
    //This property is true only for icache and dcache as
    //they don't allow spr read.
    always @(posedge clk)
       if (f_past_valid && !$past(rst) && ($past(spr_bus_addr_i) ==
           `OR1K_SPR_DCBFR_ADDR | $past(spr_bus_addr_i) ==
           `OR1K_SPR_ICBIR_ADDR) && $stable(spr_bus_addr_i) &&
           !$past(spr_bus_we_i) && $past(spr_bus_stb_i) &&
           !$past(spr_bus_stb_i,2))
          assert (!spr_bus_ack_o);

    wire f_valid_spr_addr = 0;
    assign f_valid_spr_addr = (spr_bus_addr_i == `OR1K_SPR_ICBIR_ADDR ||
                               spr_bus_addr_i == `OR1K_SPR_DCBFR_ADDR ||
                               spr_bus_addr_i[15:11] == 5'd1 ||
                               spr_bus_addr_i[15:11] == 5'd2);

    reg [5:0] f_nreqs;
    initial f_nreqs = 0;

    //Incoming spr signals tracking
    //1. When strobe does 0 -> 1 transition
    //2. Back to back spr instructions may keep strobe high in
    //   the consecutive clock cycles. To count such requests
    //   track spr address change
    always @(posedge clk)
       if (rst)
          f_nreqs <= 0;
       else if (($rose(spr_bus_stb_i) || (spr_bus_stb_i &
                $changed(spr_bus_addr_i))) & f_valid_spr_addr)
          f_nreqs <= f_nreqs + 1;

    reg [5:0] f_nacks;
    initial f_nacks = 0;

    //---Counting spr_acks---
    //1. When any spr_ack signals rose
    //2. Back to back spr signals acknowlegement.
    always @(posedge clk)
       if (rst)
          f_nacks <= 0;
       else if (($rose(spr_bus_ack_o) || (spr_bus_ack_o &
                $changed(spr_bus_addr_i) & spr_bus_stb_i))
                & f_valid_spr_addr)
          f_nacks <= f_nacks + 1;

    wire [5:0] f_outstanding;
    assign f_outstanding = f_nreqs-f_nacks;

    localparam F_MAX_ACK_DELAY = 1;

    reg [3:0] f_ackwait_count;
    initial f_ackwait_count = 0;

    generate if (F_MAX_ACK_DELAY > 0)
    begin: ACKWAIT
          always @(posedge clk)
             if (f_past_valid && !spr_bus_stb_i &&
                 f_outstanding && f_valid_spr_addr)
                f_ackwait_count <= f_ackwait_count + 1;
             else
                f_ackwait_count <= 0;
          always @*
             if (!rst && !spr_bus_stb_i && f_outstanding > 0)
                assert (f_ackwait_count < F_MAX_ACK_DELAY);
    end endgenerate

    //No ack without request
    always @(posedge clk)
       if (f_past_valid && !$past(rst) && !$past(spr_bus_stb_i)
           && !$past(spr_bus_stb_i,2))
          assert (!spr_bus_ack_o);

    //Spr ack is high only if strobe arrives either in the past
    //two clock cycles or in the present clock cycle. 
    always @(posedge clk)
       if (f_past_valid && !$past(rst) && spr_bus_ack_o)
          assert (spr_bus_stb_i || $past(spr_bus_stb_i) ||
                   $past(spr_bus_stb_i,2));
`endif
endmodule
