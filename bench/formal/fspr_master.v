`include "mor1kx-defines.v"

module fspr_master
  #(
    parameter OPTION_OPERAND_WIDTH = 32
    )
   (
    input                            clk,
    input                            rst,
    // SPR interface
    input [15:0] 		      spr_bus_addr_o,
    input 			      spr_bus_we_o,
    input 			      spr_bus_stb_o,
    input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_dc_i,
    input 			      spr_bus_ack_dc_i,
    input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_ic_i,
    input 			      spr_bus_ack_ic_i,
    input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_dmmu_i,
    input 			      spr_bus_ack_dmmu_i,
    input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_immu_i,
    input 			      spr_bus_ack_immu_i,
    input                            ctrl_mfspr_ack_o,
    input                            ctrl_mtspr_ack_o,
    input                            ctrl_op_mfspr_o,
    input                            ctrl_op_mtspr_o
    );

`ifdef FORMAL

    reg f_past_valid = 0;

    initial f_past_valid = 0;

    always @(posedge clk)
       f_past_valid <= 1'b1;

    always @(*)
       if (!f_past_valid)
          assume (rst);

    initial assume (rst);

    //For any spr write, strobe should go high
    always @(posedge clk)
       if (f_past_valid && !$past(rst) && spr_bus_we_o)
          assert (spr_bus_stb_o);

    //Spr acknowledgement should be seen only if there is spr strobe
    //Fail
    /*always @(posedge clk)
       if (f_past_valid && f_past_valid && ($rose(ctrl_mfspr_ack_o)
           || $rose(ctrl_mtspr_ack_o)))
          assert (ctrl_op_mfspr_o | ctrl_op_mtspr_o);*/

    //Checking onehot spr acks for immu, dmmu, dc and ic
    always @(posedge clk)
       if (f_past_valid && !$past(rst) && $stable(spr_bus_addr_o)
           && $past(spr_bus_stb_o) && !$past(spr_bus_stb_o,2)
           && $past(rst,2))
          assert ($onehot0({spr_bus_ack_ic_i, spr_bus_ack_dc_i,
                  spr_bus_ack_immu_i, spr_bus_ack_dmmu_i}));

    //Without spr strobe, spr bus data remains unchanged.
    always @(posedge clk) begin
       if (f_past_valid && !$past(rst) && !$past(spr_bus_stb_o)
           && !spr_bus_stb_o && !rst && !$past(spr_bus_stb_o,2)
           && !$past(rst,2)) begin
          assert ($stable(spr_bus_dat_dmmu_i));
          assert ($stable(spr_bus_dat_immu_i));
       end
    end

    // Using f_valid_spr_addr to identify spr addresses
    // of icache, dacache, immu and dmmu. 
    wire f_valid_spr_addr = 0;

    // Records spr acks of ic, dc, immu and dmmu
    wire f_spr_bus_ack_o = 0;

    assign f_valid_spr_addr = (spr_bus_addr_o == `OR1K_SPR_ICBIR_ADDR |
                               spr_bus_addr_o == `OR1K_SPR_DCBFR_ADDR |
                               spr_bus_addr_o[15:11] == 5'd1 |
                               spr_bus_addr_o[15:11] == 5'd2);

    assign f_spr_bus_ack_o = spr_bus_ack_ic_i | spr_bus_ack_dc_i |
                             spr_bus_ack_immu_i | spr_bus_ack_dmmu_i;

    //Initially, reset is assumed so expecting no spr ack
    initial assert (!f_spr_bus_ack_o);

    reg [5:0] f_nreqs;
    initial f_nreqs = 0;

    //---Incoming spr signals tracking---
    //1. When strobe does 0 -> 1 transition
    //2. Back to back spr instructions may keep strobe high
    //   in the consecutive clock cycles. To count such requests
    //   track spr address change
    always @(posedge clk)
       if (rst)
          f_nreqs <= 0;
       else if (($rose(spr_bus_stb_o) || (spr_bus_stb_o &
                $changed(spr_bus_addr_o))) & f_valid_spr_addr)
          f_nreqs <= f_nreqs + 1;

    reg [5:0] f_nacks;
    initial f_nacks = 0;

    //---Counting spr_acks---
    //1. When any spr_ack signals rose
    //2. Back to back spr signals acknowlegement.
    always @(posedge clk)
       if (rst)
          f_nacks <= 0;
       else if (($rose(f_spr_bus_ack_o) || (f_spr_bus_ack_o &
                $changed(spr_bus_addr_o) & spr_bus_stb_o)) &
                f_valid_spr_addr)
          f_nacks <= f_nacks + 1;

    //f_outstanding holds number of pending spr requests waiting
    //for acknowledgement. 
    wire [5:0] f_outstanding;
    assign f_outstanding = f_nreqs-f_nacks;

    //Maximum delay for any spr acknowledgement.
    localparam F_MAX_ACK_DELAY = 2;

    //To count clock interval between spr req and spr ack.
    reg [3:0] f_ackwait_count;
    initial f_ackwait_count = 0;

    //For valid spr address and spr request, acknowledgement shouldn't
    //take more than F_MAX_ACK_DELAY clock cycles.
    generate if (F_MAX_ACK_DELAY > 0)
    begin: ACKWAIT
          always @(posedge clk)
             if (f_past_valid && !spr_bus_stb_o && f_outstanding
                 && f_valid_spr_addr)
                f_ackwait_count <= f_ackwait_count + 1;
             else
                f_ackwait_count <= 0;
          always @*
             if (!rst && !spr_bus_stb_o && f_outstanding > 0)
                assert (f_ackwait_count < F_MAX_ACK_DELAY);
    end endgenerate
    
    //Without mtspr/mfspr instructions, spr strobe can't go high
    always @(posedge clk)
       if (f_past_valid && !$past(rst) && spr_bus_stb_o)
          assert (ctrl_op_mfspr_o | ctrl_op_mtspr_o);

    //If any spr request is outstanding, there shouldn't be any
    // changes to spr we signal, strobe and address. Also,
    // write data should not change.
    always @(posedge clk)
       if (f_past_valid && f_outstanding > 0 && f_valid_spr_addr) begin
          assert (spr_bus_we_o == $past(spr_bus_we_o));
          assert (spr_bus_stb_o);
          assert ($stable(spr_bus_addr_o));
          if (spr_bus_we_o) begin
             assert ($stable(spr_bus_dat_immu_i));
             assert ($stable(spr_bus_dat_dmmu_i));
             assert ($stable(spr_bus_dat_ic_i));
             assert ($stable(spr_bus_dat_dc_i));
          end
       end
`endif

endmodule
