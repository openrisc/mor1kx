/* ****************************************************************************
  SPDX-License-Identifier: CERN-OHL-W-2.0
  ***************************************************************************** */

 module fspr_master
#(
  parameter OPTION_OPERAND_WIDTH = 32
  )
  (
   input                            clk,
   input                            rst,
   // SPR interface
   input                     [15:0] spr_bus_addr_o,
   input                            spr_bus_we_o,
   input                            spr_bus_stb_o,
   input [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_o,
   input                            spr_bus_ack_ic_i,
   input                            spr_bus_ack_dc_i,
   input                            spr_bus_ack_dmmu_i,
   input                            spr_bus_ack_immu_i,
   input                            f_past_valid
  );

`define SPR_ASSUME assert
`define SPR_ASSERT assume

   initial `SPR_ASSUME(rst);
   initial `SPR_ASSUME(!spr_bus_stb_o);
   reg [4:0] f_nreqs;
   reg [4:0] f_nacks;

   wire f_spr_ack;
   assign f_spr_ack = spr_bus_ack_dmmu_i | spr_bus_ack_ic_i |
                      spr_bus_ack_dc_i | spr_bus_ack_immu_i;

   //SPR group is identified by last 5 bits of spr address.
   //Group 1 - Data MMU
   //Group 2 - Instruction MMU
   //Group 3 - Data Cache
   //Group 4 - Instruction Cache
   wire f_spr_valid;
   assign f_spr_valid = (spr_bus_addr_o[11:15] == 5'd1) |
                        (spr_bus_addr_o[11:15] == 5'd2) |
                        (spr_bus_addr_o == `OR1K_SPR_ICBIR_ADDR) |
                        (spr_bus_addr_o == `OR1K_SPR_DCBIR_ADDR |
                         spr_bus_addr_o == `OR1K_SPR_DCBFR_ADDR);


   //Limit check for 20 requests.
   always @(*)
      `SPR_ASSERT((f_nreqs < 20) & (f_nacks < 20));

   always @(posedge clk)
      if (rst)
         f_nreqs <= 0;
      else if (f_past_valid & ($rose(spr_bus_stb_o) |
              (spr_bus_stb_o & !f_spr_ack)) & f_spr_valid)
         f_nreqs <= f_nreqs + 1;

   always @(posedge clk)
      if (rst)
         f_nacks <= 0;
      else if (f_past_valid & $rose(f_spr_ack) & f_spr_valid)
         f_nacks <= f_nacks + 1;

   always @*
      if (f_past_valid)
      `SPR_ASSUME(f_nacks <= f_nreqs);

   //Issue 137: one-hot SPR acks fail
   /*always @(posedge clk)
      if (f_past_valid)
         `SPR_ASSUME ($onehot0({spr_bus_ack_dc_i, spr_bus_ack_ic_i,
                 spr_bus_ack_dmmu_i, spr_bus_ack_immu_i}));*/

   //While waiting for ack, strobe, we and addr should be stable.
   always @(posedge clk)
      if (f_past_valid & !f_spr_ack & $past(spr_bus_stb_o) &
          !$past(spr_bus_stb_o,2) & !$past(f_spr_ack) &
          $past(f_spr_valid) & spr_bus_stb_o & f_spr_valid) begin
         `SPR_ASSUME($stable(spr_bus_addr_o));
         `SPR_ASSUME($stable(spr_bus_we_o));
      end

endmodule
