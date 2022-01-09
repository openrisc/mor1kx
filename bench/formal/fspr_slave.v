/* ****************************************************************************
  SPDX-License-Identifier: CERN-OHL-W-2.0
  ***************************************************************************** */

module fspr_slave
#(
  parameter OPTION_OPERAND_WIDTH = 32,
  parameter SLAVE = "IMMU"
  )
  (
   input                            clk,
   input                            rst,
   // SPR interface
   input                     [15:0] spr_bus_addr_i,
   input                            spr_bus_we_i,
   input                            spr_bus_stb_i,
   input [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_i,
   input [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_o,
   input                            spr_bus_ack_o,
   input                            f_past_valid
  );

`define SPR_ASSUME assume
`define SPR_ASSERT assert

   initial `SPR_ASSUME(!spr_bus_stb_i);
   reg [4:0] f_nreqs;
   reg [4:0] f_nacks;

   //Limit check for 20 requests.
   always @(*)
      `SPR_ASSUME((f_nreqs < 20) & (f_nacks < 20));

   wire f_spr_valid;
   assign f_spr_valid = ((spr_bus_addr_i[11:15] == 5'd1) & (SLAVE == "DMMU")) |
                        ((spr_bus_addr_i[11:15] == 5'd2) & (SLAVE == "IMMU")) |
                        ((spr_bus_addr_i ==`OR1K_SPR_ICBIR_ADDR)
                          & (SLAVE == "ICACHE")) |
                        ((spr_bus_addr_i == `OR1K_SPR_DCBIR_ADDR |
                         spr_bus_addr_i == `OR1K_SPR_DCBFR_ADDR )
                          & (SLAVE == "DCACHE"));

   always @(posedge clk)
      if (rst)
         f_nreqs <= 0;
      else if (f_past_valid & ($rose(spr_bus_stb_i) |
              (spr_bus_stb_i & !spr_bus_ack_o)) & f_spr_valid)
         f_nreqs <= f_nreqs + 1;

   always @(posedge clk)
      if (rst)
         f_nacks <= 0;
      else if (f_past_valid & $rose(spr_bus_ack_o) & f_spr_valid)
         f_nacks <= f_nacks + 1;

   //Kept check simple by not testing back to back mtspr/mfspr signals
   always @*
      if (f_past_valid)
         `SPR_ASSERT (f_nacks <= f_nreqs);

   //No ack without request
   always @(posedge clk)
      if (f_past_valid && !$past(rst) && !$past(spr_bus_stb_i)
          && !$past(spr_bus_stb_i,2))
         `SPR_ASSERT (!spr_bus_ack_o);

endmodule
