/* ****************************************************************************
  This Source Code Form is subject to the terms of the
  Open Hardware Description License, v. 1.0. If a copy
  of the OHDL was not distributed with this file, You
  can obtain one at http://juliusbaxter.net/ohdl/ohdl.txt

  Description: Data bus interface for MAROCCHINO pipeline

  Dbus interface request signal out synchronous
  32-bit specific
  Derived from mor1kx_lsu_cappuccino

  Copyright (C) 2012 Julius Baxter <juliusbaxter@gmail.com>
  Copyright (C) 2013 Stefan Kristiansson <stefan.kristiansson@saunalahti.fi>
  Copyright (C) 2015 Andrey Bacherov <avbacherov@opencores.org>

***************************************************************************** */

`include "mor1kx-defines.v"

module mor1kx_lsu_marocchino
#(
  // data cache
  parameter FEATURE_DATACACHE         = "NONE",
  parameter OPTION_OPERAND_WIDTH      = 32,
  parameter OPTION_DCACHE_BLOCK_WIDTH = 5,
  parameter OPTION_DCACHE_SET_WIDTH   = 9,
  parameter OPTION_DCACHE_WAYS        = 2,
  parameter OPTION_DCACHE_LIMIT_WIDTH = 32,
  parameter OPTION_DCACHE_SNOOP       = "NONE",
  // mmu cache
  parameter FEATURE_DMMU               = "NONE",
  parameter FEATURE_DMMU_HW_TLB_RELOAD = "NONE",
  parameter OPTION_DMMU_SET_WIDTH      = 6,
  parameter OPTION_DMMU_WAYS           = 1,
  // store buffer
  parameter FEATURE_STORE_BUFFER            = "ENABLED",
  parameter OPTION_STORE_BUFFER_DEPTH_WIDTH = 8,
  // atomic support
  parameter FEATURE_ATOMIC = "ENABLED"
)
(
  input                             clk,
  input                             rst,

  input                             padv_decode_i,
  input                             exec_new_input_i,

  // Input from execute stage (decode's latches)
  input [OPTION_OPERAND_WIDTH-1:0]  exec_lsu_adr_i, // calculated address from ALU
  input [OPTION_OPERAND_WIDTH-1:0]  exec_rfb_i,  // register file B in (store operand)
  input                             exec_op_lsu_load_i,
  input                             exec_op_lsu_store_i,
  input                             exec_op_lsu_atomic_i,
  input                             exec_op_msync_i,
  input [1:0]                       exec_lsu_length_i,
  input                             exec_lsu_zext_i,

  // From control stage, exception PC for the store buffer input
  input [OPTION_OPERAND_WIDTH-1:0]  ctrl_epcr_i,
  // The exception PC as it has went through the store buffer
  output [OPTION_OPERAND_WIDTH-1:0] store_buffer_epcr_o,

  output [OPTION_OPERAND_WIDTH-1:0] lsu_result_o,
  output [OPTION_OPERAND_WIDTH-1:0] lsu_adr_o,
  output                            lsu_valid_o,
  // exception output
  output                            lsu_except_dbus_o,
  output                            lsu_except_align_o,
  output                            lsu_except_dtlb_miss_o,
  output                            lsu_except_dpagefault_o,
  output                            lsu_excepts_o,

  // Indicator that the dbus exception came via the store buffer
  output reg                        store_buffer_err_o,

  // Atomic operation flag set/clear logic
  output                            atomic_flag_set_o,
  output                            atomic_flag_clear_o,

  // stall signal for msync logic
  output                            msync_done_o,

  // SPR interface
  input [15:0]                      spr_bus_addr_i,
  input                             spr_bus_we_i,
  input                             spr_bus_stb_i,
  input [OPTION_OPERAND_WIDTH-1:0]  spr_bus_dat_i,
  output [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_dc_o,
  output                            spr_bus_ack_dc_o,
  output [OPTION_OPERAND_WIDTH-1:0] spr_bus_dat_dmmu_o,
  output                            spr_bus_ack_dmmu_o,

  input                             dc_enable_i,
  input                             dmmu_enable_i,
  input                             supervisor_mode_i,

  // interface to data bus
  output [OPTION_OPERAND_WIDTH-1:0] dbus_adr_o,
  output reg                        dbus_req_o,
  output [OPTION_OPERAND_WIDTH-1:0] dbus_dat_o,
  output reg [3:0]                  dbus_bsel_o,
  output                            dbus_we_o,
  output                            dbus_burst_o,
  input                             dbus_err_i,
  input                             dbus_ack_i,
  input [OPTION_OPERAND_WIDTH-1:0]  dbus_dat_i,
  input                             pipeline_flush_i,

  input [31:0]                      snoop_adr_i,
  input                             snoop_en_i
);

  reg [2:0] state;

  reg                               dbus_ack;
  reg                               dbus_err;
  reg [OPTION_OPERAND_WIDTH-1:0]    dbus_dat;
  reg [OPTION_OPERAND_WIDTH-1:0]    dbus_adr;
  wire [OPTION_OPERAND_WIDTH-1:0]   next_dbus_adr;
  reg                               dbus_we;
  wire                              dbus_access;
  wire                              dbus_stall;

  wire [OPTION_OPERAND_WIDTH-1:0]   lsu_ldat;
  wire [OPTION_OPERAND_WIDTH-1:0]   lsu_sdat;
  wire                              lsu_ack;

  wire                              dc_err;
  wire                              dc_ack;
  wire [31:0]                       dc_ldat;
  wire [31:0]                       dc_sdat;
  wire [31:0]                       dc_adr;
  wire [31:0]                       dc_adr_match;
  wire                              dc_req;
  wire                              dc_we;
  wire [3:0]                        dc_bsel;

  wire                              dc_access;
  wire                              dc_refill_allowed;
  wire                              dc_refill;
  wire                              dc_refill_req;
  wire                              dc_refill_done;

  reg                               dc_enable_r;
  wire                              dc_enabled;

  // DMMU
  wire                              tlb_miss;
  wire                              dmmu_pagefault;
  wire [OPTION_OPERAND_WIDTH-1:0]   dmmu_phys_addr;
  wire                              dmmu_cache_inhibit;

  wire                              tlb_reload_req;
  wire                              tlb_reload_busy;
  wire [OPTION_OPERAND_WIDTH-1:0]   tlb_reload_addr;
  wire                              tlb_reload_pagefault;
  reg                               tlb_reload_ack;
  reg [OPTION_OPERAND_WIDTH-1:0]    tlb_reload_data;
  wire                              tlb_reload_pagefault_clear;
  reg                               tlb_reload_done;

  // Store buffer
  wire                              store_buffer_write;
  wire                              store_buffer_read;
  wire                              store_buffer_full;
  wire                              store_buffer_empty;
  wire [OPTION_OPERAND_WIDTH-1:0]   store_buffer_radr;
  wire [OPTION_OPERAND_WIDTH-1:0]   store_buffer_wadr;
  wire [OPTION_OPERAND_WIDTH-1:0]   store_buffer_dat;
  wire [OPTION_OPERAND_WIDTH/8-1:0] store_buffer_bsel;
  wire                              store_buffer_atomic;
  reg                               store_buffer_write_pending;

  reg                               dbus_atomic;

  reg                               last_write;
  reg                               write_done;

  // Atomic operations
  reg [OPTION_OPERAND_WIDTH-1:0]    atomic_addr;
  reg                               atomic_reserve;
  wire                              swa_success;

  wire                              snoop_valid;
  wire                              dc_snoop_hit;

  wire                              except_align;
  wire                              except_dbus_err;
  wire                              except_dtlb_miss;
  wire                              except_dpagefault;

  // combined exception flag
  wire lsu_excepts = except_dbus_err  | except_align |
                     except_dtlb_miss | except_dpagefault;

  // it makes sense to take new LSU command
  wire exec_new_input_en = exec_new_input_i &
                           (~pipeline_flush_i) & (~except_align);
  wire exec_op_lsu_x = exec_op_lsu_store_i | exec_op_lsu_load_i;
  // signal to take new LSU command (less priority than flushing)
  wire take_op_lsu_x = exec_new_input_en & exec_op_lsu_x;

  // local latches of inputs from execute stage
  reg                             cmd_op_lsu_load;
  reg                             cmd_op_lsu_store;
  reg                             cmd_op_lsu_atomic;
  reg                             cmd_op_lsu_x;
  reg [1:0]                       cmd_lsu_length;
  reg                             cmd_lsu_zext;
  reg [OPTION_OPERAND_WIDTH-1:0]  cmd_lsu_adr; // calculated address from ALU
  reg [OPTION_OPERAND_WIDTH-1:0]  cmd_rfb;  // register file B in (store operand)
  // lsu local latched commands
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      cmd_op_lsu_load   <= 1'b0;
      cmd_op_lsu_store  <= 1'b0;
      cmd_op_lsu_atomic <= 1'b0;
      cmd_op_lsu_x      <= 1'b0;
    end
    else if (padv_decode_i | pipeline_flush_i) begin
      cmd_op_lsu_load   <= 1'b0;
      cmd_op_lsu_store  <= 1'b0;
      cmd_op_lsu_atomic <= 1'b0;
      cmd_op_lsu_x      <= 1'b0;
    end
    else if (take_op_lsu_x) begin
      cmd_op_lsu_load   <= exec_op_lsu_load_i;
      cmd_op_lsu_store  <= exec_op_lsu_store_i;
      cmd_op_lsu_atomic <= exec_op_lsu_atomic_i;
      cmd_op_lsu_x      <= exec_op_lsu_x;
    end
  end // @clock

  // lsu local latched additional parameters
  always @(posedge clk) begin
    if (take_op_lsu_x) begin
      cmd_lsu_length <= exec_lsu_length_i;
      cmd_lsu_zext   <= exec_lsu_zext_i;
      cmd_lsu_adr    <= exec_lsu_adr_i;
      cmd_rfb        <= exec_rfb_i;
    end
  end // @clock

  // output latched address for exceptions processing
  assign lsu_adr_o = cmd_lsu_adr;

  // lsu new command 1-clock mask
  reg cmd_new;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      cmd_new <= 1'b0;
    else
      cmd_new <= take_op_lsu_x;
  end // @clock

  // l.msync to generate msync-stall
  reg cmd_op_msync;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      cmd_op_msync <= 1'b0;
    else if (padv_decode_i | pipeline_flush_i)
      cmd_op_msync <= 1'b0;
    else if (exec_new_input_i)
      cmd_op_msync <= exec_op_msync_i;
  end // @clock

  // LSU exceptions for output
  reg except_dbus_err_r,  except_dbus_align_r,
      except_dtlb_miss_r, except_dpagefault_r;
  // latching
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      except_dbus_err_r   <= 1'b0;
      except_dbus_align_r <= 1'b0;
      except_dtlb_miss_r  <= 1'b0;
      except_dpagefault_r <= 1'b0;
    end
    else if (padv_decode_i | pipeline_flush_i) begin
      except_dbus_err_r   <= 1'b0;
      except_dbus_align_r <= 1'b0;
      except_dtlb_miss_r  <= 1'b0;
      except_dpagefault_r <= 1'b0;
    end
    else if (exec_op_lsu_x) begin
      if (except_dbus_err)
        except_dbus_err_r   <= 1'b1;
      if (except_align)
        except_dbus_align_r <= 1'b1;
      if (except_dtlb_miss)
        except_dtlb_miss_r  <= 1'b1;
      if (except_dpagefault)
        except_dpagefault_r <= 1'b1;
    end
  end // @clock
  // output assignement
  assign lsu_except_dbus_o       = except_dbus_err_r;
  assign lsu_except_align_o      = except_dbus_align_r;
  assign lsu_except_dtlb_miss_o  = except_dtlb_miss_r;
  assign lsu_except_dpagefault_o = except_dpagefault_r;
  assign lsu_excepts_o           = except_dbus_err_r  | except_dbus_align_r |
                                   except_dtlb_miss_r | except_dpagefault_r;


  //----------------------//
  // Exceptions detection //
  //----------------------//

  // --- align ---
  wire align_err_word  = |exec_lsu_adr_i[1:0];
  wire align_err_short = exec_lsu_adr_i[0];

  assign except_align = exec_op_lsu_x &
                        (((exec_lsu_length_i == 2'b10) & align_err_word) |
                         ((exec_lsu_length_i == 2'b01) & align_err_short));


  // --- any bus error ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      dbus_err <= 1'b0;
    else if (padv_decode_i | pipeline_flush_i)
      dbus_err <= 1'b0;
    else if (dbus_err_i)
      dbus_err <= 1'b1;
  end // @ clock
  // --- write bus error ---
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      store_buffer_err_o <= 1'b0;
    else if (pipeline_flush_i)
      store_buffer_err_o <= 1'b0;
    else if (dbus_err_i & dbus_we_o)
      store_buffer_err_o <= 1'b1;
  end // @ clock
  // --- combined bus errors ---
  assign except_dbus_err = dbus_err | store_buffer_err_o;

  // --- D-TLB miss ---
  assign except_dtlb_miss =
    cmd_op_lsu_x & dmmu_enable_i & tlb_miss & (~tlb_reload_busy);

  // --- Page fault ---
  assign except_dpagefault =
    tlb_reload_pagefault |
    (cmd_op_lsu_x & dmmu_enable_i & dmmu_pagefault & (~tlb_reload_busy));


  //------------//
  // LSU output //
  //------------//

  // Big endian bus mapping
  reg [3:0] dbus_bsel;
  always @(*)
    case (cmd_lsu_length)
      2'b00: // byte access
        case(cmd_lsu_adr[1:0])
          2'b00: dbus_bsel = 4'b1000;
          2'b01: dbus_bsel = 4'b0100;
          2'b10: dbus_bsel = 4'b0010;
          2'b11: dbus_bsel = 4'b0001;
        endcase
      2'b01: // halfword access
        case(cmd_lsu_adr[1])
          1'b0: dbus_bsel = 4'b1100;
          1'b1: dbus_bsel = 4'b0011;
        endcase
      2'b10,
      2'b11: dbus_bsel = 4'b1111;
    endcase

  // Select part of bus for load
  reg [OPTION_OPERAND_WIDTH-1:0] dbus_dat_aligned;
  always @(*)
    case(cmd_lsu_adr[1:0])
      2'b00: dbus_dat_aligned = lsu_ldat;
      2'b01: dbus_dat_aligned = {lsu_ldat[23:0],8'd0};
      2'b10: dbus_dat_aligned = {lsu_ldat[15:0],16'd0};
      2'b11: dbus_dat_aligned = {lsu_ldat[7:0],24'd0};
    endcase

  // Do appropriate extension for load
  reg [OPTION_OPERAND_WIDTH-1:0] dbus_dat_extended;
  always @(*)
    case({cmd_lsu_zext, cmd_lsu_length})
      3'b100:  dbus_dat_extended = {24'd0,dbus_dat_aligned[31:24]}; // lbz
      3'b101:  dbus_dat_extended = {16'd0,dbus_dat_aligned[31:16]}; // lhz
      3'b000:  dbus_dat_extended = {{24{dbus_dat_aligned[31]}},
                                    dbus_dat_aligned[31:24]}; // lbs
      3'b001:  dbus_dat_extended = {{16{dbus_dat_aligned[31]}},
                                    dbus_dat_aligned[31:16]}; // lhs
      default: dbus_dat_extended = dbus_dat_aligned;
    endcase

  // ready flag
  reg access_done;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      access_done <= 1'b0;
    else if (padv_decode_i) // clear only by pipeline advancing
      access_done <= 1'b0;
    else if (lsu_ack)
      access_done <= 1'b1;
  end // @ clock

  // data from load
  reg [OPTION_OPERAND_WIDTH-1:0] lsu_result_r;
  always @(posedge clk) begin
    if (cmd_op_lsu_load & lsu_ack & (~lsu_excepts) & (~access_done)) // latch result
      lsu_result_r <= dbus_dat_extended;
  end // @ clock

  // output assignement
  assign lsu_valid_o  = access_done & (~tlb_reload_busy) & (~dc_snoop_hit);
  assign lsu_result_o = lsu_result_r;


  // Data bus mapping for store
  assign lsu_sdat =
    (cmd_lsu_length == 2'b00) ? {cmd_rfb[7:0],cmd_rfb[7:0],cmd_rfb[7:0],cmd_rfb[7:0]} : // byte access
    (cmd_lsu_length == 2'b01) ? {cmd_rfb[15:0],cmd_rfb[15:0]} : // halfword access
                                cmd_rfb; // word access


  // Bus access logic
  localparam [2:0]
    IDLE        = 3'd0,
    READ        = 3'd1,
    WRITE       = 3'd2,
    TLB_RELOAD  = 3'd3,
    DC_REFILL   = 3'd4;

  // Stall until the store buffer is empty
  assign msync_done_o = cmd_op_msync & (state == IDLE);

  wire store_buffer_ack = (FEATURE_STORE_BUFFER != "NONE") ?
                           store_buffer_write : write_done;

  assign dbus_access = (state == WRITE) |
                       ((state != DC_REFILL) &
                        (cmd_op_lsu_store | tlb_reload_busy | (~dc_access)));

  assign lsu_ack = lsu_excepts ? 1'b0 :
                   (cmd_op_lsu_store | (state == WRITE)) ?
                    ((store_buffer_ack & (~cmd_op_lsu_atomic)) |
                     (write_done       &   cmd_op_lsu_atomic)) :
                    (dbus_access ? dbus_ack : dc_ack);

  assign lsu_ldat = dbus_access ? dbus_dat : dc_ldat;



  assign dbus_adr_o   = dbus_adr;
  assign dbus_dat_o   = dbus_dat;
  assign dbus_burst_o = (state == DC_REFILL) & (~dc_refill_done);

  assign dbus_stall = tlb_reload_busy | lsu_excepts | pipeline_flush_i;

  //
  // Slightly subtle, but if there is an atomic store coming out from the
  // store buffer, and the link has been broken while it was waiting there,
  // the bus access is still performed as a (discarded) read.
  //
  assign dbus_we_o = dbus_we & ((~dbus_atomic) | atomic_reserve);

  assign next_dbus_adr = (OPTION_DCACHE_BLOCK_WIDTH == 5) ?
                         {dbus_adr[31:5], dbus_adr[4:0] + 5'd4} : // 32 byte
                         {dbus_adr[31:4], dbus_adr[3:0] + 4'd4};  // 16 byte


  // state machine
  always @(posedge clk) begin
    // init
    dbus_ack        <= 1'b0;
    write_done      <= 1'b0;
    tlb_reload_ack  <= 1'b0;
    tlb_reload_done <= 1'b0;
    // process
    case (state)
      IDLE: begin
        dbus_req_o  <= 1'b0;
        dbus_we     <= 1'b0;
        dbus_adr    <= 0;
        dbus_bsel_o <= 4'hf;
        dbus_atomic <= 1'b0;
        last_write  <= 1'b0;
        if (store_buffer_write |
            ((~store_buffer_empty) & (~dbus_stall))) begin
          state <= WRITE;
        end
        else if (cmd_op_lsu_x & //(~pipeline_flush_i) &
                 (~dc_refill) &
                 dbus_access & (~access_done) & (~dbus_ack) & (~dbus_err)) begin
          if (tlb_reload_req) begin
            dbus_req_o <= 1'b1;
            dbus_adr   <= tlb_reload_addr;
            state      <= TLB_RELOAD;
          end
          else if (dmmu_enable_i) begin
            dbus_adr <= dmmu_phys_addr;
            if ((~tlb_miss) & (~dmmu_pagefault) & (~except_align)) begin
              if (cmd_op_lsu_load) begin
                dbus_req_o  <= 1'b1;
                dbus_bsel_o <= dbus_bsel;
                state       <= READ;
              end
            end
          end
          else if (~except_align) begin // D-MMU disabled or none
            dbus_adr <= cmd_lsu_adr;
            if (cmd_op_lsu_load) begin
              dbus_req_o  <= 1'b1;
              dbus_bsel_o <= dbus_bsel;
              state       <= READ;
            end
          end
        end
        else if (dc_refill_req) begin
          dbus_req_o <= 1'b1;
          dbus_adr   <= dc_adr_match;
          state      <= DC_REFILL;
        end
      end // idle

      DC_REFILL: begin
        dbus_req_o <= 1'b1;
        if (dbus_ack_i) begin
          dbus_adr <= next_dbus_adr;
          if (dc_refill_done) begin
            dbus_req_o <= 1'b0;
            state      <= IDLE;
          end
        end
        // TODO: only abort on snoop-hits to refill address
        if (dbus_err_i | dc_snoop_hit) begin
          dbus_req_o <= 1'b0;
          state      <= IDLE;
        end
      end // dc-refill

      READ: begin
        dbus_ack <= dbus_ack_i;
        dbus_dat <= dbus_dat_i;
        if (dbus_err_i | dbus_ack_i) begin
          dbus_req_o <= 1'b0;
          state      <= IDLE;
        end
      end // read

      WRITE: begin
        dbus_req_o <= 1'b1;
        dbus_we    <= 1'b1;
        //---
        if ((~dbus_req_o) | (dbus_ack_i & (~last_write))) begin
          dbus_bsel_o <= store_buffer_bsel;
          dbus_adr    <= store_buffer_radr;
          dbus_dat    <= store_buffer_dat;
          dbus_atomic <= store_buffer_atomic;
          last_write  <= store_buffer_empty;
        end
        //---
        if (store_buffer_write)
          last_write <= 1'b0;
        //---
        if (dbus_err_i | (dbus_ack_i & last_write)) begin
          dbus_req_o <= 1'b0;
          dbus_we    <= 1'b0;
          if (dbus_err_i | (~store_buffer_write)) begin
            write_done <= 1'b1;
            state      <= IDLE;
          end
        end
      end // write

      TLB_RELOAD: begin
        dbus_adr        <= tlb_reload_addr;
        tlb_reload_data <= dbus_dat_i;
        tlb_reload_ack  <= dbus_ack_i & tlb_reload_req;
        //---
        if (dbus_err_i | (~tlb_reload_req)) begin
          tlb_reload_done <= 1'b1;
          state           <= IDLE;
        end
        //---
        dbus_req_o <= tlb_reload_req;
        if (dbus_ack_i | tlb_reload_ack)
          dbus_req_o <= 1'b0;
      end // tlb-reload

      default: state <= IDLE;
    endcase

    if (rst) begin
      state       <= IDLE;
      dbus_req_o  <= 1'b0;
      dbus_we     <= 1'b0;
      dbus_atomic <= 1'b0;
      last_write  <= 1'b0;
    end
  end // @ clock state machine


  // We have to mask out our snooped bus accesses
  assign snoop_valid = (OPTION_DCACHE_SNOOP != "NONE") &
                       (snoop_en_i & (~((snoop_adr_i == dbus_adr_o) & dbus_ack_i)));


generate
if (FEATURE_ATOMIC!="NONE") begin : atomic_gen
  // Atomic operations logic

  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      atomic_reserve <= 1'b0;
    else if (pipeline_flush_i)
      atomic_reserve <= 1'b0;
    else if ((cmd_op_lsu_store & cmd_op_lsu_atomic & write_done) |
             ((~cmd_op_lsu_atomic) & store_buffer_write & (store_buffer_wadr == atomic_addr)) |
             (snoop_valid & (snoop_adr_i == atomic_addr)))
      atomic_reserve <= 1'b0;
    else if (cmd_op_lsu_load & cmd_op_lsu_atomic & cmd_new)
      atomic_reserve <= ~(snoop_valid & (snoop_adr_i == dc_adr_match));
  end // @clock

  always @(posedge clk)
    if (cmd_op_lsu_load & cmd_op_lsu_atomic & cmd_new)
      atomic_addr <= dc_adr_match;

  assign swa_success = cmd_op_lsu_store & cmd_op_lsu_atomic &
                       atomic_reserve & (dbus_adr == atomic_addr);

  reg atomic_flag_set;
  reg atomic_flag_clear;

  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst) begin
      atomic_flag_set   <= 1'b0;
      atomic_flag_clear <= 1'b0;
    end
    else if (padv_decode_i | pipeline_flush_i) begin
      atomic_flag_set   <= 1'b0;
      atomic_flag_clear <= 1'b0;
    end
    else if (write_done) begin
      atomic_flag_set   <= swa_success & lsu_valid_o;
      atomic_flag_clear <= (~swa_success) & lsu_valid_o &
                           cmd_op_lsu_atomic & cmd_op_lsu_store;
    end
  end // @clock

  assign atomic_flag_set_o   = atomic_flag_set;
  assign atomic_flag_clear_o = atomic_flag_clear;

end
else begin
  assign atomic_flag_set_o   = 1'b0;
  assign atomic_flag_clear_o = 1'b0;
  assign swa_success         = 1'b0;
  always @(posedge clk) begin
     atomic_addr    <= 0;
     atomic_reserve <= 1'b0;
  end
end
endgenerate



  //--------------------//
  // Store buffer logic //
  //--------------------//
  reg dc_refill_r;
  always @(posedge clk)
    dc_refill_r <= dc_refill;

  always @(posedge clk) begin
    if (rst)
      store_buffer_write_pending <= 1'b0;
    else if (store_buffer_write | pipeline_flush_i)
      store_buffer_write_pending <= 1'b0;
    else if (cmd_op_lsu_store & cmd_new & (~dbus_stall) &
             (store_buffer_full | dc_refill | dc_refill_r | dc_snoop_hit))
      store_buffer_write_pending <= 1'b1;
  end // @ clock

  assign store_buffer_write = ((cmd_op_lsu_store & (cmd_new | tlb_reload_done)) |
                                store_buffer_write_pending) & (~dbus_stall) &
                               (~store_buffer_full) & (~dc_refill) & (~dc_refill_r) & (~dc_snoop_hit);

  assign store_buffer_wadr = dc_adr_match;

generate
if (FEATURE_STORE_BUFFER!="NONE") begin : store_buffer_gen
  assign store_buffer_read = ((state == IDLE) & store_buffer_write) |
                             ((state == IDLE) & (~store_buffer_empty)) |
                             ((state == WRITE) & last_write & store_buffer_write) |
                             ((state == WRITE) & (~last_write) & (store_buffer_write | (~store_buffer_empty)) &
                              (dbus_ack_i | (~dbus_req_o)));

  mor1kx_store_buffer
  #(
    .DEPTH_WIDTH(OPTION_STORE_BUFFER_DEPTH_WIDTH),
    .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH)
  )
  u_store_buffer
  (
    .clk      (clk),
    .rst      (rst),

    .pc_i     (ctrl_epcr_i),
    .adr_i    (store_buffer_wadr),
    .dat_i    (lsu_sdat),
    .bsel_i   (dbus_bsel),
    .atomic_i (cmd_op_lsu_atomic),
    .write_i  (store_buffer_write),

    .pc_o     (store_buffer_epcr_o),
    .adr_o    (store_buffer_radr),
    .dat_o    (store_buffer_dat),
    .bsel_o   (store_buffer_bsel),
    .atomic_o (store_buffer_atomic),
    .read_i   (store_buffer_read),

    .full_o   (store_buffer_full),
    .empty_o  (store_buffer_empty)
  );
end
else begin
  assign store_buffer_epcr_o = ctrl_epcr_i;
  assign store_buffer_radr   = store_buffer_wadr;
  assign store_buffer_dat    = lsu_sdat;
  assign store_buffer_bsel   = dbus_bsel;
  assign store_buffer_empty  = 1'b1;
  assign store_buffer_atomic = cmd_op_lsu_atomic;

  reg store_buffer_full_r;
  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      store_buffer_full_r <= 1'b0;
    else if (store_buffer_write)
      store_buffer_full_r <= 1'b1;
    else if (write_done)
      store_buffer_full_r <= 1'b0;
  end // @ clock

  assign store_buffer_full = store_buffer_full_r & (~write_done);
end
endgenerate

  always @(posedge clk `OR_ASYNC_RST) begin
    if (rst)
      dc_enable_r <= 1'b0;
    else if (dc_enable_i & (~dbus_req_o))
      dc_enable_r <= 1'b1;
    else if ((~dc_enable_i) & (~dc_refill))
      dc_enable_r <= 1'b0;
  end // @ clock

  assign dc_enabled = dc_enable_i & dc_enable_r;


  assign dc_adr = take_op_lsu_x ? exec_lsu_adr_i : cmd_lsu_adr;

  assign dc_adr_match = dmmu_enable_i ?
                      `ifdef SIM_SMPL_SOC
                        dmmu_phys_addr : cmd_lsu_adr;
                      `else
                        {dmmu_phys_addr[OPTION_OPERAND_WIDTH-1:2],2'b0} :
                        {cmd_lsu_adr[OPTION_OPERAND_WIDTH-1:2],2'b0};
                      `endif

  assign dc_req = cmd_op_lsu_x & dc_access & (~access_done) & (~dbus_stall) &
                  (~(dbus_atomic & dbus_we & (~atomic_reserve)));

  assign dc_refill_allowed = (~(cmd_op_lsu_store | (state == WRITE))) &
                             (~dc_snoop_hit) & (~snoop_valid);

generate
if (FEATURE_DATACACHE!="NONE") begin : dcache_gen
  if (OPTION_DCACHE_LIMIT_WIDTH == OPTION_OPERAND_WIDTH) begin
    assign dc_access = cmd_op_lsu_store |
                       (dc_enabled & (~(dmmu_cache_inhibit & dmmu_enable_i)));
  end
  else if (OPTION_DCACHE_LIMIT_WIDTH < OPTION_OPERAND_WIDTH) begin
    assign dc_access = cmd_op_lsu_store |
                       (dc_enabled &
                        (dc_adr_match[OPTION_OPERAND_WIDTH-1:
                                      OPTION_DCACHE_LIMIT_WIDTH] == 0) &
                        (~(dmmu_cache_inhibit & dmmu_enable_i)));
  end
  else begin
    initial begin
      $display("ERROR: OPTION_DCACHE_LIMIT_WIDTH > OPTION_OPERAND_WIDTH");
      $finish();
    end
  end

  assign dc_bsel = dbus_bsel;

  assign dc_we =
    (exec_op_lsu_store_i & (~exec_op_lsu_atomic_i) & exec_new_input_en) |
    (dbus_atomic & dbus_we_o & (~write_done)) |
    (cmd_op_lsu_store & tlb_reload_busy & (~tlb_reload_req));

  mor1kx_dcache
  #(
    .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH),
    .OPTION_DCACHE_BLOCK_WIDTH(OPTION_DCACHE_BLOCK_WIDTH),
    .OPTION_DCACHE_SET_WIDTH(OPTION_DCACHE_SET_WIDTH),
    .OPTION_DCACHE_WAYS(OPTION_DCACHE_WAYS),
    .OPTION_DCACHE_LIMIT_WIDTH(OPTION_DCACHE_LIMIT_WIDTH),
    .OPTION_DCACHE_SNOOP(OPTION_DCACHE_SNOOP)
  )
  u_dcache
  (
    // Outputs
    .refill_o                   (dc_refill),
    .refill_req_o               (dc_refill_req),
    .refill_done_o              (dc_refill_done),
    .cpu_err_o                  (dc_err),
    .cpu_ack_o                  (dc_ack),
    .cpu_dat_o                  (dc_ldat),
    .snoop_hit_o                (dc_snoop_hit),
    .spr_bus_dat_o              (spr_bus_dat_dc_o),
    .spr_bus_ack_o              (spr_bus_ack_dc_o),
    // Inputs
    .clk                        (clk),
    .rst                        (rst),
    .dc_dbus_err_i              (dbus_err),
    .dc_enable_i                (dc_enabled),
    .dc_access_i                (dc_access),
    .cpu_dat_i                  (lsu_sdat),
    .cpu_adr_i                  (dc_adr),
    .cpu_adr_match_i            (dc_adr_match),
    .cpu_req_i                  (dc_req),
    .cpu_we_i                   (dc_we),
    .cpu_bsel_i                 (dc_bsel),
    .refill_allowed             (dc_refill_allowed),
    .wradr_i                    (dbus_adr),
    .wrdat_i                    (dbus_dat_i),
    .we_i                       (dbus_ack_i),
    .snoop_adr_i                (snoop_adr_i[31:0]),
    .snoop_valid_i              (snoop_valid),
    .spr_bus_addr_i             (spr_bus_addr_i[15:0]),
    .spr_bus_we_i               (spr_bus_we_i),
    .spr_bus_stb_i              (spr_bus_stb_i),
    .spr_bus_dat_i              (spr_bus_dat_i[OPTION_OPERAND_WIDTH-1:0])
  );
end
else begin
   assign dc_access = 0;
   assign dc_refill = 0;
   assign dc_refill_done = 0;
   assign dc_refill_req = 0;
   assign dc_err = 0;
   assign dc_ack = 0;
   assign dc_bsel = 0;
   assign dc_we = 0;
   assign dc_snoop_hit = 0;
end
endgenerate

generate
if (FEATURE_DMMU!="NONE") begin : dmmu_gen
  wire  [OPTION_OPERAND_WIDTH-1:0] virt_addr;
  wire                             dmmu_enable;

  assign virt_addr = dc_adr;

  assign tlb_reload_pagefault_clear = ~cmd_op_lsu_x; // use pipeline_flush_i?

  assign dmmu_enable = dmmu_enable_i & (~pipeline_flush_i);

  mor1kx_dmmu
  #(
    .FEATURE_DMMU_HW_TLB_RELOAD(FEATURE_DMMU_HW_TLB_RELOAD),
    .OPTION_OPERAND_WIDTH(OPTION_OPERAND_WIDTH),
    .OPTION_DMMU_SET_WIDTH(OPTION_DMMU_SET_WIDTH),
    .OPTION_DMMU_WAYS(OPTION_DMMU_WAYS)
  )
  u_dmmu
  (
    // Outputs
    .phys_addr_o                      (dmmu_phys_addr),
    .cache_inhibit_o                  (dmmu_cache_inhibit),
    .tlb_miss_o                       (tlb_miss),
    .pagefault_o                      (dmmu_pagefault),
    .tlb_reload_req_o                 (tlb_reload_req),
    .tlb_reload_busy_o                (tlb_reload_busy),
    .tlb_reload_addr_o                (tlb_reload_addr),
    .tlb_reload_pagefault_o           (tlb_reload_pagefault),
    .spr_bus_dat_o                    (spr_bus_dat_dmmu_o),
    .spr_bus_ack_o                    (spr_bus_ack_dmmu_o),
    // Inputs
    .clk                              (clk),
    .rst                              (rst),
    .enable_i                         (dmmu_enable),
    .virt_addr_i                      (virt_addr),
    .virt_addr_match_i                (cmd_lsu_adr),
    .op_store_i                       (cmd_op_lsu_store),
    .op_load_i                        (cmd_op_lsu_load),
    .supervisor_mode_i                (supervisor_mode_i),
    .tlb_reload_ack_i                 (tlb_reload_ack),
    .tlb_reload_data_i                (tlb_reload_data),
    .tlb_reload_pagefault_clear_i     (tlb_reload_pagefault_clear),
    .spr_bus_addr_i                   (spr_bus_addr_i[15:0]),
    .spr_bus_we_i                     (spr_bus_we_i),
    .spr_bus_stb_i                    (spr_bus_stb_i),
    .spr_bus_dat_i                    (spr_bus_dat_i[OPTION_OPERAND_WIDTH-1:0])
  );
end
else begin
   assign dmmu_cache_inhibit = 0;
   assign tlb_miss = 0;
   assign dmmu_pagefault = 0;
   assign tlb_reload_busy = 0;
   assign tlb_reload_req = 0;
   assign tlb_reload_pagefault = 0;
end
endgenerate

endmodule // mor1kx_lsu_marocchino
