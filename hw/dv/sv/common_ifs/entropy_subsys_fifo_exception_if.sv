// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Interface for capturing overflow/underflow/status events in
// entropy complex (entropy_src, CSRNG, EDN) fifos


interface entropy_subsys_fifo_exception_if#(
  parameter bit IsPackerFifo = 0
)
(
   input logic clk_i,
   input logic rst_ni,

   input logic wready_o,
   input logic wvalid_i,
   input logic rready_i,
   input logic rvalid_o,
   input logic full_o
);

   import entropy_subsys_fifo_exception_pkg::*;

   logic read_err_d, write_err_d, state_err_d;
   logic read_err_q, write_err_q, state_err_q;
   logic read_err_pulse, write_err_pulse, state_err_pulse;
   logic write_forbidden;

   logic [N_FIFO_ERR_TYPES-1:0] error_pulses;
   assign error_pulses[FIFO_READ_ERR]  = read_err_pulse;
   assign error_pulses[FIFO_WRITE_ERR] = write_err_pulse;
   assign error_pulses[FIFO_STATE_ERR] = state_err_pulse;

   // Error conidtions map to the types of events that cause errors in the
   // entropy subsystem IPs
   assign write_forbidden = IsPackerFifo ? !wready_o : full_o;

   assign write_err_d  = wvalid_i && write_forbidden;
   assign read_err_d   = IsPackerFifo ?  1'b0 : (!rvalid_o && rready_i);
   assign state_err_d  = IsPackerFifo ?  1'b0 : (!rvalid_o && full_o);

   always @(posedge clk_i) begin
     state_err_q <= state_err_d;
     read_err_q  <= read_err_d;
     write_err_q <= write_err_d;
   end

   clocking mon_cb @(posedge clk_i);
     input write_forbidden;
     input error_pulses;
   endclocking


   assign write_err_pulse = write_err_d && !write_err_q;
   assign state_err_pulse = state_err_d && !state_err_q;
   assign read_err_pulse = read_err_d && !read_err_q;

endinterface : entropy_subsys_fifo_exception_if
