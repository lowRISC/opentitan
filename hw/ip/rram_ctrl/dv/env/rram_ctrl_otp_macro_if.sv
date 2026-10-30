// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface to the DUT's otp_ctrl macro port, which otp_ctrl uses to store OTP data in the RRAM.
// The port lives in the OTP clock domain.
interface rram_ctrl_otp_macro_if(
  input logic clk,
  input logic rst_n
);
  // Packages defining the types of the DUT signals below
  import otp_ctrl_macro_pkg::*;

  otp_ctrl_macro_req_t req;
  otp_ctrl_macro_rsp_t rsp;

  // The request is idle from time zero, so that the DUT never sees unknown values.
  initial req = '{valid: 1'b0, cmd: Init, default: '0};

  // Used to drive requests and sample responses without racing the DUT's own posedge-triggered
  // updates.
  clocking cb @(posedge clk);
    output req;
    input  rsp;
  endclocking

  // Sends `cmd` and waits for its response.
  //
  // The request is held stable until the DUT has accepted it (valid and ready sampled on the same
  // edge), as required by the DUT's request FIFO.
  // The DUT returns exactly one response per request, flagged by a single-cycle rvalid.
  // The request is driven right after a clock edge. If it were driven between edges instead, the
  // first wait for the edge would return in the same time step, and deasserting valid there would
  // override the request before the DUT ever saw it.
  task automatic send(input  cmd_e            cmd,
                      input  otp_macro_addr_t addr,
                      input  otp_macro_size_t size,
                      input  otp_macro_data_t wdata,
                      output otp_macro_data_t rdata,
                      output err_e            err);
    @(cb);
    cb.req <= '{valid: 1'b1, cmd: cmd, addr: addr, size: size, wdata: wdata};
    do @(cb); while (!cb.rsp.ready);
    cb.req <= '{valid: 1'b0, cmd: Init, default: '0};
    do @(cb); while (!cb.rsp.rvalid);
    rdata = cb.rsp.rdata;
    err   = cb.rsp.err;
  endtask

endinterface : rram_ctrl_otp_macro_if
