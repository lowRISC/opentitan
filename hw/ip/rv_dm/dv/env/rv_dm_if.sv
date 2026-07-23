// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface rv_dm_if(input logic clk, input logic rst_n);

  import rv_dm_env_pkg::*;

  // Most of the signals in the interface are designed to be connected to ports of rv_dm. If
  // is_active is true, the signals that will be connected to its input ports are driven by cb. If
  // is_active is false, they are driven with 'z here, which allows the interface to monitor a
  // larger design that drives rv_dm itself.
  //
  // The flag is defined as a wire with a weak pull-up. This ensures that a testbench that doesn't
  // customise is_active will see the interface be driven actively, but allows a testbench that
  // *does* want to customise the signal to pull it low.
  wire is_active;
  assign (weak0, weak1) is_active = 1'b1;

  // The signals connected to ports of rv_dm, other than the TL, alert, RACL and JTAG interfaces.
  // These have the same name as the port, but without an _i or _o suffix.
  wire                  scan_rst_n;
  wire                  ndmreset_req;
  wire                  dmactive;
  wire [NUM_HARTS-1:0]  debug_req;
  wire  [NUM_HARTS-1:0] unavailable;

  // "Internal" versions of the per-port signals above for rv_dm's input ports
  logic                 scan_rst_n_internal;
  logic [NUM_HARTS-1:0] unavailable_internal;

  // Drive the wire signals for rv_dm's input ports if is_active is true
  assign scan_rst_n  = is_active ? scan_rst_n_internal  : 'z;
  assign unavailable = is_active ? unavailable_internal : 'z;

  // A clocking block for driving the various _internal signals that are all synchronous to clk. If
  // is_active is true, these can be used to drive input ports of rv_dm. The signals from output
  // ports of rv_dm can also be sampled through this clocking block.
  clocking cb @(posedge clk);
    input  ndmreset_req;
    input  dmactive;
    input  debug_req;
    output scan_rst_n = scan_rst_n_internal;
    output unavailable = unavailable_internal;
  endclocking

  // A clocking block for a monitor
  clocking mon_cb @(posedge clk);
    input ndmreset_req;
    input dmactive;
    input debug_req;
    input unavailable;
  endclocking

  // Disable TLUL host SBA assertions when injecting intg errors on the response channel.
  bit disable_tlul_assert_host_sba_resp_svas;

endinterface
