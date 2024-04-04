// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//
// Interface: rst_shadowed_if
// An interface to drive rst_shadowed_n pin
// By default, the `rst_shadowed_n` pin is directly connected to `rst_n` pin from the IP.
// This interface provide methods to drive `rst_shadowed_n` pin when `drive_shadow_rst_pin()` task is
// called, and can use `reconnect_shadowed_rst_n_to_rst_n()` to reconnect to `rst_n` pin.
interface rst_shadowed_if (
  input  rst_n,
  output rst_shadowed_n
);

`ifndef VERILATOR
  // include macros and import pkgs
  `include "dv_macros.svh"
  `include "uvm_macros.svh"
  import uvm_pkg::*;
`endif

  bit   drive_shadowed_rst_en;
  logic shadowed_rst_n;

  // If set `drive_shadowed_rst_en` bit to 0, the `rst_shadowed_n` output will be the same as IP
  // level reset pin.
  function automatic void reconnect_shadowed_rst_n_to_rst_n();
    drive_shadowed_rst_en = 0;
  endfunction

  task automatic drive_shadow_rst_pin(logic val);
    shadowed_rst_n = val;
    drive_shadowed_rst_en = 1;
  endtask

  assign rst_shadowed_n = drive_shadowed_rst_en ? shadowed_rst_n : rst_n;

endinterface
