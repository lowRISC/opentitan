// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface i2c_if (
  input clk_i,
  input rst_ni
);

  // standard i2c interface pins
  logic scl_i;
  logic scl_o;
  logic sda_i;
  logic sda_o;

  // task: wait for bus free
  task automatic wait_for_idle();
    //@wait(rst_ni == 1'b1);
  endtask

  // clocking modules
  clocking drv_cb @(posedge clk_i);
    //default input #1step output #1;
    input   rst_ni;
    input   sda_i;
    input   scl_i;

    output  sda_o;
    output  scl_o;
  endclocking: drv_cb
  modport drv_cb_mp(clocking drv_cb);

  // monitor modules
  clocking mon_cb @(negedge clk_i);
    //default input #1step output #1;
    input   sda_i;
    input   scl_i;

    output  sda_o;
    output  scl_o;
  endclocking: mon_cb
  modport mon_cb_mp(clocking mon_cb);

endinterface : i2c_if
