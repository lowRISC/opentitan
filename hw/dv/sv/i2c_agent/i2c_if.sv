// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface i2c_if;

  logic clk_i;
  logic rst_ni;

  // standard i2c interface pins
  logic scl_i;
  logic scl_o;
  logic sda_i;
  logic sda_o;

  // debug signal
  logic [255:0]  rw_dir;
  logic [255:0]  status;
  int            num_rd_trans;
  int            num_wr_trans;

  // task: wait for bus free
  task automatic wait_for_idle();
    wait(rst_ni == 1'b1);
    @(posedge scl_i);
    wait(scl_i === 1'b1 && sda_i === 1'b1);
    // much less than standard value (4.7us) defined by i2c spec
    // but avoid timeout
    #1us;
    wait(scl_i === 1'b1 && sda_i === 1'b1);
    #10ps;
  endtask : wait_for_idle

  // clocking modules
  clocking drv_rx_cb @(posedge clk_i);
    //default input #1step output #1;
    input   rst_ni;
    input   sda_i;
    input   scl_i;
  endclocking: drv_rx_cb
  modport drv_rx_mp(clocking drv_rx_cb);

  clocking drv_tx_cb @(posedge clk_i);
    //default input #1step output #1;
    output  sda_o;
    output  scl_o;
  endclocking: drv_tx_cb
  modport drv_tx_mp(clocking drv_tx_cb);

  // monitor modules
  clocking mon_rx_cb @(negedge clk_i);
    //default input #1step output #1;
    input   rst_ni;
    input   sda_i;
    input   scl_i;
  endclocking: mon_rx_cb
  modport mon_rx_mp(clocking mon_rx_cb);

  clocking mon_tx_cb @(negedge clk_i);
    //default input #1step output #1;
    output  sda_o;
    output  scl_o;
  endclocking: mon_tx_cb
  modport mon_tx_mp(clocking mon_tx_cb);

endinterface : i2c_if
