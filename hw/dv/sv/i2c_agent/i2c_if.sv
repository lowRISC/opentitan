// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

import i2c_agent_pkg::*;

interface i2c_if;
  logic clk_i;
  logic rst_ni;
  // standard i2c interface pins
  logic scl_i;
  logic scl_o;
  logic sda_i;
  logic sda_o;

  // debug signal
  bus_status_e bus_status;
  int num_rd_trans;
  int num_wr_trans;

  clocking drv_rx_cb @(posedge clk_i);
    input rst_ni;
    input sda_i;
    input scl_i;
  endclocking: drv_rx_cb
  modport drv_rx_mp(clocking drv_rx_cb);

  clocking drv_tx_cb @(posedge clk_i);
    output sda_o;
    output scl_o;
  endclocking: drv_tx_cb
  modport drv_tx_mp(clocking drv_tx_cb);

  clocking mon_rx_cb @(negedge clk_i);
    input rst_ni;
    input sda_i;
    input scl_i;
  endclocking: mon_rx_cb
  modport mon_rx_mp(clocking mon_rx_cb);

  clocking mon_tx_cb @(negedge clk_i);
    output sda_o;
    output scl_o;
  endclocking: mon_tx_cb
  modport mon_tx_mp(clocking mon_tx_cb);

  //---------------------------------
  // common tasks
  //---------------------------------
  task automatic wait_for_idle();
    wait(rst_ni == 1'b1);
    wait(scl_i == 1'b1);
    wait(scl_i == 1'b1 && sda_i == 1'b1);
    // much less than standard value (4.7us) defined by i2c spec and less than timeout
    #1us;
    wait(scl_i == 1'b1 && sda_i == 1'b1);
    #10ps;
  endtask : wait_for_idle

  task automatic wait_for_dly(int dly);
    repeat (dly) @(posedge clk_i);
  endtask : wait_for_dly

  task automatic wait_for_start_from_host(int thd_sta);
    wait(scl_i == 1'b1 && sda_i == 1'b1);
    wait(sda_i == 1'b0);
    wait_for_dly(thd_sta);
    wait(scl_i == 1'b0);
    bus_status = HostSendStart;
  endtask: wait_for_start_from_host

  task automatic wait_for_repstart_from_host(int tsu_sta);
    wait(scl_i == 1'b0 && sda_i == 1'b1);
    wait(scl_i == 1'b1);
    wait_for_dly(tsu_sta);
    wait(sda_i == 1'b1);
    bus_status = HostSendRestart;
  endtask: wait_for_repstart_from_host

  task automatic wait_for_start_repstart_from_host(int thd_sta, int tsu_sta);
    fork
      begin : isolation_fork_start_or_restart
        fork
          begin
            wait_for_start_from_host(thd_sta);
          end
          begin
            wait_for_repstart_from_host(tsu_sta);
          end
        join_any
        disable fork;
      end : isolation_fork_start_or_restart
    join
  endtask : wait_for_start_repstart_from_host

  task automatic wait_for_stop_from_host(int tsu_sto);
    wait(scl_i == 1'b0 && scl_i == 1'b0)
    wait(scl_i == 1'b1);
    wait_for_dly(tsu_sto);
    wait(scl_i == 1'b1);
    bus_status = HostSendStop;
  endtask: wait_for_stop_from_host

  task automatic wait_for_stop_or_restart_from_host(int tsu_sta, int tsu_sto);
    fork
      begin : isolation_fork_stop_or_restart
        fork
          begin
            wait_for_stop_from_host(tsu_sto);
          end
          begin
            wait_for_repstart_from_host(tsu_sta);
          end
        join_any
        disable fork;
      end : isolation_fork_stop_or_restart
    join
  endtask: wait_for_stop_or_restart_from_host

  task automatic wait_for_bus_free(int delay_ns);
    wait(scl_o == 1'b1 && sda_o == 1'b1)
    #(delay_ns * 1ns) bus_status = BusFree;
  endtask : wait_for_bus_free

  task automatic wait_for_ack_from_host(int tvd_ack);
    wait(scl_i == 1'b0 && scl_i == 1'b1)
    wait_for_dly(tvd_ack);
    wait(scl_i == 1'b0);
    bus_status = HostSendAck;
  endtask: wait_for_ack_from_host

  task automatic wait_for_nack_from_host(int tvd_ack);
    wait(scl_i == 1'b0 && scl_i == 1'b1)
    wait_for_dly(tvd_ack);
    wait(scl_i == 1'b0);
    bus_status = HostSendNoAck;
  endtask: wait_for_nack_from_host

  task automatic wait_for_ack_by_device(int tvd_ack);
    wait(scl_o == 1'b0 && sda_o == 1'b1)
    wait_for_dly(tvd_ack);
    wait(sda_o == 1'b0);
    bus_status = TargetSendAck;
  endtask: wait_for_ack_by_device

  task automatic send_ack_by_device(int tvd_ack);
    scl_o = 1'b0;
    sda_o = 1'b1;
    wait_for_dly(tvd_ack);
    sda_o = 1'b0;
    bus_status = TargetSendAck;
  endtask: send_ack_by_device

endinterface : i2c_if
