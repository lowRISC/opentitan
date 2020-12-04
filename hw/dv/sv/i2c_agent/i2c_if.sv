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

  //---------------------------------
  // common tasks
  //---------------------------------
  task automatic wait_for_dly(int dly);
    repeat (dly) @(posedge clk_i);
  endtask : wait_for_dly

  task automatic wait_for_host_start(ref timing_cfg_t tc);
    forever begin
      @(negedge sda_i);
      wait_for_dly(tc.tHoldStart);
      @(negedge scl_i);
      wait_for_dly(tc.tClockStart);
      break;
    end
  endtask: wait_for_host_start

  task automatic wait_for_host_rstart(ref timing_cfg_t tc,
                                      output bit rstart);
    rstart = 1'b0;
    forever begin
      @(posedge scl_i && sda_i);
      wait_for_dly(tc.tSetupStart);
      @(negedge sda_i);
      if (scl_i) begin
        wait_for_dly(tc.tHoldStart);
        @(negedge scl_i) begin
          rstart = 1'b1;
          break;
        end
      end
    end
  endtask: wait_for_host_rstart

  task automatic wait_for_host_stop(ref timing_cfg_t tc,
                                    output bit stop);
    stop = 1'b0;
    forever begin
      @(posedge scl_i);
      @(posedge sda_i);
      if (scl_i) begin
        stop = 1'b1;
        break;
      end
    end
    wait_for_dly(tc.tHoldStop);
  endtask: wait_for_host_stop

  task automatic wait_for_host_stop_or_rstart(timing_cfg_t tc,
                                              output bit   rstart,
                                              output bit   stop);
    fork
      begin : iso_fork
        fork
          wait_for_host_stop(tc, stop);
          wait_for_host_rstart(tc, rstart);
        join_any
        disable fork;
      end : iso_fork
    join
  endtask: wait_for_host_stop_or_rstart

  task automatic wait_for_host_ack(ref timing_cfg_t tc);
    @(negedge sda_i);
    wait_for_dly(tc.tClockLow + tc.tSetupBit);
    forever begin
      @(posedge scl_i);
      if (!sda_i) begin
        wait_for_dly(tc.tClockPulse);
        break;
      end
    end
    wait_for_dly(tc.tHoldBit);
  endtask: wait_for_host_ack

  task automatic wait_for_host_nack(ref timing_cfg_t tc);
    @(negedge sda_i);
    wait_for_dly(tc.tClockLow + tc.tSetupBit);
    forever begin
      @(posedge scl_i);
      if (sda_i) begin
        wait_for_dly(tc.tClockPulse);
        break;
      end
    end
    wait_for_dly(tc.tHoldBit);
  endtask: wait_for_host_nack

  task automatic wait_for_host_ack_or_nack(timing_cfg_t tc,
                                           output bit   ack,
                                           output bit   nack);
    ack = 1'b0;
    nack = 1'b0;
    fork
      begin : iso_fork
        fork
          begin
            wait_for_host_ack(tc);
            ack = 1'b1;
          end
          begin
            wait_for_host_nack(tc);
            nack = 1'b1;
          end
        join_any
        disable fork;
      end : iso_fork
    join
  endtask: wait_for_host_ack_or_nack

  task automatic wait_for_device_ack(ref timing_cfg_t tc);
    @(negedge sda_o && scl_o);
    wait_for_dly(tc.tSetupBit);
    forever begin
      @(posedge scl_i);
      if (!sda_o) begin
        wait_for_dly(tc.tClockPulse);
        break;
      end
    end
    wait_for_dly(tc.tHoldBit);
  endtask: wait_for_device_ack

  // the `sda_unstable` interrupt is asserted if, when receiving data or ,
  // ack pulse (device_send_ack) the value of the target sda signal does not
  // remain constant over the duration of the scl pulse.
  task automatic device_send_bit(ref timing_cfg_t tc,
                                 input bit bit_i);
    sda_o = 1'b1;
    wait_for_dly(tc.tClockLow);
    sda_o = bit_i;
    wait_for_dly(tc.tSetupBit);
    @(posedge scl_i);
    // flip sda_target2host during the clock pulse of scl_host2target causes sda_unstable irq
    sda_o = ~sda_o;
    wait_for_dly(tc.tSdaUnstable);
    sda_o = ~sda_o;
    wait_for_dly(tc.tClockPulse + tc.tHoldBit - tc.tSdaUnstable);
    // not release/change sda_o until host clock stretch passes
    if (tc.enbTimeOut) wait(!scl_i);
    sda_o = 1'b1;
  endtask: device_send_bit

  task automatic device_send_ack(ref timing_cfg_t tc);
    device_send_bit(tc, 1'b0); // special case
  endtask: device_send_ack

  // when the I2C module is in transmit mode, `scl_interference` interrupt
  // will be asserted if the IP identifies that some other device (host or target) on the bus
  // is forcing scl low and interfering with the transmission.
  task automatic device_stretch_host_clk(ref timing_cfg_t tc);
    if (tc.enbTimeOut && tc.tTimeOut > 0) begin
      wait_for_dly(tc.tClockLow + tc.tSetupBit + tc.tSclInterference - 1);
      scl_o = 1'b0;
      wait_for_dly(tc.tStretchHostClock - tc.tSclInterference + 1);
      scl_o = 1'b1;
    end
  endtask : device_stretch_host_clk

  // when the I2C module is in transmit mode, `sda_interference` interrupt
  // will be asserted if the IP identifies that some other device (host or target) on the bus
  // is forcing sda low and interfering with the transmission.
  task automatic get_bit_data(string src = "host",
                              ref timing_cfg_t tc,
                              output bit bit_o);
    wait_for_dly(tc.tClockLow + tc.tSetupBit);
    @(posedge scl_i);
    if (src == "host") begin // host transmits data (addr/wr_data)
      bit_o = sda_i;
      // force sda_target2host low during the clock pulse of scl_host2target
      sda_o = 1'b0;
      wait_for_dly(tc.tSdaInterference);
      sda_o = 1'b1;
      wait_for_dly(tc.tClockPulse + tc.tHoldBit - tc.tSdaInterference);
    end else begin // target transmits data (rd_data)
      bit_o = sda_o;
      wait_for_dly(tc.tClockPulse + tc.tHoldBit);
    end
  endtask: get_bit_data

endinterface : i2c_if
