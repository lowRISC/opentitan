// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Covergroup for I2C interrupts with interrupt enable and interrupt test
covergroup i2c_interrupts_cg with function sample(
  bit [14:0] intr_state,
  bit [14:0] intr_enable,
  bit [14:0] intr_test
  );
  option.per_instance = 1;
  // host mode interrupt: raised when the FMT FIFO depth is less than the low threshold.
  cp_fmt_threshold : coverpoint intr_state[0] iff (intr_enable[0]);
  // host mode interrupt: raised if the RX FIFO is greater than the high threshold.
  cp_rx_threshold : coverpoint intr_state[1] iff (intr_enable[1]);
  // host mode interrupt: raised if the FMT FIFO has overflowed.
  cp_fmt_overflow : coverpoint intr_state[2] iff (intr_enable[2]);
  // host mode interrupt: raised if the RX FIFO has overflowed.
  cp_rx_overflow : coverpoint intr_state[3] iff (intr_enable[3]);
  // host mode interrupt: raised if there is no ACK in response to an address or data write
  cp_nak : coverpoint intr_state[4] iff (intr_enable[4]);
  // host mode interrupt: raised if the SCL line drops early (not supported without clock synchronization).
  cp_scl_interference : coverpoint intr_state[5] iff (intr_enable[5]);
  // host mode interrupt: raised if the SDA line goes low when host is trying to assert high
  cp_sda_interference : coverpoint intr_state[6] iff (intr_enable[6]);
  // host mode interrupt: raised if target stretches the clock beyond the allowed timeout period
  cp_stretch_timeout : coverpoint intr_state[7] iff (intr_enable[7]);
  // host mode interrupt: raised if the target does not assert a constant value of SDA during transmission.
  cp_sda_unstable : coverpoint intr_state[8] iff (intr_enable[8]);
  // host and target mode interrupt. In host mode, raised if the host issues a repated START or terminates the transaction by issuing STOP
  cp_cmd_complete : coverpoint intr_state[9] iff (intr_enable[9]);
  // target mode interrupt: raised if the target is stretching clocks for a read command. This is a level status interrupt.
  cp_tx_stretch : coverpoint intr_state[10] iff (intr_enable[10]);
  // target mode interrupt: raised if TX FIFO has overflowed.
  cp_tx_overflow : coverpoint intr_state[11] iff (intr_enable[11]);
  // target mode interrupt: raised if ACQ FIFO becomes full. This is a level status interrupt.
  cp_acq_full : coverpoint intr_state[12] iff (intr_enable[12]);
  // target mode interrupt: raised if STOP is received without a preceding NACK during an external host read.
  cp_unexp_stop : coverpoint intr_state[13] iff (intr_enable[13]);
  // target mode interrupt: raised if the host stops sending the clock during an ongoing transaction.
  cp_host_timeout : coverpoint intr_state[14] iff (intr_enable[14]);

  cp_fmt_threshold_test : coverpoint intr_state[0] iff (intr_test[0]){ ignore_bins dis = {0}; }
  cp_rx_threshold_test : coverpoint intr_state[1] iff (intr_test[1]){ ignore_bins dis = {0}; }
  cp_fmt_overflow_test : coverpoint intr_state[2] iff (intr_test[2]){ ignore_bins dis = {0}; }
  cp_rx_overflow_test : coverpoint intr_state[3] iff (intr_test[3]){ ignore_bins dis = {0}; }
  cp_nak_test : coverpoint intr_state[4] iff (intr_test[4]){ ignore_bins dis = {0}; }
  cp_scl_interference_test : coverpoint intr_state[5] iff (intr_test[5]){ ignore_bins dis = {0}; }
  cp_sda_interference_test : coverpoint intr_state[6] iff (intr_test[6]){ ignore_bins dis = {0}; }
  cp_stretch_timeout_test : coverpoint intr_state[7] iff (intr_test[7]){ ignore_bins dis = {0}; }
  cp_sda_unstable_test : coverpoint intr_state[8] iff (intr_test[8]){ ignore_bins dis = {0}; }
  cp_cmd_complete_test : coverpoint intr_state[9] iff (intr_test[9]){ ignore_bins dis = {0}; }
  cp_tx_stretch_test : coverpoint intr_state[10] iff (intr_test[10]){ ignore_bins dis = {0}; }
  cp_tx_overflow_test : coverpoint intr_state[11] iff (intr_test[11]){ ignore_bins dis = {0}; }
  cp_acq_full_test : coverpoint intr_state[12] iff (intr_test[12]){ ignore_bins dis = {0}; }
  cp_unexp_stop_test : coverpoint intr_state[13] iff (intr_test[13]){ ignore_bins dis = {0}; }
  cp_host_timeout_test : coverpoint intr_state[14] iff (intr_test[14]){ ignore_bins dis = {0}; }
endgroup

covergroup i2c_fifo_reset_cg with function sample(
  bit fmtrst,
  bit rxrst,
  bit acqrst,
  bit txrst,
  bit fmt_threshold,
  bit rx_threshold,
  bit fmt_overflow,
  bit rx_overflow,
  bit acq_overflow,
  bit tx_overflow
);
  cp_fmtrst : coverpoint fmtrst;
  cp_rxrst : coverpoint rxrst;
  cp_acqrst : coverpoint acqrst;
  cp_txrst : coverpoint txrst;
  cp_fmt_threshold : coverpoint fmt_threshold;
  cp_rx_threshold : coverpoint rx_threshold;
  cp_fmt_overflow : coverpoint fmt_overflow;
  cp_rx_overflow : coverpoint rx_overflow;
  cp_acq_overflow : coverpoint acq_overflow;
  cp_tx_overflow : coverpoint tx_overflow;
  cp_fmt_threshold_cross : cross cp_fmt_threshold, cp_fmtrst;
  cp_rx_threshold_cross : cross cp_rx_threshold, cp_rxrst;
  cp_fmt_overflow_cross : cross cp_fmt_overflow, cp_fmtrst;
  cp_rx_overflow_cross : cross cp_rx_overflow, cp_rxrst;
  cp_acq_overflow_cross : cross cp_acq_overflow, cp_acqrst;
  cp_tx_overflow_cross : cross cp_tx_overflow, cp_txrst;
endgroup

covergroup i2c_fifo_level_cg (uint fifo_depth)
  with function sample(int fifolvl, bit irq, bit rst);

  option.per_instance = 1;
  cp_rst: coverpoint rst;
  cp_irq: coverpoint irq;
  cp_fifolvl: coverpoint fifolvl {
    bins lvl[] = {1, 4, 8, 16};
    bins others = {[0:fifo_depth]} with (!(item inside {1, 4, 8, 16}));
  }
  cp_fifo_threshold_cross : cross cp_fifolvl, cp_irq{
    ignore_bins reserved_values = binsof(cp_fifolvl.others);
  }
endgroup : i2c_fifo_level_cg

covergroup i2c_operating_mode_cg with function sample(
  bit ip_mode,
  bit tb_mode,
  int scl_frequency
);
  cp_ip_mode : coverpoint ip_mode{
    bins host = {1'b1};
    bins target = {1'b0};
  }
  cp_tb_mode : coverpoint tb_mode{
    bins host = {1'b1};
    bins target = {1'b0};
  }
  cp_mode_cross : cross ip_mode, tb_mode {
    ignore_bins both_host = binsof(ip_mode) intersect {1} && binsof(tb_mode) intersect {1};
    ignore_bins both_target = binsof(ip_mode) intersect {0} && binsof(tb_mode) intersect {0};
    bins ip_host_tb_target = binsof(ip_mode) intersect {1} && binsof(tb_mode) intersect {0};
    bins ip_target_tb_host = binsof(ip_mode) intersect {0} && binsof(tb_mode) intersect {1};
  }
  cp_scl_frequency : coverpoint scl_frequency{
    bins standard_mode[2] = {100, [0:99]};
    bins fast_mode[2] = {400, [101:399]};
    bins fast_plus_mode[2] = {1000, [401:999]};
  }
  cp_ip_mode_x_frequency: cross cp_ip_mode, cp_scl_frequency;

endgroup

class i2c_env_cov extends cip_base_env_cov #(.CFG_T(i2c_env_cfg));
  `uvm_component_utils(i2c_env_cov)

  i2c_fifo_level_cg fmt_fifo_level_cg;
  i2c_fifo_level_cg rx_fifo_level_cg;
  i2c_interrupts_cg interrupts_cg;
  i2c_fifo_reset_cg fifo_reset_cg;
  i2c_operating_mode_cg openting_mode_cg;

  function new(string name, uvm_component parent);
    super.new(name, parent);

    fmt_fifo_level_cg = new(I2C_FMT_FIFO_DEPTH);
    rx_fifo_level_cg  = new(I2C_RX_FIFO_DEPTH);
    interrupts_cg = new();
    fifo_reset_cg = new();
    openting_mode_cg = new();

  endfunction : new

endclass : i2c_env_cov
