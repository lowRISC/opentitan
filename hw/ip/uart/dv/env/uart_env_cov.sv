// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class uart_env_cov extends cip_base_env_cov #(.CFG_T(uart_env_cfg));
  `uvm_component_utils(uart_env_cov)

  covergroup fifo_level_cg with function sample(uart_dir_e dir, int lvl, bit rst);
    cp_dir: coverpoint dir;
    cp_lvl: coverpoint lvl {
      bins all_levels[] = {[0:UART_FIFO_DEPTH]};
    }
    cp_rst: coverpoint rst;
    cross cp_dir, cp_lvl, cp_rst;
  endgroup

  // Cover all combinations of 2 different clocks
  covergroup baud_rate_w_core_clk_cg with function sample(baud_rate_e baud_rate,
                                                          int clk_freq);
    cp_baud_rate: coverpoint baud_rate;
    cp_clk_freq:  coverpoint clk_freq {
      bins freqs[] = {24, 25, 48, 50, 100};
    }
    cross cp_baud_rate, cp_clk_freq {
      ignore_bins unsupported = binsof(cp_baud_rate) intersect {BaudRate1p5Mbps} &&
                                binsof(cp_clk_freq)  intersect {24};
    }
  endgroup

  covergroup tx_watermark_cg with function sample(int watermark_lvl);
    cp_watermark_lvl: coverpoint watermark_lvl {
      bins all_levels[] = {[0:MAX_WATERMARK_LVL-1]};
    }
  endgroup

  covergroup rx_watermark_cg with function sample(int watermark_lvl);
    cp_watermark_lvl: coverpoint watermark_lvl {
      bins all_levels[] = {[0:MAX_WATERMARK_LVL]};
    }
  endgroup

  covergroup rx_break_err_cg with function sample(int break_lvl);
    cp_break_level: coverpoint break_lvl {
      bins all_levels[] = {[0:4]};
    }
  endgroup

  covergroup rx_timeout_cg with function sample(int timeout);
    cp_timeout: coverpoint timeout {
      bins small_timeout = {[0:20]};
      bins medium_timeout = {[20:50]};
      bins large_timeout = {[50:$]};
    }
  endgroup

  covergroup rx_parity_err_cg with function sample(bit parity);
    cp_parity : coverpoint parity;
  endgroup

  covergroup noise_filter_cg with function sample(bit rx_sync, bit rx_sync_q1, bit rx_sync_q2);
    cp_noise_filter : coverpoint {rx_sync, rx_sync_q1, rx_sync_q2};
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    fifo_level_cg = new();
    baud_rate_w_core_clk_cg = new();
    tx_watermark_cg = new();
    rx_watermark_cg = new();
    rx_break_err_cg = new();
    rx_timeout_cg = new();
    rx_parity_err_cg = new();
    noise_filter_cg = new();
  endfunction : new

endclass
