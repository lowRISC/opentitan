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
                                                          clk_freq_mhz_e clk_freq);
    cp_baud_rate: coverpoint baud_rate;
    cp_clk_freq:  coverpoint clk_freq;
    cross cp_baud_rate, cp_clk_freq {
      ignore_bins unsupported = binsof(cp_baud_rate) intersect {BaudRate1p5Mbps} &&
                                binsof(cp_clk_freq)  intersect {ClkFreq24Mhz};
    }
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    fifo_level_cg = new();
    baud_rate_w_core_clk_cg = new();
  endfunction : new

endclass
