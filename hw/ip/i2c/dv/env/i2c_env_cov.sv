// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

covergroup i2c_fifo_level_cg (uint fifo_depth)
  with function sample(int lvl, bit irq, bit rst);

  option.per_instance = 1;
  cp_rst: coverpoint rst;
  cp_irq: coverpoint irq;
  cp_lvl: coverpoint lvl {bins all_levels[] = {[0:fifo_depth]};}

  cr_fifo_lvl_irq_rst: cross cp_rst, cp_irq, cp_lvl;
endgroup : i2c_fifo_level_cg

class i2c_env_cov extends cip_base_env_cov #(.CFG_T(i2c_env_cfg));
  `uvm_component_utils(i2c_env_cov)

  i2c_fifo_level_cg fmt_fifo_level_cg;
  i2c_fifo_level_cg rx_fifo_level_cg;

  function new(string name, uvm_component parent);
    super.new(name, parent);

    fmt_fifo_level_cg = new(I2C_FMT_FIFO_DEPTH);
    rx_fifo_level_cg  = new(I2C_RX_FIFO_DEPTH);
  endfunction : new

endclass : i2c_env_cov
