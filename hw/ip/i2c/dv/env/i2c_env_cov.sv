// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

covergroup i2c_fifo_level_cg (uint fifo_depth)
  with function sample(int fmtlvl, int rxlvl, bit irq, bit rst);

  option.per_instance = 1;
  cp_rst: coverpoint rst;
  cp_irq: coverpoint irq;
  cp_fmtlvl: coverpoint fmtlvl {
    bins lvl[] = {1, 4, 8, 16};
    bins others = {[0:fifo_depth]} with (!(item inside {1, 4, 8, 16}));
  }
  cp_rxlvl: coverpoint rxlvl {
    bins lvl[] = {1, 4, 8, 16, 30};
    bins others = {[0:fifo_depth]} with (!(item inside {1, 4, 8, 16, 30}));
  }
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
