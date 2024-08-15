// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Tests the upper range of clkdiv values [FF+1: FFFF]
class spi_host_upper_range_clkdiv_vseq extends spi_host_speed_vseq;
  `uvm_object_utils(spi_host_upper_range_clkdiv_vseq)
  `uvm_object_new

  // when set causes the constraint to pick the maximum value in the clock divider range
  rand bit max_range_value;

  constraint spi_config_regs_clkdiv_c {
    solve max_range_value before spi_config_regs.clkdiv;
    max_range_value dist { 0 :/ 7, 1 :/ 3};
    // CLKDIV randomised not in the whole range since there's a dedicated VSEQ: seq_name
    // which uses the upper range of clock divider values - this way we won't have super long
    // tests when running this VSEQ
    max_range_value -> (spi_config_regs.clkdiv == cfg.seq_cfg.host_spi_max_clkdiv);
    !max_range_value -> (spi_config_regs.clkdiv inside {[cfg.seq_cfg.host_spi_middle_clkdiv :
                                                         cfg.seq_cfg.host_spi_max_clkdiv]});

    // In order to minimise sim-time the idle/lead/trail delays are all set to 0.
    foreach (spi_config_regs.csnlead[i]) {
      spi_config_regs.csnlead[i] == 0;
    }
    foreach (spi_config_regs.csntrail[i]) {
      spi_config_regs.csntrail[i] == 0;
    }
    foreach (spi_config_regs.csnidle[i]) {
      spi_config_regs.csnidle[i] == 0 ;
    }
  }


  constraint spi_config_regs_faster_clkdiv_c {
    // Only multiples of 16 to quicken up the clock - this constraint should be part of the clkdiv
    spi_config_regs.clkdiv[3:0] == 0;
  }

  constraint num_trans_c {
    // Really low number of TXN generated to avoid lenghty simulation time
    // since we already have a very slow SPI clock
    num_trans inside {[1 : 2]};
  }

  // This VSEQ is the only one which allows large clock divider values and due to that the
  // VSEQ allow the internal FSM counter to be decremented by 16-units.
  // The VIF flag is enabled only whilst this VSEQ is run
  virtual task pre_start();
    super.pre_start();
    cfg.force_spi_fsm_vif.fast_mode = 1;
  endtask

  virtual task post_start();
    super.post_start();
    cfg.force_spi_fsm_vif.fast_mode = 0;
  endtask

  function void pre_randomize();
    super.pre_randomize();
    // Redefining the ranges to ensure 'num_cmd_bytes' gets randomised to a
    // lower value to ensure simulations finish sooner
    cfg.seq_cfg.host_spi_min_len = 1;
    cfg.seq_cfg.host_spi_max_len = 2;
  endfunction

endclass : spi_host_upper_range_clkdiv_vseq
