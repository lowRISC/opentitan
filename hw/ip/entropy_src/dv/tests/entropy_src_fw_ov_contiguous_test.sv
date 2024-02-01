// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_fw_ov_contiguous_test extends entropy_src_base_test;

  `uvm_component_utils(entropy_src_fw_ov_contiguous_test)
  `uvm_component_new

  function void configure_env();
    super.configure_env();

    cfg.en_scb                              = 1;

    cfg.dut_cfg.route_software_pct          = 50;

    cfg.dut_cfg.ht_threshold_scope_pct      = 50;
    cfg.dut_cfg.default_ht_thresholds_pct   = 100;
    cfg.dut_cfg.fips_enable_pct             = 50;
    cfg.dut_cfg.type_bypass_pct             = 50;

    cfg.dut_cfg.fw_read_pct                 = 100;
    // To read from the observe FIFO, both otp_en_entropy_src_fw_over and
    // FW_OV_CONTROL.FW_OV_MODE need to be enabled.
    cfg.dut_cfg.fw_over_pct                 = 50;

    cfg.dut_cfg.rng_bit_enable_pct          = 80;
    cfg.dut_cfg.fips_enable_pct             = 50;
    cfg.dut_cfg.module_enable_pct           = 100;

    // Set the maximum threshold for the observe FIFO threshold randomization to half of
    // ObserveFifoDepth. This leaves enough leeway to avoid overflows.
    cfg.dut_cfg.max_observe_fifo_threshold = entropy_src_reg_pkg::ObserveFifoDepth/2;

    `DV_CHECK_RANDOMIZE_FATAL(cfg)

    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_LOW)
  endfunction
endclass : entropy_src_fw_ov_contiguous_test
