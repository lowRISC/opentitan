// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// inherit from spi_device_flash_and_tpm_vseq and override the task to always
// use `min_idle_ns_after_csb_drop`.
class spi_device_flash_and_tpm_min_idle_vseq extends spi_device_flash_and_tpm_vseq;
  `uvm_object_utils(spi_device_flash_and_tpm_min_idle_vseq)
  `uvm_object_new

  virtual task spi_clk_init();
    super.spi_clk_init();
    // always use the min value
    cfg.spi_host_agent_cfg.max_idle_ns_after_csb_drop =
        cfg.spi_host_agent_cfg.min_idle_ns_after_csb_drop;
  endtask
endclass : spi_device_flash_and_tpm_min_idle_vseq
