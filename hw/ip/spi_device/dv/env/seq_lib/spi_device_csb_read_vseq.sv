// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Assign both CSB pins with random values and read the CSB CSRs to check the values
class spi_device_csb_read_vseq extends spi_device_base_vseq;
  `uvm_object_utils(spi_device_csb_read_vseq)
  `uvm_object_new
  constraint num_trans_c {
    num_trans inside {[20:40]};
  }
  virtual task body();
    bit exp_fw_flash_csb, exp_tpm_csb;

    // disable interface checker as it checks CSBs is onehot
    cfg.spi_host_agent_cfg.vif.en_chk = 0;

    repeat (num_trans) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(exp_fw_flash_csb)
      `DV_CHECK_STD_RANDOMIZE_FATAL(exp_tpm_csb)

      cfg.spi_host_agent_cfg.vif.csb[FW_FLASH_CSB_ID] = exp_fw_flash_csb;
      cfg.spi_host_agent_cfg.vif.csb[TPM_CSB_ID] = exp_tpm_csb;
      // Need a few cycles to sync the value from spi domain to CSR
      cfg.clk_rst_vif.wait_clks(5);
      csr_rd_check(.ptr(ral.status.csb), .compare_value(exp_fw_flash_csb));
      csr_rd_check(.ptr(ral.status.tpm_csb), .compare_value(exp_tpm_csb));
    end

    // bring CSB back to inactive
    cfg.spi_host_agent_cfg.vif.csb = '1;
    cfg.spi_host_agent_cfg.vif.en_chk = 1;
  endtask : body
endclass : spi_device_csb_read_vseq
