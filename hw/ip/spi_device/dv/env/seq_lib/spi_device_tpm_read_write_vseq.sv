// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test is a mix of TPM Read and TPM Write transactions
class spi_device_tpm_read_write_vseq extends spi_device_tpm_base_vseq;
  `uvm_object_utils(spi_device_tpm_read_write_vseq)
  `uvm_object_new

  virtual task body();
    int pay_num;
    bit [7:0] tpm_cmd;

    spi_device_init();

    // randomised tpm configuration.
    tpm_init();
    tpm_configure();

    repeat (num_trans) begin
      pay_num = 0;

      cfg.clk_rst_vif.wait_clks(100);

      // Randomize the tpm_cmd
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(tpm_cmd, tpm_cmd inside {TPM_READ_CMD, TPM_WRITE_CMD};)
      `uvm_info(`gfn, $sformatf("tpm_cmd: %s", tpm_cmd.name), UVM_LOW)

      if(tpm_cmd == TPM_READ_CMD) begin
       tpm_read_trans(tpm_cmd);
      end
      else if (tpm_cmd == TPM_WRITE_CMD) begin
       tpm_write_trans(tpm_cmd);
      end
    end
  endtask : body

endclass : spi_device_tpm_read_write_vseq
