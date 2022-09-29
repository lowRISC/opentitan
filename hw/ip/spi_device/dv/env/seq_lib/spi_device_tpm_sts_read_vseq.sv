// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TPM Locality test, making transactions of various locality
// Targeting HW sts register, randomizing it and checking data returned to host
class spi_device_tpm_sts_read_vseq extends spi_device_tpm_base_vseq;
  `uvm_object_utils(spi_device_tpm_sts_read_vseq)
  `uvm_object_new

  virtual task body();
    bit [23:0] tpm_addr;
    bit [7:0] returned_bytes[$];
    uint locality_idx;

    spi_device_init();

    // randomised tpm configuration.
    tpm_init();
    tpm_configure_locality();
    repeat (num_trans) begin
      `DV_CHECK_RANDOMIZE_FATAL(ral.tpm_access_0)
      `DV_CHECK_RANDOMIZE_FATAL(ral.tpm_access_1)
      `DV_CHECK_RANDOMIZE_FATAL(ral.tpm_sts)
      csr_update(.csr(ral.tpm_access_0));
      csr_update(.csr(ral.tpm_access_1));
      csr_update(.csr(ral.tpm_sts));
      cfg.clk_rst_vif.wait_clks(100);
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(locality_idx, locality_idx < MAX_TPM_LOCALITY;)

      tpm_addr = get_tpm_addr(locality_idx, TPM_STS_OFFSET);

      spi_host_xfer_tpm_item(.write(0), .tpm_size(4), .addr(tpm_addr),
                              .payload_q(returned_bytes));
      if (cfg.get_locality_active(locality_idx) == 1) begin
        `DV_CHECK_CASE_EQ({returned_bytes[3], returned_bytes[2], returned_bytes[1],
                          returned_bytes[0]}, `gmv(ral.tpm_sts))
      end else begin
        `DV_CHECK_CASE_EQ({returned_bytes[3], returned_bytes[2], returned_bytes[1],
                          returned_bytes[0]}, 32'hFFFFFFFF)
      end
    end
  endtask : body

endclass : spi_device_tpm_sts_read_vseq
