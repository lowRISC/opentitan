// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// configure TPM to FIFO mode and randomize all other field on the TPM_CFG CSR
// There are 2 threads
// 1. SW randomly programs TPM HW returned registers
// 2. Upstream host randomly reads any of these registers. Scb will checks the data correctness
class spi_device_tpm_read_hw_reg_vseq extends spi_device_tpm_base_vseq;
  `uvm_object_utils(spi_device_tpm_read_hw_reg_vseq)
  `uvm_object_new

  rand tpm_cfg_mode_e tpm_mode;

  rand uint sw_to_update_tpm_reg_cyc_dly;

  constraint sw_to_update_tpm_reg_cyc_dly_c {
    sw_to_update_tpm_reg_cyc_dly dist {
      [1:100]              :/ 1,
      [101:1000]           :/ 1
    };
  }

  // Override this to test more in the extended test
  constraint tpm_addition_for_read_hw_reg_c {
    tpm_mode == TpmFifoMode;
    is_hw_reg_region == 1;
    is_hw_reg_offset == 1;
    tpm_write == 0;

    // TODO
    is_valid_locality == 1;
  }

  virtual task body();
    dv_base_reg tpm_hw_regs[$] = {
        ral.tpm_access_0, ral.tpm_access_1, ral.tpm_sts, ral.tpm_intf_capability,
        ral.tpm_int_enable, ral.tpm_int_status, ral.tpm_int_vector, ral.tpm_did_vid, ral.tpm_rid};
    // randomly update all HW CSRs
    foreach (tpm_hw_regs[j]) begin
      `DV_CHECK_RANDOMIZE_FATAL(tpm_hw_regs[j])
      csr_update(.csr(tpm_hw_regs[j]));
    end
    for (int i = 1; i <= num_trans; i++) begin
      bit upstream_spi_done;
      bit [7:0] returned_bytes[$]; // this is checked in scb
      `uvm_info(`gfn, $sformatf("starting sequence %0d/%0d", i, num_trans), UVM_LOW)
      tpm_init(.mode(tpm_mode), .is_hw_return(1));

      fork
        while (!upstream_spi_done) begin
          int num_regs;
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(sw_to_update_tpm_reg_cyc_dly)
          cfg.clk_rst_vif.wait_clks(sw_to_update_tpm_reg_cyc_dly);

          num_regs = $urandom_range(0, tpm_hw_regs.size / 2);
          tpm_hw_regs.shuffle();
          for (int j = 0; j < num_regs; j++) begin
            `DV_CHECK_RANDOMIZE_FATAL(tpm_hw_regs[j])
            csr_update(.csr(tpm_hw_regs[j]));
          end
          // if SPI has a ongoing transaction, wait until it completes
          // no need to write the TPM HW reg mutliple times during a SPI transaction,
          // as host should read the HW reg to ensure it updates successfully before
          // update it again.
          `DV_WAIT(cfg.spi_host_agent_cfg.vif.csb[TPM_CSB_ID] == 1)
        end
        begin
          repeat ($urandom_range(10, 20)) begin
              randomize_tpm_trans();
              spi_host_xfer_tpm_item(.write(tpm_write), .tpm_size(tpm_size), .addr(tpm_addr),
                                    .payload_q(returned_bytes));
          end
          upstream_spi_done = 1;
        end
      join
    end
  endtask : body

endclass : spi_device_tpm_read_hw_reg_vseq
