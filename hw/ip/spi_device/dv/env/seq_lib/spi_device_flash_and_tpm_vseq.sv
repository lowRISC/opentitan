// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Run both flash_all and tpm_all sequence in parallel to test that spi_device receives
// flash transactions interleaving with TPM transactions
class spi_device_flash_and_tpm_vseq extends spi_device_base_vseq;
  `uvm_object_utils(spi_device_flash_and_tpm_vseq)
  `uvm_object_new

  task body();
    spi_device_flash_all_vseq flash_vseq;
    spi_device_tpm_all_vseq tpm_vseq;

    `uvm_create_on(flash_vseq, p_sequencer)
    `uvm_create_on(tpm_vseq, p_sequencer)

    // this flash_and_tpm_vseq will do dut_init and clear_all_interrupts
    // don't do it in sub-vseq, it could affect the other
    flash_vseq.do_dut_init = 0;
    tpm_vseq.do_dut_init = 0;
    flash_vseq.do_clear_all_interrupts = 0;
    tpm_vseq.do_clear_all_interrupts = 0;

    `DV_CHECK_RANDOMIZE_FATAL(flash_vseq)
    `DV_CHECK_RANDOMIZE_FATAL(tpm_vseq)
    fork
      flash_vseq.start(p_sequencer);
      tpm_vseq.start(p_sequencer);
    join
  endtask : body
endclass : spi_device_flash_and_tpm_vseq
