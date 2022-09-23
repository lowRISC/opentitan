// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TPM Read test, issuing READ command, writing to read fifo, checking host received data
class spi_device_tpm_rw_vseq extends spi_device_tpm_base_vseq;
  `uvm_object_utils(spi_device_tpm_rw_vseq)
  `uvm_object_new

  rand uint tpm_size = 4;

  constraint tpm_size_c {
    tpm_size dist {
      [1:3]              :/ 1,
      4                  :/ 2,
      [5:MAX_SUPPORT_TPM_SIZE-1] :/ 2,
      MAX_SUPPORT_TPM_SIZE       :/ 1
    };
  }
  virtual task body();
    bit [7:0] spi_byte_q[$];
    bit [7:0] sw_byte_q[$];
    spi_device_init();

    // randomised tpm configuration.
    tpm_init();
    tpm_configure();
    repeat (num_trans) begin
      bit write = $urandom;
      bit [TPM_ADDR_WIDTH-1:0] tpm_addr = $urandom;
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(tpm_size)
      fork
        begin
          spi_host_xfer_tpm_item(write, tpm_size, tpm_addr, spi_byte_q);
        end
        begin
          wait_and_process_tpm_fifo(write, tpm_addr, tpm_size, sw_byte_q);
        end
      join
      `DV_CHECK_Q_EQ(spi_byte_q, sw_byte_q)
    end
  endtask : body

endclass : spi_device_tpm_rw_vseq
