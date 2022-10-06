// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TPM Read test, issuing READ command, writing to read fifo, checking host received data
class spi_device_tpm_rw_vseq extends spi_device_tpm_base_vseq;
  `uvm_object_utils(spi_device_tpm_rw_vseq)
  `uvm_object_new

  virtual task body();
    bit [7:0] spi_byte_q[$];
    bit [7:0] sw_byte_q[$];
    spi_device_fw_init();

    // randomised tpm configuration.
    tpm_init(TpmCrbMode);
    repeat (num_trans) begin
      bit write = $urandom;
      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(tpm_addr)
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
