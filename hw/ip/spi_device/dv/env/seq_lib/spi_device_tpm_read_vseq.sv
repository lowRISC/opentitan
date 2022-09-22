// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// TPM Read test, issuing READ command, writing to read fifo, checking host received data
class spi_device_tpm_read_vseq extends spi_device_tpm_base_vseq;
  `uvm_object_utils(spi_device_tpm_read_vseq)
  `uvm_object_new

  virtual task body();
    bit [23:0] tpm_addr = $urandom;
    bit [7:0] ret_byte_q[$];
    bit [7:0] rfifo_byte_q[$];
    int read_size = 4; // TODO, fixed size for now
    spi_device_init();

    // randomised tpm configuration.
    tpm_init();
    tpm_configure();
    repeat (num_trans) begin
      // send cmd_addr
      fork
        begin
          spi_host_xfer_tpm_item(
            .write(0),
            .payload_q(ret_byte_q),
            .read_size(read_size),
            .addr(tpm_addr));
        end
        begin
          wait_and_fill_tpm_rfifo(tpm_addr, read_size, rfifo_byte_q);
        end
      join
      `DV_CHECK_Q_EQ(ret_byte_q, rfifo_byte_q)
    end
  endtask : body

endclass : spi_device_tpm_read_vseq
