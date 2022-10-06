// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Abort test, make TX FIFO full without host traffic, check for idle state
class spi_device_abort_vseq extends spi_device_base_vseq;
  `uvm_object_utils(spi_device_abort_vseq)
  `uvm_object_new

  virtual task body();
    bit [31:0] device_data;
    bit        tx_fifo_full = 0;
    bit            abort_done = 0;

    spi_device_fw_init();
    `DV_CHECK_RANDOMIZE_FATAL(this)
    `DV_CHECK_STD_RANDOMIZE_FATAL(device_data)

    while (tx_fifo_full == 0) begin
      write_device_words_to_send({device_data});
      csr_rd(.ptr(ral.status.txf_full), .value(tx_fifo_full));
    end

    cfg.clk_rst_vif.wait_clks(100);
    ral.control.abort.set(1'b1);
    csr_update(.csr(ral.control));
    //TODO Abort done returns 1 - Issue 9823 for implementation
    while (abort_done == 0) begin
      csr_rd(.ptr(ral.status.abort_done), .value(abort_done));
    end
    ral.control.abort.set(1'b0);
    csr_update(.csr(ral.control));
    cfg.clk_rst_vif.wait_clks(100);
    //TODO Checking when we get feedback on issue 9822
  endtask : body

endclass : spi_device_abort_vseq
