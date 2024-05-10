// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_rx_crc_err_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_rx_crc_err_vseq)

  `uvm_object_new

  task body();
    // Configure transaction
    configure_out_trans();

    // Enable rx_crc_err interrupt
    csr_wr(.ptr(ral.intr_enable.rx_crc_err), .value(1'b1));

    // Out Token packet with corrupted CRC5
    call_token_seq(PidTypeOutToken);
    // Adding a delay ensures that the CRC5 status is updated and triggers the
    // interrupt to go high.
    cfg.clk_rst_vif.wait_clks(4);

    // In this check we are checking the rx crc error interrupt bit because we are sending corrupt
    // crc and after getting corrupt crc the rx crc err bit should be high.
    `DV_CHECK_EQ(cfg.intr_vif.sample_pin(IntrRxCrcErr), 1'b1)
  endtask

  // Override the create_token_pkt function to corrupt the crc5
  virtual function token_pkt create_token_pkt(pid_type_e pid_type);
    token_pkt pkt = super.create_token_pkt(pid_type);
    pkt.crc5 = ~pkt.crc5;
    return pkt;
  endfunction

endclass
