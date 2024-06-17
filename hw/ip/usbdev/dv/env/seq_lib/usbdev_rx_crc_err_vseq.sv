// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_rx_crc_err_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_rx_crc_err_vseq)

  `uvm_object_new

  task body();
    // Configure transaction
    configure_out_trans(ep_default);

    // Enable rx_crc_err interrupt
    csr_wr(.ptr(ral.intr_enable.rx_crc_err), .value(1'b1));

    // Out Token packet with corrupted CRC5
    inject_bad_token_crc5 = 1'b1;
    send_token_packet(ep_default, PidTypeOutToken);
    inject_bad_token_crc5 = 1'b0;

    // Wait a little while for the interrupt signal to become asserted.
    for (int i = 0; i < 16; i++) begin
      if (1'b1 === cfg.intr_vif.sample_pin(IntrRxCrcErr)) break;
      cfg.clk_rst_vif.wait_clks(1);
    end

    // Check that the interrupt has become asserted to inform firmware that a CRC error was
    // detected on an OUT packet; the correct DUT behavior on the USB is simply to ignore the
    // packet; the host will retry the transmission.
    `DV_CHECK_EQ(cfg.intr_vif.sample_pin(IntrRxCrcErr), 1'b1)
  endtask

endclass
