// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_host_lost_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_host_lost_vseq)

  `uvm_object_new

  uint sof_loss_time_ns = 48_241; // 1.005ms

  task body();
    configure_setup_trans();
    // Enable host lost and packet sent interrupt
    csr_wr(.ptr(ral.intr_enable.host_lost), .value(1'b1));

    // Call Start of Frame Sequence
    call_sof_seq(PidTypeSofToken);
    // After four missed SOF the link state should go into host lost
    cfg.clk_rst_vif.wait_clks(sof_loss_time_ns); // 1st SOF miss
    cfg.clk_rst_vif.wait_clks(sof_loss_time_ns); // 2nd SOF miss

    // Do a transacation on USB to keep link active before 3ms
    trans_usb_keep_alive();

    cfg.clk_rst_vif.wait_clks(sof_loss_time_ns); // 3rd SOF miss
    cfg.clk_rst_vif.wait_clks(sof_loss_time_ns); // 4th SOF miss

    // Read USB host_lost interrupt to check that it is asserted
    `DV_CHECK_EQ(cfg.intr_vif.sample_pin(IntrHostLost), 1);
  endtask

  // Transaction on USB to keep it from going into suspend state
  task trans_usb_keep_alive ();
    // Configure out transaction
    configure_out_trans();

    // Out token packet followed by a data packet
    call_token_seq(PidTypeOutToken);
    inter_packet_delay();
    call_data_seq(PidTypeData0, .randomize_length(1'b1), .num_of_bytes(0));

    // Get response from DUT
    get_response(m_response_item);
    $cast(m_usb20_item, m_response_item);
    `DV_CHECK_EQ(m_usb20_item.m_pkt_type, PktTypeHandshake);
    `DV_CHECK_EQ(m_usb20_item.m_pid_type, PidTypeAck);
  endtask

endclass
