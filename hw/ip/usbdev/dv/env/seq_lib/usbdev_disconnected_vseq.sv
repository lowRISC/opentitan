// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_disconnected_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_disconnected_vseq)

  `uvm_object_new

  task body();
    uvm_reg_data_t rd_data;
    bit disconnected;
    // Enable disconnected interrupt
    csr_wr(.ptr(ral.intr_enable.disconnected), .value(1'b1));
    // Clear disconnected interrupt to make sure it's in reset state.
    csr_wr(.ptr(ral.intr_state.disconnected), .value(1'b1));
    // send pkt to device
    configure_out_trans(ep_default);
    send_sof_packet(PidTypeSofToken);
    for (int i = 0; i < 4; i++) begin
      @(posedge cfg.m_usb20_agent_cfg.bif.clk_i);
      if (cfg.m_usb20_agent_cfg.bif.usb_ref_val_o) break;
    end
    // Verify that the device has asserted the usb_ref_val_o signal after receiving the SoF packet.
    `DV_CHECK_EQ(cfg.m_usb20_agent_cfg.bif.usb_ref_val_o, 1)
    // Check the disconnected interrupt isn't yet asserted
    `DV_CHECK_EQ(cfg.intr_vif.pins[IntrDisconnected], 0)
    // Drive 0 on usb_vbus signal to tell device that it has been disconnected.
    cfg.m_usb20_agent_cfg.bif.drive_vbus = 1'b0;
    // Expect the disconnected interrupt within a short time
    for (int i = 0; i < 40; i++) begin
      @(posedge cfg.m_usb20_agent_cfg.bif.clk_i);
      if (cfg.intr_vif.pins[IntrDisconnected]) break;
    end
    `DV_CHECK_EQ(cfg.intr_vif.pins[IntrDisconnected], 1)
  endtask
endclass
