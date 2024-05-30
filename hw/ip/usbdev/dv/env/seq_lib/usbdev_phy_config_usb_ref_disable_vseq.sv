// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_phy_config_usb_ref_disable_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_phy_config_usb_ref_disable_vseq)

  `uvm_object_new

  task body();
    configure_out_trans(ep_default);
    // Tx Start of Frame (SoF) packet to the device.
    // The device will receive the SoF and in response, it will assert the usb_ref_val_o signal.
    send_sof_packet(PidTypeSofToken);
    inter_packet_delay();
    // Verify that the device has asserted the usb_ref_val_o signal after receiving the SoF packet.
    `DV_CHECK_EQ(cfg.m_usb20_agent_cfg.bif.usb_ref_val_o, 1)
    // De-assert usb_ref_disable signal from phy_config register.
    csr_wr(.ptr(ral.phy_config.usb_ref_disable), .value(1'b1));
    // Check that usb_ref_val_o is zero.
    `DV_CHECK_EQ(cfg.m_usb20_agent_cfg.bif.usb_ref_val_o, 0)
    send_sof_packet(PidTypeSofToken);
    // Confirm that after setting usb_ref_disable to 1,
    // the device will not assert the synchronous usb_ref_val_o signal.
    `DV_CHECK_EQ(cfg.m_usb20_agent_cfg.bif.usb_ref_val_o, 0)
  endtask
endclass
