// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_phy_config_pinflip_vseq extends usbdev_smoke_vseq;
  `uvm_object_utils(usbdev_phy_config_pinflip_vseq)

  `uvm_object_new

  virtual task body();
    // The DUT should already be connected at this point, and the pin flipping has been
    // configured 'run_opts' to set 'pin_flip' so all we need to do here is check that they
    // really are flipped by checking the line state.
    `DV_CHECK_EQ(phy_pinflip, 1, "Pin flipping must be enabled for this sequence")
    // The bus should be Idle at this point.
    `DV_CHECK_EQ(cfg.m_usb20_agent_cfg.bif.usb_p, 0, "DP should be low during Idle state")
    `DV_CHECK_EQ(cfg.m_usb20_agent_cfg.bif.usb_n, 1, "DN should be high during Idle state")
    // Check the pull up enables.
    `DV_CHECK_EQ(cfg.m_usb20_agent_cfg.bif.usb_dp_pullup_o, 0, "DP pull up should be disabled")
    `DV_CHECK_EQ(cfg.m_usb20_agent_cfg.bif.usb_dn_pullup_o, 1, "DN pull up should be enabled")
    // Check that communication may be performed successfully.
    super.body();
  endtask
endclass : usbdev_phy_config_pinflip_vseq
