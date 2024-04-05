// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_phy_config_tx_osc_test_mode_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_phy_config_tx_osc_test_mode_vseq)

  `uvm_object_new

  task body();
    bit [10:0] usbstat_frame;
    // phy_config.tx_osc_mode If enabled, the device constantly transmits a J/K pattern,
    // which is useful for testing the USB clock. In oscillator test mode,
    // the device no longer receives SOFs.
    csr_wr(.ptr(ral.phy_config.tx_osc_test_mode), .value(1'b1));
    csr_wr(.ptr(ral.ep_out_enable[0].enable[endp]), .value(1'b1)); // Enable EP
    call_sof_seq(PktTypeSoF, PidTypeSofToken);
    csr_rd(.ptr(ral.usbstat.frame), .value(usbstat_frame));
    // Verify that device not received SoF pkt by reading USBSTAT register field frame.
    // it should be zero.
    `DV_CHECK_EQ(0, usbstat_frame);
  endtask
endclass
