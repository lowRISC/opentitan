// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_phy_pins_sense_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_phy_pins_sense_vseq)

  `uvm_object_new

  rand bit set_dp;
  rand bit set_dn;

  task body();
    bit rx_dp;
    bit rx_dn;

    super.dut_init("HARD");
    // Configure phy_pins_drive register
    // Set dp and dn randomly (0 or 1)

    csr_wr(.ptr(ral.phy_pins_drive.dp_o), .value(set_dp));
    csr_wr(.ptr(ral.phy_pins_drive.dn_o), .value(set_dn));
    csr_wr(.ptr(ral.phy_pins_drive.oe_o), .value(1'b1));
    csr_wr(.ptr(ral.phy_pins_drive.en), .value(1'b1));
    cfg.clk_rst_vif.wait_clks(5);

    // Read phy_pins_sense reg
    csr_rd(.ptr(ral.phy_pins_sense.rx_dp_i), .value(rx_dp));
    csr_rd(.ptr(ral.phy_pins_sense.rx_dn_i), .value(rx_dn));
    // DV_CHECKS to compare the input (given through phy_pins_drive reg) and
    // output (sampled by phy_pins_sense reg)
    `DV_CHECK_EQ(set_dp, rx_dp)
    `DV_CHECK_EQ(set_dn, rx_dn)

  endtask

endclass
