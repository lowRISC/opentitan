// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_phy_pins_sense_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_phy_pins_sense_vseq)

  `uvm_object_new

  // Randomized pin configuration.
  rand bit set_dp_o;
  rand bit set_dn_o;
  rand bit set_oe_o;
  rand bit set_rx_enable_o;

  task pre_start();
    // Prevent normal device initialization.
    //
    // This sequence is designed to drive the USB lines without valid USB traffic, so the
    // last thing we need is the driver and monitor connecting. The monitor would reject the bus
    // state or apparent traffic.
    do_usbdev_init = 1'b0;

    super.pre_start();
  endtask

  task body();
    uvm_reg_data_t sense;
    // Presently the usb20_monitor is kept deactivated by not asserting the VBUS line; perhaps in
    // time we shall be able to randomize the VBUS state and thus the pullup enables.
    bit exp_vbus = 1'b0;
    bit exp_dp_i;
    bit exp_dn_i;
    bit exp_d_i;

    // Configure phy_pins_drive register
    // Set dp and dn randomly (0 or 1)
    ral.phy_pins_drive.dp_o.set(set_dp_o);
    ral.phy_pins_drive.dn_o.set(set_dn_o);
    ral.phy_pins_drive.oe_o.set(set_oe_o);
    ral.phy_pins_drive.rx_enable_o.set(set_rx_enable_o);
    ral.phy_pins_drive.en.set(1'b1);
    csr_update(ral.phy_pins_drive);

    // Outputs need to propagate to input pins and then the CSR state.
    loopback_delay();

    // Form expectations.
    exp_dp_i = set_oe_o ? set_dp_o : 1'b0;
    exp_dn_i = set_oe_o ? set_dn_o : 1'b0;
    exp_d_i  = set_rx_enable_o ? (exp_dp_i & ~exp_dn_i) : 1'b0;

    // Read phy_pins_sense reg
    csr_rd(.ptr(ral.phy_pins_sense), .value(sense));
    // DV_CHECKS to compare the input (given through phy_pins_drive reg) and
    // output (sampled by phy_pins_sense reg)
    `DV_CHECK_EQ(get_field_val(ral.phy_pins_sense.rx_dp_i, sense), exp_dp_i)
    `DV_CHECK_EQ(get_field_val(ral.phy_pins_sense.rx_dn_i, sense), exp_dn_i)
    `DV_CHECK_EQ(get_field_val(ral.phy_pins_sense.rx_d_i,  sense), exp_d_i)
    // The other signals, although undriven, may be known too since the transmitter is Idle and
    // there is no host/agent activity.
    `DV_CHECK_EQ(get_field_val(ral.phy_pins_sense.pwr_sense, sense), exp_vbus)
    `DV_CHECK_EQ(get_field_val(ral.phy_pins_sense.tx_oe_o,   sense), 1'b0)
    `DV_CHECK_EQ(get_field_val(ral.phy_pins_sense.tx_se0_o,  sense), 1'b0)
    `DV_CHECK_EQ(get_field_val(ral.phy_pins_sense.tx_d_o,    sense), 1'b1)
    `DV_CHECK_EQ(get_field_val(ral.phy_pins_sense.tx_dp_o,   sense), 1'b1)
    `DV_CHECK_EQ(get_field_val(ral.phy_pins_sense.tx_dn_o,   sense), 1'b0)
  endtask

endclass
