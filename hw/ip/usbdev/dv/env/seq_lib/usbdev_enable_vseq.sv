// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_enable_vseq extends usbdev_base_vseq;
  `uvm_object_utils(usbdev_enable_vseq)

  `uvm_object_new

  task pre_start();
    // need to disable device init.
    // This sequence is designed to assess the functionality of the USB_CTRL register's
    // enable field. During device initialization, the device is automatically enabled.
    // Therefore, if we want to accurately test the device enable function,
    // we need to manually set this.
    do_usbdev_init = 1'b0;

    super.pre_start();
  endtask

  // Sense the pins, checking against expectations.
  task sense_pins(bit exp_dp, bit exp_dn, bit exp_vbus);
    uvm_reg_data_t sense;
    // Check that both of the lines are low.
    csr_rd(.ptr(ral.phy_pins_sense), .value(sense));
    `DV_CHECK_EQ(get_field_val(ral.phy_pins_sense.rx_dp_i, sense), exp_dp, "DP not as expected")
    `DV_CHECK_EQ(get_field_val(ral.phy_pins_sense.rx_dn_i, sense), exp_dn, "DN not as expected")
    // Also, just to be thorough, VBUS should be high.
    `DV_CHECK_EQ(get_field_val(ral.phy_pins_sense.pwr_sense, sense), exp_vbus,
                               "VBUS not as expected")
  endtask

  task body();
    uvm_reg_data_t enabled;

    // First ensure that the driver has asserted VBUS.
    set_vbus_state(1);

    // Check that connection has not been requested and that the DUT is _not_ connected.
    csr_rd(.ptr(ral.usbctrl.enable), .value(enabled));
    `DV_CHECK_EQ(enabled, 0, "DUT connect has been unexpectedly requested")
    sense_pins(.exp_dp(0), .exp_dn(0), .exp_vbus(1));
    // ...okay, so we may reasonably infer that neither pull up is asserted.

    // Now request connection.
    ral.usbctrl.enable.set(1'b1);
    csr_update(ral.usbctrl);
    loopback_delay();

    // Try the pins again.
    sense_pins(.exp_dp(1), .exp_dn(0), .exp_vbus(1));
  endtask

endclass
