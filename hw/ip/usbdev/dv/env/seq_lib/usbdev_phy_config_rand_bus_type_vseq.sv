// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_phy_config_rand_bus_type_vseq extends usbdev_smoke_vseq;
  `uvm_object_utils(usbdev_phy_config_rand_bus_type_vseq);

  `uvm_object_new

  virtual task pre_start();
    // Choose a random bus configuration.
    {phy_pinflip, phy_use_diff_rcvr, phy_tx_use_d_se0} = $urandom_range(0, 7);
    // Set up and run the test.
    super.pre_start();
  endtask
endclass : usbdev_phy_config_rand_bus_type_vseq
