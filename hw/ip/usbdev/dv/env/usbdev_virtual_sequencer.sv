// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_virtual_sequencer extends cip_base_virtual_sequencer #(
  .CFG_T(usbdev_env_cfg),
  .COV_T(usbdev_env_cov)
);
  `uvm_component_utils(usbdev_virtual_sequencer)

  usb20_sequencer usb20_sequencer_h;

  `uvm_component_new

endclass
