// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_usbdev_dpi_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_usbdev_dpi_vseq)

  `uvm_object_new

  // Zero initialize the usbdev packet memory
  function init_packet_mem();
    cfg.mem_bkdr_util_h[UsbdevBuf].clear_mem();
  endfunction

  virtual task body();
    super.body();

    // We need to release the tb weak pull up on DP, otherwise usbdev appears
    // to be connected much too soon
    cfg.chip_vif.cfg_default_weak_pulls_on_dios(0);

    // Connect the drivers of the DPI model
    cfg.usb20_vif.enable_driver(1);

    // Zero initialize the packet memory because otherwise partial word reads
    // from a buffer will trigger 'X' assertions on the TileLink bus
    init_packet_mem();
  endtask

endclass : chip_sw_usbdev_dpi_vseq
