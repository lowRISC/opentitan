// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_usbdev_dpi_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_usbdev_dpi_vseq)

  `uvm_object_new

  // Clock frequency delta (usbdpi clk freq - usbdev clk freq).
  int usbdpi_clk_freq_delta;

  // Frequency of the usbdpi clk.
  int usbdpi_freq;

  // Perform the typical start up of the USB DPI automatically.
  bit do_usbdpi_start = 1;

  // Zero initialize the usbdev packet memory
  function void init_packet_mem();
    cfg.mem_bkdr_util_h[UsbdevBuf].clear_mem();
  endfunction

  // Ensure that the USB DPI model has been configured with the desired clock frequency;
  // it runs on its own clock for a few reasons:
  //
  // - there is no shared clock between USB hosts and devices; USB devices are expected
  //   to synchronize to the received traffic.
  // - it must remain operable when the chip enters Deep Sleep, so that it
  //   may provide the Wakeup stimulus; by constrast the USBDEV clock is stopped.
  // - operating at the opposite frequency extreme permits us to exercise the
  //   synchronization and bitstream extraction.
  virtual task cpu_init();
    super.cpu_init();

    // Read the frequency delta of the usbdpi model relative to usb_clk
    if (!$value$plusargs("usbdpi_clk_freq_delta=%d", usbdpi_clk_freq_delta)) begin
      usbdpi_clk_freq_delta = 0;
    end
    usbdpi_freq = 48_000_000 + usbdpi_clk_freq_delta;
  endtask

  // Start the USB DPI model.
  virtual task usbdpi_start();
    int freq_khz = (usbdpi_freq + 500) / 1000;
    `uvm_info(`gfn, $sformatf("USB DPI model starting with a clock frequency of %dkHz", freq_khz),
              UVM_MEDIUM)
    cfg.usbdpi_clk_rst_vif.set_freq_khz(freq_khz);
    // Drop the reset signal, to ensure that the host-driven USB VBUS is in a defined state when
    // we subsequently connect.
    cfg.usbdpi_clk_rst_vif.drive_rst_pin(0);
    cfg.usbdpi_clk_rst_vif.set_active();
  endtask

  // Reset the USB DPI model; leave the reset asserted for around 100us because the CPU
  // has a body of code to run before it will connect to the USB.
  virtual task usbdpi_apply_reset();
    `uvm_info(`gfn, "Starting reset of USB DPI model", UVM_MEDIUM)
    fork
      cfg.usbdpi_clk_rst_vif.apply_reset(.reset_width_clks(4_800));
    join_none
  endtask

  virtual task body();
    super.body();

    // Optionally start the USB DPI model in the typical manner.
    if (do_usbdpi_start) begin
      usbdpi_start();
      usbdpi_apply_reset();
    end

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
