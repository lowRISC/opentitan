// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_base_vseq extends cip_base_vseq #(
  .CFG_T               (usbdev_env_cfg),
  .RAL_T               (usbdev_reg_block),
  .COV_T               (usbdev_env_cov),
  .VIRTUAL_SEQUENCER_T (usbdev_virtual_sequencer)
);
  `uvm_object_utils(usbdev_base_vseq)

  // various knobs to enable certain routines
  bit do_usbdev_init = 1'b1;

  // add post_reset_delays for sync between bus clk and usb clk in the apply_reset task
  bit apply_post_reset_delays_for_sync = 1'b1;

  `uvm_object_new

  // Override apply_reset to cater to usb domain as well.
  virtual task apply_reset(string kind = "HARD");
    fork
      if (kind == "HARD" || kind == "BUS_IF") begin
        super.apply_reset("HARD");
      end
      if (kind == "HARD" || kind == "USB_IF") begin
        cfg.usb_clk_rst_vif.apply_reset();
      end
    join
    do_apply_post_reset_delays_for_sync();
  endtask

  // Apply additional delays at the dut_init stage when either apply_reset or
  // wait_for_reset is called. The additional delays allow the logic to sync
  // across clock domains so that the Dut behaves deterministically. To disable
  // this, set apply_post_reset_delays_for_sync in the extended class' pre_start.
  virtual task do_apply_post_reset_delays_for_sync();
    if (apply_post_reset_delays_for_sync) begin
      fork
        cfg.clk_rst_vif.wait_clks($urandom_range(5, 10));
        cfg.usb_clk_rst_vif.wait_clks($urandom_range(5, 10));
      join
    end
  endtask

  // Override wait_for_reset to cater to usb domain as well.
  virtual task wait_for_reset(string reset_kind     = "HARD",
                              bit wait_for_assert   = 1,
                              bit wait_for_deassert = 1);

    fork
      if (reset_kind == "HARD" || reset_kind == "BUS_IF") begin
        super.wait_for_reset(reset_kind, wait_for_assert, wait_for_deassert);
      end
      if (reset_kind == "HARD" || reset_kind == "USB_IF") begin
        if (wait_for_assert) begin
          `uvm_info(`gfn, "waiting for usb rst_n assertion...", UVM_MEDIUM)
          @(negedge cfg.usb_clk_rst_vif.rst_n);
        end
        if (wait_for_deassert) begin
          `uvm_info(`gfn, "waiting for usb rst_n de-assertion...", UVM_MEDIUM)
          @(posedge cfg.usb_clk_rst_vif.rst_n);
        end
        `uvm_info(`gfn, "usb wait_for_reset done", UVM_HIGH)
      end
    join
    do_apply_post_reset_delays_for_sync();
  endtask

  // Override dut_init to do some basic usbdev initializations (if enabled).
  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_usbdev_init) usbdev_init();
  endtask

  virtual task dut_shutdown();
    // check for pending usbdev operations and wait for them to complete
    // TODO
  endtask

  // setup basic usbdev features
  virtual task usbdev_init(bit [TL_DW-1:0] device_address = 0);
    // Enable USBDEV
    ral.usbctrl.enable.set(1'b1);
    ral.usbctrl.device_address.set(device_address);
    csr_update(ral.usbctrl);
  endtask

endclass : usbdev_base_vseq
