// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_gpio_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_gpio_vseq)

    bit [NUM_GPIOS-1:0] gpios_mask = {chip_env_pkg::NUM_GPIOS{1'b1}};
    uint                timeout_ns = 2_000_000;

  `uvm_object_new

  virtual task body();
    super.body();

    // Wait until we reach the SW test state.
    wait(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest);

    // Disable pullups and pulldowns on GPIOs.
    cfg.gpio_vif.set_pulldown_en({chip_env_pkg::NUM_GPIOS{1'b0}});
    cfg.gpio_vif.set_pullup_en({chip_env_pkg::NUM_GPIOS{1'b0}});

    // Run the GPIO output tests.
    gpio_output_test();

    // Run the GPIO input tests.
    gpio_input_test();
  endtask

  virtual task gpio_output_test();
    // Disable GPIOs from being driven as chip inputs.
    cfg.gpio_vif.drive_en({chip_env_pkg::NUM_GPIOS{1'b0}});

    `uvm_info(`gfn, "Starting GPIO output test", UVM_LOW)

    // Check for W1 pattern on the GPIO output pins.
    for (int i = 0; i < NUM_GPIOS; i++) begin
      logic [NUM_GPIOS-1:0] exp_gpios = 1 << i;
      `DV_SPINWAIT(wait(cfg.gpio_vif.pins === exp_gpios);,
                   $sformatf("Timed out waiting for GPIOs == %0h", exp_gpios),
                   timeout_ns,
                  `gfn)
    end

    // Wait and check all 0s.
    `DV_SPINWAIT(wait(cfg.gpio_vif.pins === ~gpios_mask);,
                 $sformatf("Timed out waiting for GPIOs == %0h", ~gpios_mask),
                 timeout_ns,
                `gfn)

    // Wait and check all 1s.
    `DV_SPINWAIT(wait(cfg.gpio_vif.pins === gpios_mask);,
                 $sformatf("Timed out waiting for GPIOs == %0h", gpios_mask),
                 timeout_ns,
                `gfn)

    // Check for W0 pattern on the GPIO output pins.
    for (int i = 0; i < NUM_GPIOS; i++) begin
      logic [NUM_GPIOS-1:0] exp_gpios = ~(1 << i);
      `DV_SPINWAIT(wait(cfg.gpio_vif.pins === gpios_mask);,
                   $sformatf("Timed out waiting for GPIOs == %0h", exp_gpios),
                   timeout_ns,
                  `gfn)
    end

    // Wait and check all 1s.
    `DV_SPINWAIT(wait(cfg.gpio_vif.pins === gpios_mask);,
                 $sformatf("Timed out waiting for GPIOs == %0h", gpios_mask),
                 timeout_ns,
                `gfn)

    // Wait and check all 0s.
    `DV_SPINWAIT(wait(cfg.gpio_vif.pins === ~gpios_mask);,
                 $sformatf("Timed out waiting for GPIOs == %0h", ~gpios_mask),
                 timeout_ns,
                `gfn)
  endtask

  virtual task gpio_input_test();
    // Wait and check all zs - this indicates it is safe to drive GPIOs as inputs.
    `DV_SPINWAIT(wait(cfg.gpio_vif.pins === {NUM_GPIOS{1'bz}});,
                 $sformatf("Timed out waiting for GPIOs == %0h", {NUM_GPIOS{1'bz}}),
                 timeout_ns,
                `gfn)

    // Enable GPIO in input mode.
    cfg.gpio_vif.drive_en(gpios_mask);
    cfg.gpio_vif.drive(~gpios_mask);

    `uvm_info(`gfn, "Starting GPIO input test", UVM_LOW)

    // Each GPIO pin flip will cause an interrupt to fire. We need to provide sufficient time to
    // allow the SW to service the interrupt and be ready for the next one. Hence, we add
    // sufficiently long delays between GPIO pin flips.

    // Drive T1 pattern.
    for (int i = 0; i < NUM_GPIOS; i++) begin
      cfg.clk_rst_vif.wait_clks($urandom_range(400, 600));
      cfg.gpio_vif.drive_pin(i, 1'b1);
    end

    // Drive T0 pattern.
    for (int i = 0; i < NUM_GPIOS; i++) begin
      cfg.clk_rst_vif.wait_clks($urandom_range(400, 600));
      cfg.gpio_vif.drive_pin(i, 1'b0);
    end

  endtask

endclass : chip_sw_gpio_vseq
