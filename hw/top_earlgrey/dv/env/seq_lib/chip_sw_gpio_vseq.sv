// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_gpio_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_gpio_vseq)

    bit [NUM_GPIOS-1:0] gpios_mask = {NUM_GPIOS{1'b1}};
    uint                timeout_ns = 2_000_000;
    // The GPIO instance to test, selected via the plusarg '+gpio_idx'.
    uint                gpio_idx = 0;
    // The pads of the tested instance.
    gpio_pads_vif       gpios;

  `uvm_object_new

  // Override the base-class impl to pass the GPIO instance to test to SW via the backdoor.
  virtual task cpu_init();
    bit [7:0] gpio_idx_arr[1];

    void'($value$plusargs("gpio_idx=%0d", gpio_idx));
    `DV_CHECK(gpio_idx inside {[0 : NUM_GPIO_INSTS-1]})
    gpio_idx_arr = '{gpio_idx[7:0]};

    super.cpu_init();
    sw_symbol_backdoor_overwrite("gpio_idx_dv", gpio_idx_arr);
  endtask

  virtual task body();
    super.body();

    // Wait until we reach the SW test state.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)

    // The SPI host agent drives the SPI_DEV pads, which gpio0 pins 6-11 reach, so disable SPI
    // agent for this test.
    cfg.chip_vif.enable_spi_host = 0;
    gpios = cfg.gpio_pads_vifs[gpio_idx];
    gpios_mask = GpioPadsMask[gpio_idx];

    // Run the GPIO output tests.
    gpio_output_test();

    // Run the GPIO input tests.
    gpio_input_test();
  endtask

  virtual task gpio_output_test();
    // Disable GPIOs from being driven as chip inputs.
    gpios.drive_en({NUM_GPIOS{1'b0}});

    `uvm_info(`gfn, "Starting GPIO output test", UVM_LOW)

    // Check for W1 pattern on the GPIO output pins.
    for (int i = 0; i < NUM_GPIOS; i++) begin
      wait_tested_pins(1 << i);
    end

    // Wait and check all 0s.
    wait_tested_pins('0);

    // Wait and check all 1s.
    wait_tested_pins(gpios_mask);

    // Check for W0 pattern on the GPIO output pins.
    for (int i = 0; i < NUM_GPIOS; i++) begin
      wait_tested_pins(~(1 << i));
    end

    // Wait and check all 1s.
    wait_tested_pins(gpios_mask);

    // Wait and check all 0s.
    wait_tested_pins('0);
  endtask

  virtual task gpio_input_test();
    // Wait and check all zs - this indicates it is safe to drive GPIOs as inputs. The pins whose
    // pads have a default pull do not float, the SW releases all pins at once, so ignore them.
    wait_tested_pins({NUM_GPIOS{1'bz}}, 1'bz, pulled_pins());

    // Enable GPIO in input mode, drive only the tested pins low. drive() would enable all pins,
    // including the untested TAP strap pads of gpio1.
    gpios.pins_o = '0;
    gpios.drive_en(gpios_mask);

    `uvm_info(`gfn, "Starting GPIO input test", UVM_LOW)

    // Each GPIO pin flip will cause an interrupt to fire. We need to provide sufficient time to
    // allow the SW to service the interrupt and be ready for the next one. Hence, we add
    // sufficiently long delays between GPIO pin flips.

    // Drive T1 pattern.
    for (int i = 0; i < NUM_GPIOS; i++) begin
      if (!gpios_mask[i]) continue;
      cfg.chip_vif.cpu_clk_rst_if.wait_clks($urandom_range(1100, 2000));
      gpios.drive_pin(i, 1'b1);
    end

    // Drive T0 pattern.
    for (int i = 0; i < NUM_GPIOS; i++) begin
      if (!gpios_mask[i]) continue;
      cfg.chip_vif.cpu_clk_rst_if.wait_clks($urandom_range(1100, 2000));
      gpios.drive_pin(i, 1'b0);
    end

  endtask

  // Returns the pins of the tested instance whose pads have a default pull in chip_if.mios_if.
  // gpio0 pin k sits on MIO pad k, gpio1 pin k on MIO pad 32 + k.
  virtual function bit [NUM_GPIOS-1:0] pulled_pins();
    for (int i = 0; i < NUM_GPIOS; i++) begin
      int pad = gpio_idx * NUM_GPIOS + i;
      if (gpios_mask[i] && pad < MioPadCount) begin
        pulled_pins[i] = cfg.chip_vif.mios_if.pins_pd[pad] | cfg.chip_vif.mios_if.pins_pu[pad];
      end
    end
  endfunction

  // Returns the actual value of pins we actually want to test (based on gpio_mask, see its
  // definition). For pins we skip, and the `ignore` pins, return `fill`.
  virtual function logic [NUM_GPIOS-1:0] tested_pins(logic fill, bit [NUM_GPIOS-1:0] ignore);
    logic [NUM_GPIOS-1:0] pins = gpios.pins;
    for (int i = 0; i < NUM_GPIOS; i++) begin
      if (!gpios_mask[i] || ignore[i]) begin
        pins[i] = fill;
      end
    end
    return pins;
  endfunction

  // Waits until the tested pins show `exp`, the untested and the `ignore` bits of `exp` are
  // ignored.
  virtual task wait_tested_pins(logic [NUM_GPIOS-1:0] exp, logic fill = 1'b0,
                                bit [NUM_GPIOS-1:0] ignore = '0);
    for (int i = 0; i < NUM_GPIOS; i++) begin
      if (!gpios_mask[i] || ignore[i]) begin
        exp[i] = fill;
      end
    end
    `DV_SPINWAIT(while (tested_pins(fill, ignore) !== exp) begin
                   @(gpios.pins);
                 end,
                 $sformatf("Timed out waiting for the gpio%0d pins (mask %0h) == %0h",
                           gpio_idx, gpios_mask, exp),
                 timeout_ns,
                 `gfn)
  endtask

endclass : chip_sw_gpio_vseq
