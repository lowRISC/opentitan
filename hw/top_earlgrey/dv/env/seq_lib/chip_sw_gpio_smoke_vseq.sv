// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test vseq is paired with SW test `sw/device/tests/dif_gpio_smoketest.c`.
class chip_sw_gpio_smoke_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_gpio_smoke_vseq)

  // We override the SW symbol `kGpioVals` with our own set of random values.
  localparam string SW_SYM_GPIO_VALS = "kGpioVals";
  localparam uint TIMEOUT_NS = 2_000_000;

  // Declared as int to match the SW test.
  rand int gpio_vals[];
  uint num_gpio_vals;
  constraint gpio_vals_c {
    gpio_vals.size() == num_gpio_vals;
  }

  `uvm_object_new

  function void pre_randomize();
    int addr;
    // Find how many bytes the SW allocate for SW_SYM_GPIO_VALS, then convert to word size.
    sw_symbol_get_addr_size({p_sequencer.cfg.sw_images[SwTypeTest], ".elf"},
                            SW_SYM_GPIO_VALS, addr, num_gpio_vals);
    num_gpio_vals /= 4;
  endfunction

  virtual task cpu_init();
    super.cpu_init();
    // Need to convert integer array to byte array.
    sw_symbol_backdoor_overwrite(SW_SYM_GPIO_VALS, {<<byte{{<<int{gpio_vals}}}});
  endtask

  virtual task body();
    super.body();

    // Wait until we reach the SW test state.
    wait(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest);

    // Disable the default pulldown on GPIOs.
    cfg.gpio_vif.set_pulldown_en({chip_env_pkg::NUM_GPIOS{1'b0}});

    `uvm_info(`gfn, "Starting GPIO output test", UVM_LOW)
    for (int i = 0; i < num_gpio_vals; i++) begin
      `DV_SPINWAIT(wait(cfg.gpio_vif.pins === gpio_vals[i][NUM_GPIOS-1:0]);,
                   $sformatf("Timed out waiting for GPIOs == %0h", gpio_vals[i][NUM_GPIOS-1:0]),
                   TIMEOUT_NS,
                  `gfn)
    end

    // Test walking 1s and 0s.
    for (int i = 0; i < NUM_GPIOS; i++) begin
      logic [NUM_GPIOS-1:0] exp_gpios = (1 << i);
      `DV_SPINWAIT(wait(cfg.gpio_vif.pins === exp_gpios);,
                   $sformatf("Timed out waiting for GPIOs == %0h", exp_gpios),
                   TIMEOUT_NS,
                  `gfn)

      exp_gpios = ~exp_gpios;
      `DV_SPINWAIT(wait(cfg.gpio_vif.pins === exp_gpios);,
                   $sformatf("Timed out waiting for GPIOs == %0h", exp_gpios),
                   TIMEOUT_NS,
                  `gfn)
    end
  endtask

endclass
