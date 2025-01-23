// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This test vseq is paired with SW test `sw/device/tests/gpio_smoketest.c`.
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
    void'(dv_utils_pkg::sw_symbol_get_addr_size(
              .elf_file({p_sequencer.cfg.sw_images[SwTypeTestSlotA], ".elf"}),
              .symbol(SW_SYM_GPIO_VALS),
              .does_not_exist_ok(0),
              .addr(addr),
              .size(num_gpio_vals)));
    num_gpio_vals /= 4;
  endfunction

  virtual task cpu_init();
    bit [7:0] byte_gpio_vals[];
    super.cpu_init();
    // Need to convert integer array to byte array.
    byte_gpio_vals = new[4 * num_gpio_vals];
    byte_gpio_vals = {<<byte{{<<int{gpio_vals}}}};
    sw_symbol_backdoor_overwrite(SW_SYM_GPIO_VALS, byte_gpio_vals);
  endtask

  virtual task body();
    super.body();

    // Wait until we reach the SW test state.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)

    `uvm_info(`gfn, "Starting GPIO output test", UVM_LOW)
    for (int i = 0; i < num_gpio_vals; i++) begin
      `DV_SPINWAIT(wait(cfg.chip_vif.gpios_if.pins === gpio_vals[i][NUM_GPIOS-1:0]);,
                   $sformatf("Timed out waiting for GPIOs == %0h", gpio_vals[i][NUM_GPIOS-1:0]),
                   TIMEOUT_NS,
                  `gfn)
    end

    // Test walking 1s and 0s.
    for (int i = 0; i < NUM_GPIOS; i++) begin
      logic [NUM_GPIOS-1:0] exp_gpios = (1 << i);
      `DV_SPINWAIT(wait(cfg.chip_vif.gpios_if.pins === exp_gpios);,
                   $sformatf("Timed out waiting for GPIOs == %0h", exp_gpios),
                   TIMEOUT_NS,
                  `gfn)

      exp_gpios = ~exp_gpios;
      `DV_SPINWAIT(wait(cfg.chip_vif.gpios_if.pins === exp_gpios);,
                   $sformatf("Timed out waiting for GPIOs == %0h", exp_gpios),
                   TIMEOUT_NS,
                  `gfn)
    end
  endtask

endclass
