// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class gpio_base_vseq extends cip_base_vseq #(
        .CFG_T               (gpio_env_cfg),
        .RAL_T               (gpio_reg_block),
        .COV_T               (gpio_env_cov),
        .VIRTUAL_SEQUENCER_T (gpio_virtual_sequencer)
    );

  // Delay between consecutive transactions
  rand uint delay;
  constraint delay_c {
    delay dist {0 :/ 20, [1:5] :/ 40, [6:15] :/ 30, [20:25] :/ 10};
  }
  `uvm_object_utils(gpio_base_vseq)

  `uvm_object_new

  task pre_start();
    super.pre_start();
  endtask

  task body();
    `uvm_fatal(`gtn, "Need to override this when you extend from this class!")
  endtask : body

  virtual task dut_shutdown();
    // TODO(sriyerg): nothing to do yet
  endtask

  // Task: drive_gpio_in
  // task to drive dut gpio inputs (gpio_en_o from dut must be configured to 0)
  virtual task drive_gpio_in(bit [NUM_GPIOS-1:0] val);
    ral.direct_oe.set('0);
    csr_update(ral.direct_oe);
    cfg.gpio_vif.drive(val);
  endtask

  // Task: undrive_gpio_in
  virtual task undrive_gpio_in();
    cfg.gpio_vif.drive_en('0);
  endtask : undrive_gpio_in

  // Task: drive_gpio_out
  // task to drive dut gpio outputs
  virtual task drive_gpio_out(bit [NUM_GPIOS-1:0] val);
    ral.direct_out.set(val);
    csr_update(ral.direct_out);
  endtask

  // Task: drive_gpio_oe
  // task to drive dut gpio output enables
  virtual task drive_gpio_oe(bit [NUM_GPIOS-1:0] val);
    ral.direct_oe.set(val);
    csr_update(ral.direct_oe);
  endtask

  // Task: sample_gpio
  // task to sample gpio pins
  virtual task sample_gpio(ref bit [NUM_GPIOS-1:0] val);
    val = cfg.gpio_vif.sample();
  endtask

  // Task : pgm_intr_regs
  // This task program a random set of interrupt registers
  // with random values
  task pgm_intr_regs();
    if ($urandom_range(0, 1)) begin
      `DV_CHECK_RANDOMIZE_FATAL(ral.intr_enable)
      csr_update(ral.intr_enable);
    end
    if ($urandom_range(0, 1)) begin
      `DV_CHECK_RANDOMIZE_FATAL(ral.intr_ctrl_en_falling)
      csr_update(ral.intr_ctrl_en_falling);
    end
    if ($urandom_range(0, 1)) begin
      `DV_CHECK_RANDOMIZE_FATAL(ral.intr_ctrl_en_rising)
      csr_update(ral.intr_ctrl_en_rising);
    end
    if ($urandom_range(0, 1)) begin
      `DV_CHECK_RANDOMIZE_FATAL(ral.intr_ctrl_en_lvllow)
      csr_update(ral.intr_ctrl_en_lvllow);
    end
    if ($urandom_range(0, 1)) begin
      `DV_CHECK_RANDOMIZE_FATAL(ral.intr_ctrl_en_lvlhigh)
      csr_update(ral.intr_ctrl_en_lvlhigh);
    end
  endtask : pgm_intr_regs

endclass : gpio_base_vseq
