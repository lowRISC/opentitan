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
  bit  do_init_reset = 1;

  constraint delay_c {
    delay dist {0 :/ 20, [1:5] :/ 40, [6:15] :/ 30, [20:25] :/ 10};
  }
  constraint num_trans_c {
    num_trans inside {[20:200]};
  }

  `uvm_object_utils(gpio_base_vseq)
  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    if (do_init_reset) begin
      // Check for weak pullup or weak pulldown requirement
      if (cfg.pullup_en) begin
        cfg.gpio_vif.set_pullup_en({NUM_GPIOS{1'b1}});
        //cfg.gpio_vif.set_pulldown_en({NUM_GPIOS{1'b0}});
        `uvm_info(`gfn, "weak pullup applied to gpio's", UVM_LOW)
      end else if (cfg.pulldown_en) begin
        //cfg.gpio_vif.set_pullup_en({NUM_GPIOS{1'b0}});
        cfg.gpio_vif.set_pulldown_en({NUM_GPIOS{1'b1}});
        `uvm_info(`gfn, "weak pulldown applied to gpio's", UVM_LOW)
      end
      super.dut_init(reset_kind);
    end else begin
      // since stress_all_with_rand_reset test have to turn off the reset here,
      // this step makes sure that we reset out and oe pins to avoid drive x in gpio_in
      drive_gpio_out('0);
      drive_gpio_oe('0);
    end
  endtask : dut_init

  // Function: set_gpio_pulls
  // This function is meant to override gpio pullup or pulldown value
  // from extended sequence.
  // Note: This function does not check whether only one of 'pu' and 'pd' is passed 1.
  //       If we pass both pu and pd to be 1, gpio pullup will be used.
  protected function void set_gpio_pulls(bit pu = 1'b1, bit pd = 1'b0);
    bit no_pullup_pulldown;
    cfg.pullup_en   = pu;
    cfg.pulldown_en = pd;
    if ($value$plusargs("no_pullup_pulldown=%0b", no_pullup_pulldown)) begin
      if (no_pullup_pulldown == 1'b1) begin
        cfg.pullup_en   = 1'b0;
        cfg.pulldown_en = 1'b0;
      end
    end
  endfunction

  task pre_start();
    super.pre_start();
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
