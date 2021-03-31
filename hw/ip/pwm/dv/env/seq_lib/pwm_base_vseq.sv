// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_base_vseq extends cip_base_vseq #(
  .RAL_T              (pwm_reg_block),
  .CFG_T              (pwm_env_cfg),
  .COV_T              (pwm_env_cov),
  .VIRTUAL_SEQUENCER_T(pwm_virtual_sequencer)
);
  `uvm_object_utils(pwm_base_vseq)
  `uvm_object_new

  // random variables
  rand uint          num_runs;
  rand bit [26:0]    clk_div;
  rand bit [3:0]     dc_resn;
  // pwm registers
  rand pwm_regs_t    pwm_regs;

  // constraints
  constraint num_trans_c {
    //num_trans inside {[cfg.seq_cfg.pwm_min_num_trans : cfg.seq_cfg.pwm_max_num_trans]};
    num_trans == 8;
  }
  constraint num_runs_c {
    num_runs inside {[cfg.seq_cfg.pwm_min_num_runs : cfg.seq_cfg.pwm_max_num_runs]};
  }

  constraint pwm_regs_c {
    // TODO: currently, only Standard mode is verified in the smoke test
    foreach (pwm_regs.pwm_mode[i]) {
      pwm_regs.pwm_mode[i] dist {
        Standard  :/ 1,
        Blinking  :/ 0,
        Heartbeat :/ 0
      };
    }

    // constraints for single regs
    pwm_regs.dc_resn inside {[cfg.seq_cfg.pwm_min_dc_resn : cfg.seq_cfg.pwm_max_dc_resn]};
    pwm_regs.clk_div inside {[cfg.seq_cfg.pwm_min_clk_div : cfg.seq_cfg.pwm_max_clk_div]};
    pwm_regs.num_pulses inside {[cfg.seq_cfg.pwm_min_num_pulses : cfg.seq_cfg.pwm_max_num_pulses]};
    //pwm_regs.num_pulses == 1;
    // constraints for multi regs
    foreach (pwm_regs.en[i]) {
      pwm_regs.en[i] dist {1'b0 :/ 1, 1'b1 :/ 1};
    }
    foreach (pwm_regs.invert[i]) {
      pwm_regs.invert[i] dist {1'b0 :/ 1, 1'b1 :/ 1};
    }
    foreach (pwm_regs.phase_delay[i]) {
      pwm_regs.phase_delay[i]   inside {[cfg.seq_cfg.pwm_min_phase_delay :
                                         cfg.seq_cfg.pwm_max_phase_delay]};
    }
    foreach (pwm_regs.blink_param_x[i]) {
      pwm_regs.blink_param_x[i] inside {[cfg.seq_cfg.pwm_min_blink_param :
                                         cfg.seq_cfg.pwm_max_blink_param]};
    }
    foreach (pwm_regs.blink_param_y[i]) {
      pwm_regs.blink_param_y[i] inside {[cfg.seq_cfg.pwm_min_blink_param :
                                         cfg.seq_cfg.pwm_max_blink_param]};
    }
    foreach (pwm_regs.duty_cycle_a[i]) {
      pwm_regs.duty_cycle_a[i] dist {
        [0:2**(pwm_regs.dc_resn + 1) - 1] :/1,
         2**(pwm_regs.dc_resn + 1) :/1,
        [2**(pwm_regs.dc_resn + 1) + 1 : 2**(pwm_regs.dc_resn +
                                             cfg.seq_cfg.pwm_max_dc_resn + 1)] :/2
      };
    }
    foreach (pwm_regs.duty_cycle_b[i]) {
      pwm_regs.duty_cycle_b[i] dist {
        [0:2**(pwm_regs.dc_resn + 1) - 1] :/2,
         2**(pwm_regs.dc_resn + 1) :/1,
        [2**(pwm_regs.dc_resn + 1) + 1 : 2**(pwm_regs.dc_resn +
                                             cfg.seq_cfg.pwm_max_dc_resn + 1)] :/2
      };
    }
  }

  //================================
  virtual task pre_start();
    num_runs.rand_mode(0);
    // unset to disable intr test because pwm does not have intr pins
    do_clear_all_interrupts = 1'b0;
    super.pre_start();
  endtask : pre_start

  virtual task initialization();
    wait(cfg.clk_rst_vif.rst_n && cfg.clk_rst_core_vif.rst_n);
    `uvm_info(`gfn, "\n  base_vseq: out of reset", UVM_DEBUG)
    csr_spinwait(.ptr(ral.regen), .exp_data(1'b1));
    `uvm_info(`gfn, "\n  base_vseq: clear regen to allow programming channel registers", UVM_DEBUG)
  endtask : initialization

  //=== tasks for programming single registers
  // clear regen after initialization to allow programming registers
  virtual task program_pwm_regen_reg(pwm_status_e status);
    csr_wr(.ptr(ral.regen), .value(status));
    `uvm_info(`gfn, $sformatf("\n  base_vseq: program regen %s", status.name()), UVM_DEBUG)
  endtask : program_pwm_regen_reg

  virtual task program_pwm_cfg_reg();
    ral.cfg.clk_div.set(pwm_regs.clk_div);
    ral.cfg.dc_resn.set(pwm_regs.dc_resn);
    csr_update(ral.cfg);
    `uvm_info(`gfn, "\n  base_vseq: clear counter and program clk_div and dc_resn", UVM_DEBUG)
  endtask : program_pwm_cfg_reg

  virtual task program_pwm_cfg_counters(pwm_status_e status);
    ral.cfg.cntr_en.set(status);      // reset counting
    csr_update(ral.cfg);
    `uvm_info(`gfn, $sformatf("\n  base_vseq: %s beat and phase counter",
        (status == Enable) ? "START" : "RESET"), UVM_DEBUG)
  endtask : program_pwm_cfg_counters

  //=== tasks for programming multi registers
  virtual task start_pwm_channels();
    program_pwm_cfg_counters(Enable);
    csr_wr(.ptr(ral.pwm_en), .value(pwm_regs.en));
    `uvm_info(`gfn, $sformatf("\n  base_vseq: start channels (%b)", pwm_regs.en), UVM_DEBUG)
  endtask : start_pwm_channels

  virtual task run_pwm_channels();
    int runtime;

    runtime =  pwm_regs.num_pulses * pwm_regs.pulse_cycle * pwm_regs.beat_cycle;
    `DV_CHECK_NE(runtime, 0)
    cfg.clk_rst_core_vif.wait_clks(runtime);
    for (int i = 0; i < PWM_NUM_CHANNELS; i++) begin
      if (pwm_regs.en[i]) begin
        `uvm_info(`gfn, $sformatf("\n  base_vseq: pulses generated in channel %0d", i), UVM_DEBUG)
      end
    end
    // disable channels and clear phase counter
    csr_wr(.ptr(ral.pwm_en), .value({PWM_NUM_CHANNELS{1'b0}}));
    program_pwm_cfg_counters(Disable);
  endtask : run_pwm_channels

  virtual task program_pwm_invert_regs();
    for (int i = 0; i < PWM_NUM_CHANNELS; i++) begin
      set_dv_base_reg_field_by_name("invert", "invert", pwm_regs.invert[i], i);
    end
  endtask : program_pwm_invert_regs

  virtual task program_pwm_duty_cycle_regs(int channel);
    dv_base_reg base_reg = get_dv_base_reg_by_name("duty_cycle", channel);

    // set reg fields but not update
    set_dv_base_reg_field_by_name("duty_cycle", "a",
      pwm_regs.duty_cycle_a[channel], channel, channel, 1'b0);
    set_dv_base_reg_field_by_name("duty_cycle", "b",
      pwm_regs.duty_cycle_b[channel], channel, channel, 1'b0);
    // update fields in same cycle
    csr_update(base_reg);
  endtask : program_pwm_duty_cycle_regs

  virtual task program_pwm_blink_param_regs(int channel);
    dv_base_reg base_reg = get_dv_base_reg_by_name("blink_param", channel);
    // set reg fields but not update
    set_dv_base_reg_field_by_name("blink_param", "x",
        pwm_regs.blink_param_x[channel], channel, channel, 1'b0);
    set_dv_base_reg_field_by_name("blink_param", "y",
        pwm_regs.blink_param_y[channel], channel, channel, 1'b0);
    // update fields in same cycle
    csr_update(base_reg);
  endtask : program_pwm_blink_param_regs

  // override apply_reset to handle reset for bus and core domain
  virtual task apply_reset(string kind = "HARD");
    fork
      if (kind == "HARD" || kind == "TL_IF") begin
        super.apply_reset("HARD");
      end
      if (kind == "HARD" || kind == "CORE_IF") begin
        cfg.clk_rst_core_vif.apply_reset();
      end
    join
  endtask : apply_reset

  // phase alignment for resets signal of core and bus domain
  virtual task do_phase_align_reset(bit do_phase_align = 1'b0);
    if (do_phase_align) begin
      fork
        cfg.clk_rst_vif.wait_clks($urandom_range(5, 10));
        cfg.clk_rst_core_vif.wait_clks($urandom_range(5, 10));
      join
    end
  endtask : do_phase_align_reset

  // functions
  virtual function void update_pwm_reg_config(int max_channel = PWM_NUM_CHANNELS);
    // derived params
    pwm_regs.beat_cycle  = pwm_regs.clk_div + 1;
    pwm_regs.pulse_cycle = 2**(pwm_regs.dc_resn + 1);
    for (int i = 0; i < max_channel; i++) begin
      if (pwm_regs.en[i]) begin
        unique case (pwm_regs.pwm_mode[i])
          Standard: begin
            pwm_regs.pulse_duty[i] = pwm_regs.duty_cycle_a[i] % pwm_regs.pulse_cycle;
            cfg.print_pwm_regs("base_vseq", pwm_regs, i, 1'b0);
          end
        endcase
      end
      cfg.print_pwm_regs("base_vseq", pwm_regs, i);
    end
    // update pwm_cfg
    cfg.num_pulses = pwm_regs.num_pulses;
    // update agent_cfg
    cfg.invert = pwm_regs.invert;
  endfunction : update_pwm_reg_config

  // set field of reg/mreg using name and index, need to call csr_update after setting
  virtual task set_dv_base_reg_field_by_name(string  csr_name,
                                             string  field_name,
                                             uint    field_value,
                                             int     field_idx = -1,
                                             int     csr_idx = -1,
                                             bit     update  = 1'b1);
    string        reg_name;
    uvm_reg_field reg_field;
    dv_base_reg   base_reg;

    base_reg = get_dv_base_reg_by_name(csr_name, csr_idx);
    reg_name = (field_idx == -1) ? field_name : $sformatf("%s_%0d", field_name, field_idx);
    reg_field = base_reg.get_field_by_name(reg_name);
    `DV_CHECK_NE_FATAL(reg_field, null, reg_name)
    reg_field.set(field_value);
    if (update) csr_update(base_reg);
    `uvm_info(`gfn, $sformatf("base_vseq: set register %s.%s", csr_name, field_name), UVM_DEBUG)
  endtask : set_dv_base_reg_field_by_name

  // set reg/mreg using name and index
  virtual function dv_base_reg get_dv_base_reg_by_name(string csr_name,
                                                       int    csr_idx = -1);
    string  reg_name;
    uvm_reg reg_uvm;

    reg_name = (csr_idx == -1) ? csr_name : $sformatf("%s_%0d", csr_name, csr_idx);
    reg_uvm  = ral.get_reg_by_name(reg_name);
    `DV_CHECK_NE_FATAL(reg_uvm, null, reg_name)
    `downcast(get_dv_base_reg_by_name, reg_uvm)
  endfunction : get_dv_base_reg_by_name

endclass : pwm_base_vseq
