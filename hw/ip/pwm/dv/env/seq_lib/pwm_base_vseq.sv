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

  // number of runs
  rand uint num_runs;
  // pwm registers
  rand pwm_regs_t pwm_regs;
  // number of generated pulses
  rand int num_pulses;

  // constraints
  constraint num_trans_c {
    num_trans inside {[cfg.seq_cfg.pwm_min_num_trans : cfg.seq_cfg.pwm_max_num_trans]};
  }
  constraint num_runs_c {
    num_runs inside {[cfg.seq_cfg.pwm_min_num_runs : cfg.seq_cfg.pwm_max_num_runs]};
  }
  constraint num_pulses_c {
    num_pulses inside {[cfg.seq_cfg.pwm_min_num_pulses : cfg.seq_cfg.pwm_max_num_pulses]};
  }

  constraint pwm_regs_c {
    // constraints for single regs
    pwm_regs.dc_resn inside {[cfg.seq_cfg.pwm_min_dc_resn : cfg.seq_cfg.pwm_max_dc_resn]};
    pwm_regs.clk_div inside {[cfg.seq_cfg.pwm_min_clk_div : cfg.seq_cfg.pwm_max_clk_div]};

    // constraints for multi regs
    foreach (pwm_regs.pwm_mode[i]) {
      if (cfg.seq_cfg.pwm_run_mode == Allmodes) {
        pwm_regs.pwm_mode[i] dist {
          Standard  :/ 1,
          Blinking  :/ 1,
          Heartbeat :/ 0
        };
      } else {
        pwm_regs.pwm_mode[i] == cfg.seq_cfg.pwm_run_mode;
      }
    }
    foreach (pwm_regs.blink_en[i]) {pwm_regs.blink_en[i] == (pwm_regs.pwm_mode[i] != Standard);}
    foreach (pwm_regs.htbt_en[i]) {pwm_regs.htbt_en[i] == (pwm_regs.pwm_mode[i] == Heartbeat);}
    pwm_regs.pwm_en inside {[1 : (1 << cfg.seq_cfg.pwm_run_channel) - 1]};
    foreach (pwm_regs.invert[i]) {
      if (pwm_regs.pwm_en[i]) {
        pwm_regs.invert[i] dist {
          1'b1 :/ 1,
          1'b0 :/ 1
        };
      } else {
        pwm_regs.invert[i] == 1'b0;
      }
    }
    foreach (pwm_regs.phase_delay[i]) {
      pwm_regs.phase_delay[i] inside {[0 : 2 ** (pwm_regs.dc_resn + 1)]};
    }
    foreach (pwm_regs.blink_param_x[i]) {
      pwm_regs.blink_param_x[i] inside {[cfg.seq_cfg.pwm_min_param : cfg.seq_cfg.pwm_max_param]};
    }
    foreach (pwm_regs.blink_param_y[i]) {
      pwm_regs.blink_param_y[i] inside {[cfg.seq_cfg.pwm_min_param : cfg.seq_cfg.pwm_max_param]};
    }
    foreach (pwm_regs.duty_cycle_a[i]) {
      pwm_regs.duty_cycle_a[i] inside {[1 : 2 ** (pwm_regs.dc_resn + 1) - 1]};
    }
    foreach (pwm_regs.duty_cycle_b[i]) {
      pwm_regs.duty_cycle_b[i] inside {[1 : 2 ** (pwm_regs.dc_resn + 1) - 1]};
    }
  }

  //================================
  virtual task pre_start();
    num_runs.rand_mode(0);
    // unset to disable intr test because pwm does not have intr pins
    do_clear_all_interrupts = 1'b0;
    super.pre_start();
  endtask : pre_start

  virtual task initialize_pwm();
    wait(cfg.clk_rst_vif.rst_n && cfg.clk_rst_core_vif.rst_n);
    `uvm_info(`gfn, "\n  base_vseq: out of reset", UVM_DEBUG)
    csr_spinwait(.ptr(ral.regen), .exp_data(1'b1));
    program_pwm_enb_regs(Disable);
    program_pwm_cnt_regs(Disable);
    `uvm_info(`gfn, "\n  base_vseq: clear regen to enable register program", UVM_DEBUG)
    `uvm_info(`gfn, "\n--> INITIALIZATION is finished", UVM_LOW)
  endtask : initialize_pwm

  virtual task start_pwm_channels();
    update_pwm_monitor_cfg();
    cfg.num_pulses = num_pulses;
    program_pwm_enb_regs(Enable);
    program_pwm_inv_regs(Enable);
    program_pwm_cnt_regs(Enable);
    cfg.m_pwm_monitor_cfg.print_pwm_monitor_cfg(.en_print(1'b0));
    `uvm_info(`gfn, $sformatf("\n  base_vseq: start channels (%b)", pwm_regs.pwm_en), UVM_DEBUG)
  endtask : start_pwm_channels

  virtual task run_pwm_channels();
    int runtime = cfg.num_pulses * pwm_regs.pulse_cycle * pwm_regs.beat_cycle;
    `DV_CHECK_NE(runtime, 0)
    cfg.clk_rst_core_vif.wait_clks(runtime);
    foreach (pwm_regs.pwm_en[i]) begin
      if (pwm_regs.pwm_en[i]) begin
        `uvm_info(`gfn, $sformatf(
                  "\n  base_vseq: generate %0d pulse in channel %0d", cfg.num_pulses, i), UVM_DEBUG)
      end
    end
    // disable channels and clear phase counter
    program_pwm_cnt_regs(Disable);
    program_pwm_enb_regs(Disable);
    program_pwm_inv_regs(Disable);
  endtask : run_pwm_channels

  // clear regen after initialization to allow programming registers
  virtual task program_pwm_regen_reg(pwm_status_e status = Enable);
    csr_wr(.ptr(ral.regen), .value(status));
    `uvm_info(`gfn, $sformatf("\n  base_vseq: program regen %s", status.name()), UVM_DEBUG)
  endtask : program_pwm_regen_reg

  virtual task program_pwm_cfg_regs();
    // derived params
    `uvm_info(`gfn, $sformatf(
              "\n  base_vseq: clk_div %0d and dc_resn %0d ", pwm_regs.clk_div, pwm_regs.dc_resn),
              UVM_DEBUG)
    pwm_regs.beat_cycle  = pwm_regs.clk_div + 1;
    pwm_regs.pulse_cycle = 2 ** (pwm_regs.dc_resn + 1);
    ral.cfg.clk_div.set(pwm_regs.clk_div);
    ral.cfg.dc_resn.set(pwm_regs.dc_resn);
    csr_update(ral.cfg);
  endtask : program_pwm_cfg_regs

  virtual task program_pwm_cnt_regs(pwm_status_e status = Enable);
    pwm_regs.cntr_en = (status == Enable);
    ral.cfg.cntr_en.set(pwm_regs.cntr_en);
    csr_update(ral.cfg);
    csr_spinwait(.ptr(ral.cfg.cntr_en), .exp_data(pwm_regs.cntr_en));
    cfg.m_pwm_monitor_cfg.cntr_en = pwm_regs.cntr_en;
    `uvm_info(`gfn, $sformatf(
              "\n  base_vseq: phase counters %s", pwm_regs.cntr_en ? "enable" : "clear"), UVM_DEBUG)
  endtask : program_pwm_cnt_regs

  virtual task program_pwm_enb_regs(pwm_status_e status = Enable);
    if (status == Enable) begin
      csr_wr(.ptr(ral.pwm_en), .value(pwm_regs.pwm_en));
    end else begin
      pwm_regs.pwm_en = '0;
      csr_wr(.ptr(ral.pwm_en), .value(pwm_regs.pwm_en));
      // wait one cycle before disable channels to let last pulses completed
      cfg.clk_rst_core_vif.wait_clks(1);
    end
    csr_spinwait(.ptr(ral.pwm_en), .exp_data(pwm_regs.pwm_en));
    cfg.m_pwm_monitor_cfg.pwm_en = pwm_regs.pwm_en;
    `uvm_info(`gfn, $sformatf("\n  base_vseq: %pwm_en %b", pwm_regs.pwm_en), UVM_DEBUG)
  endtask : program_pwm_enb_regs

  virtual task program_pwm_inv_regs(pwm_status_e status = Enable);
    if (status == Disable) begin
      pwm_regs.invert = '0;
    end
    csr_wr(.ptr(ral.invert), .value(pwm_regs.invert));
    cfg.m_pwm_monitor_cfg.invert = pwm_regs.invert;
    `uvm_info(`gfn, $sformatf("\n  base_vseq: pwm_invert %b", pwm_regs.invert), UVM_DEBUG)
  endtask : program_pwm_inv_regs

  virtual task program_pwm_duty_cycle_regs(int channel);
    dv_base_reg base_reg = get_dv_base_reg_by_name("duty_cycle", channel);
    // set reg fields but not update
    set_dv_base_reg_field_by_name("duty_cycle", "a", pwm_regs.duty_cycle_a[channel], channel,
                                  channel, 1'b0);
    set_dv_base_reg_field_by_name("duty_cycle", "b", pwm_regs.duty_cycle_b[channel], channel,
                                  channel, 1'b0);
    // update fields in same cycle
    csr_update(base_reg);
  endtask : program_pwm_duty_cycle_regs

  virtual task program_pwm_blink_param_regs(int channel);
    dv_base_reg base_reg = get_dv_base_reg_by_name("blink_param", channel);
    // set reg fields but not update
    set_dv_base_reg_field_by_name("blink_param", "x", pwm_regs.blink_param_x[channel], channel,
                                  channel, 1'b0);
    set_dv_base_reg_field_by_name("blink_param", "y", pwm_regs.blink_param_y[channel], channel,
                                  channel, 1'b0);
    // update fields in same cycle
    csr_update(base_reg);
  endtask : program_pwm_blink_param_regs

  // update pwm_monitor_config
  virtual function void update_pwm_monitor_cfg();
    cfg.m_pwm_monitor_cfg.num_pulses    = num_pulses;
    cfg.m_pwm_monitor_cfg.duty_cycle_a  = pwm_regs.duty_cycle_a;
    cfg.m_pwm_monitor_cfg.duty_cycle_b  = pwm_regs.duty_cycle_b;
    cfg.m_pwm_monitor_cfg.blink_param_x = pwm_regs.blink_param_x;
    cfg.m_pwm_monitor_cfg.blink_param_y = pwm_regs.blink_param_y;
    cfg.m_pwm_monitor_cfg.phase_delay   = pwm_regs.phase_delay;
    cfg.m_pwm_monitor_cfg.invert        = pwm_regs.invert;
    cfg.m_pwm_monitor_cfg.pwm_mode      = pwm_regs.pwm_mode;
    cfg.m_pwm_monitor_cfg.phase_delay   = pwm_regs.phase_delay;
    cfg.m_pwm_monitor_cfg.pulse_cycle   = pwm_regs.pulse_cycle;
    cfg.print_all_channel_cfg("base_vseq", pwm_regs, 1'b0);
  endfunction : update_pwm_monitor_cfg

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

  virtual task apply_resets_concurrently(int reset_duration_ps = 0);
    cfg.clk_rst_core_vif.drive_rst_pin(0);
    super.apply_resets_concurrently(cfg.clk_rst_core_vif.clk_period_ps);
    cfg.clk_rst_core_vif.drive_rst_pin(1);
  endtask

  // phase alignment for resets signal of core and bus domain
  virtual task do_phase_align_reset(bit do_phase_align = 1'b0);
    if (do_phase_align) begin
      fork
        cfg.clk_rst_vif.wait_clks($urandom_range(5, 10));
        cfg.clk_rst_core_vif.wait_clks($urandom_range(5, 10));
      join
    end
  endtask : do_phase_align_reset

  // set field of reg/mreg using name and index, need to call csr_update after setting
  virtual task set_dv_base_reg_field_by_name(string csr_name, string field_name, uint field_value,
                                             int field_idx = -1, int csr_idx = -1,
                                             bit update = 1'b1);
    string        reg_name;
    uvm_reg_field reg_field;
    dv_base_reg   base_reg;

    base_reg  = get_dv_base_reg_by_name(csr_name, csr_idx);
    reg_name  = (field_idx == -1) ? field_name : $sformatf("%s_%0d", field_name, field_idx);
    reg_field = base_reg.get_field_by_name(reg_name);
    `DV_CHECK_NE_FATAL(reg_field, null, reg_name)
    reg_field.set(field_value);
    if (update) csr_update(base_reg);
    `uvm_info(`gfn, $sformatf("base_vseq: set register %s.%s", csr_name, field_name), UVM_DEBUG)
  endtask : set_dv_base_reg_field_by_name

  // set reg/mreg using name and index
  virtual function dv_base_reg get_dv_base_reg_by_name(string csr_name, int csr_idx = -1);
    string  reg_name;
    uvm_reg reg_uvm;

    reg_name = (csr_idx == -1) ? csr_name : $sformatf("%s_%0d", csr_name, csr_idx);
    reg_uvm  = ral.get_reg_by_name(reg_name);
    `DV_CHECK_NE_FATAL(reg_uvm, null, reg_name)
    `downcast(get_dv_base_reg_by_name, reg_uvm)
  endfunction : get_dv_base_reg_by_name

endclass : pwm_base_vseq
