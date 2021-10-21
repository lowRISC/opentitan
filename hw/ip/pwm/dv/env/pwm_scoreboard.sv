// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_scoreboard extends cip_base_scoreboard #(
    .CFG_T(pwm_env_cfg),
    .RAL_T(pwm_reg_block),
    .COV_T(pwm_env_cov)
  );
  `uvm_component_utils(pwm_scoreboard)
  `uvm_component_new

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(pwm_item) item_fifo[PWM_NUM_CHANNELS];

  local pwm_regs_t pwm_regs;
  local pwm_item   exp_item_q[PWM_NUM_CHANNELS][$];

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    for (int i = 0; i < PWM_NUM_CHANNELS; i++) begin
      item_fifo[i] = new($sformatf("item_fifo[%0d]", i), this);
    end
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    forever begin
      `DV_SPINWAIT_EXIT(
        for (int i = 0; i < PWM_NUM_CHANNELS; i++) begin
          fork
            automatic int channel = i;
            compare_trans(channel);
          join_none
        end
        wait fork;,
        @(negedge cfg.clk_rst_vif.rst_n),
      )
    end
  endtask : run_phase

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit [TL_DW-1:0] reg_value;
    bit do_read_check = 1'b1;
    bit write = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    bit addr_phase_write = (write && channel  == AddrChannel);
    bit data_phase_read  = (!write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end
    else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    if (addr_phase_write) begin
      string csr_name = csr.get_name();

      // if incoming access is a write to a valid csr, then make updates right away
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));

      // process the csr req
      // for write, update local variable and fifo at address phase
      // for read, update predication at address phase and compare at data phase
      case (csr_name)
        "pwm_en": begin
          pwm_regs.pwm_en = ral.pwm_en.get_mirrored_value();
          `uvm_info(`gfn, $sformatf("\n  scb: pwm_en %b", pwm_regs.pwm_en), UVM_DEBUG)
        end
        "cfg": begin
          reg_value = ral.cfg.get_mirrored_value();
          pwm_regs.clk_div = get_field_val(ral.cfg.clk_div, reg_value);
          pwm_regs.dc_resn = get_field_val(ral.cfg.dc_resn, reg_value);
          pwm_regs.cntr_en = get_field_val(ral.cfg.cntr_en, reg_value);
          pwm_regs.beat_cycle  = pwm_regs.clk_div + 1;
          pwm_regs.pulse_cycle = 2**(pwm_regs.dc_resn + 1);
          for (int channel = 0; channel < PWM_NUM_CHANNELS; channel++) begin
            cfg.print_channel_cfg("scb", pwm_regs, channel, 1'b0);
            generate_exp_items(channel);
          end
        end
        "invert": begin
          pwm_regs.invert = ral.invert.get_mirrored_value();
          `uvm_info(`gfn, $sformatf("\n  scb: channels invert %b", pwm_regs.invert), UVM_DEBUG)
        end
        "pwm_param_0", "pwm_param_1", "pwm_param_2",
        "pwm_param_3", "pwm_param_4", "pwm_param_5": begin
          int channel = get_reg_index(csr_name, 10);
          pwm_regs.blink_en[channel] = bit'(get_field_val(ral.pwm_param_0.blink_en_0, item.a_data));
          pwm_regs.htbt_en[channel] = bit'(get_field_val(ral.pwm_param_0.htbt_en_0, item.a_data));
          pwm_regs.phase_delay[channel] = get_field_val(ral.pwm_param_0.phase_delay_0, item.a_data);
          pwm_regs.pwm_mode[channel] = get_pwm_mode({pwm_regs.blink_en[channel],
                                                     pwm_regs.htbt_en[channel]});
          `uvm_info(`gfn, $sformatf("\n  scb: channel %0d, data %b, pwm_mode %s, phase_delay %0d",
              channel, item.a_data, pwm_regs.pwm_mode[channel].name(),
              pwm_regs.phase_delay[channel]), UVM_DEBUG)
        end
        "duty_cycle_0", "duty_cycle_1", "duty_cycle_2",
        "duty_cycle_3", "duty_cycle_4", "duty_cycle_5": begin
          int channel = get_reg_index(csr_name, 11);
          {pwm_regs.duty_cycle_b[channel], pwm_regs.duty_cycle_a[channel]} = item.a_data;
          `uvm_info(`gfn, $sformatf("\n  scb: channel %0d, duty_cycle_b %0d, duty_cycle_a %0d",
              channel, pwm_regs.duty_cycle_b[channel], pwm_regs.duty_cycle_a[channel]), UVM_DEBUG)
        end
        "blink_param_0", "blink_param_1", "blink_param_2",
        "blink_param_3", "blink_param_4", "blink_param_5": begin
          int channel = get_reg_index(csr_name, 12);
          {pwm_regs.blink_param_y[channel], pwm_regs.blink_param_x[channel]} = item.a_data;
          `uvm_info(`gfn, $sformatf("\n  scb: channel %0d, blink_param_y %0d, blink_param_x %0d",
              channel, pwm_regs.blink_param_y[channel],
              pwm_regs.blink_param_x[channel]), UVM_DEBUG)
        end
        default: begin
          `uvm_fatal(`gfn, $sformatf("\n  scb: invalid csr: %0s", csr.get_full_name()))
        end
      endcase
    end

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  virtual task compare_trans(int channel);
    pwm_item exp_item;
    pwm_item dut_item;

    forever begin
      item_fifo[channel].get(dut_item);
      wait(exp_item_q[channel].size() > 0);
      exp_item = exp_item_q[channel].pop_front();

      if (!dut_item.compare(exp_item)) begin
        //cfg.print_channel_regs("scb", pwm_regs, channel);
        `uvm_error(`gfn, $sformatf("\n--> channel %0d item mismatch!\n--> EXP:\n%s\--> DUT:\n%s",
            channel, exp_item.sprint(), dut_item.sprint()))
      end else begin
        `uvm_info(`gfn, $sformatf("\n--> channel %0d item match!\n--> EXP:\n%s\--> DUT:\n%s",
            channel, exp_item.sprint(), dut_item.sprint()), UVM_DEBUG)
      end
    end
  endtask : compare_trans

  virtual function void generate_exp_items(uint channel);
    uint beat_cycle  = uint'(pwm_regs.beat_cycle);
    uint pulse_cycle = uint'(pwm_regs.pulse_cycle);

    if (pwm_regs.pwm_en[channel] && pwm_regs.cntr_en) begin
      for (int pulse_index = 1; pulse_index <= cfg.num_pulses; pulse_index++) begin
        bit get_exp_item = 1'b0;
        pwm_item exp_item = pwm_item::type_id::create("exp_item");

        exp_item.index = pulse_index;
        unique case (pwm_regs.pwm_mode[channel])
          Heartbeat: begin
            // TODO: get the duty_cycle for the Heartbeat mode
          end
          Blinking: begin
            // TODO: get the duty_cycle for the Blinking mode
          end
          Standard: begin  // Standard mode
            // pulse_duty depends on duty_cycle_a is only
            exp_item.duty_high = pwm_regs.beat_cycle *
                                 (pwm_regs.duty_cycle_a[channel] % pwm_regs.pulse_cycle);
            exp_item.duty_low  = pwm_regs.beat_cycle * pwm_regs.pulse_cycle - exp_item.duty_high;

            `uvm_info(`gfn, $sformatf("\n  scb: channel %0d duty_a %0d, pulse_cyc %0d, duty_high %0d",
                channel, pwm_regs.duty_cycle_a[channel], pwm_regs.pulse_cycle, exp_item.duty_high), UVM_DEBUG)
            // if invert bit is set, swap duty_high and duty_low since pulses are inverted
            if (pwm_regs.invert[channel]) begin
              int temp = exp_item.duty_high;
              exp_item.duty_high = exp_item.duty_low;
              exp_item.duty_low = temp;
            end
            get_exp_item = (exp_item.index < cfg.num_pulses);
          end
        endcase
        if (get_exp_item) begin
          exp_item_q[channel].push_back(exp_item);
          `uvm_info(`gfn, $sformatf("\n--> scb: get exp_item for channel %0d\n%s",
              channel, exp_item.sprint()), UVM_DEBUG)
        end
      end
    end
  endfunction : generate_exp_items

  virtual function int get_reg_index(string csr_name, int pos);
    return csr_name.substr(pos, pos).atoi();
  endfunction : get_reg_index

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    for (int i = 0; i < PWM_NUM_CHANNELS; i++) begin
      item_fifo[i].flush();
      exp_item_q[i].delete();
    end
  endfunction

  virtual function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    for (int i = 0; i < PWM_NUM_CHANNELS; i++) begin
      `DV_EOT_PRINT_Q_CONTENTS(pwm_item, exp_item_q[i])
      `DV_EOT_PRINT_TLM_FIFO_CONTENTS(pwm_item, item_fifo[i])
    end
  endfunction

endclass : pwm_scoreboard