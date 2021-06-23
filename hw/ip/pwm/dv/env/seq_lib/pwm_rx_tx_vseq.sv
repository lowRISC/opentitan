// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_rx_tx_vseq extends pwm_base_vseq;
  `uvm_object_utils(pwm_rx_tx_vseq)
  `uvm_object_new

  virtual task body();
    `uvm_info(`gfn, "\n--> Start body task", UVM_DEBUG)
    `uvm_info(`gfn, $sformatf("\n--> SIMULATE %0d transactions", num_trans), UVM_DEBUG)
    initialize_pwm();
    for (int i = 0; i < num_trans; i++) begin
      `uvm_info(`gfn, $sformatf("\n\n--> start transaction %0d/%0d", i + 1, num_trans), UVM_LOW)
      `DV_CHECK_RANDOMIZE_FATAL(this)
      // program single registers out of the loop
      wait(!cfg.under_reset);
      program_pwm_cfg_regs();
      // program multi registers
      program_pwm_mode_regs();
      start_pwm_channels();   // start channels
      run_pwm_channels();     // run then stop channels
      `uvm_info(`gfn, $sformatf("\n--> finish transaction %0d/%0d\n", i + 1, num_trans), UVM_LOW)
    end
    `uvm_info(`gfn, "\n--> Finish body task", UVM_DEBUG)
  endtask : body

  // program pwm mode (including programming duty_cycle and pwm_param multiregs)
  virtual task program_pwm_mode_regs();
    for (int channel = 0; channel < PWM_NUM_CHANNELS; channel++) begin
      if (pwm_regs.pwm_en[channel] == Enable) begin
        dv_base_reg base_reg;

        // program duty_cycle_a and duty_cycle_b in same cycle
        program_pwm_duty_cycle_regs(channel);
        // program blink_param_x and blink_param_y in same cycle
        program_pwm_blink_param_regs(channel);

        `uvm_info(`gfn, $sformatf("\n  rxtx_vseq: program pwm_param[%0d] to mode %s",
            channel, pwm_regs.pwm_mode[channel].name()), UVM_DEBUG)
        base_reg = get_dv_base_reg_by_name("pwm_param", channel);
        // program pwm_mode
        `uvm_info(`gfn, $sformatf("\n  rxtx_vseq: programm channel %0d to mode %s",
            channel, pwm_regs.pwm_mode[channel].name()), UVM_DEBUG)
        case (pwm_regs.pwm_mode[channel])
          Blinking: begin
            // enable blink_en, disable htbt_en in same cycle
            set_dv_base_reg_field_by_name("pwm_param", "blink_en", Enable,  channel, channel, 1'b0);
            set_dv_base_reg_field_by_name("pwm_param", "htbt_en",  Disable, channel, channel, 1'b0);
          end
          Heartbeat: begin
            // enable both blink_en and htbt_en in same cycle
            set_dv_base_reg_field_by_name("pwm_param", "blink_en", Enable, channel, channel, 1'b0);
            set_dv_base_reg_field_by_name("pwm_param", "htbt_en",  Enable, channel, channel, 1'b0);
            csr_update(base_reg);
          end
          Standard: begin
            // disable both blink_en and htbt_en in same cycle
            set_dv_base_reg_field_by_name("pwm_param", "blink_en", Disable, channel, channel, 1'b0);
            set_dv_base_reg_field_by_name("pwm_param", "htbt_en",  Disable, channel, channel, 1'b0);
          end
        endcase
        // program phase delay
        cfg.num_pulses = num_pulses;
        set_dv_base_reg_field_by_name("pwm_param", "phase_delay",
            pwm_regs.phase_delay[channel], channel, channel, 1'b0);
        // update pwm_param register
        csr_update(base_reg);
        `uvm_info(`gfn, $sformatf("\n  rxtx_vseq: update pwm_mode_regs[%0d]", channel), UVM_DEBUG)
      end
    end
  endtask : program_pwm_mode_regs

endclass : pwm_rx_tx_vseq