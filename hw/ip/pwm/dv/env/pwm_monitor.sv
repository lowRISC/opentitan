// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_monitor extends dv_base_monitor #(
  .CFG_T  (pwm_env_cfg),
  .COV_T  (pwm_env_cov),
  .ITEM_T (pwm_item)
);

  `uvm_component_utils(pwm_monitor)
  `uvm_component_new

  uvm_analysis_port #(pwm_item) item_port[PWM_NUM_CHANNELS];
  bit reset_asserted = 1'b0;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    for (uint i = 0; i < PWM_NUM_CHANNELS; i++) begin
      item_port[i] = new($sformatf("item_port[%0d]", i), this);
    end
  endfunction

  task run_phase(uvm_phase phase);
    wait(cfg.pwm_vif.rst_core_n);
    collect_trans(phase);
  endtask : run_phase

  virtual protected task collect_trans(uvm_phase phase);
    fork
      for (uint i = 0; i < PWM_NUM_CHANNELS; i++) begin
        fork
          automatic uint channel = i;
          collect_channel_trans(channel);
        join_none
      end
      reset_thread();
    join
  endtask : collect_trans

  virtual task collect_channel_trans(int channel);
    pwm_item dut_item;
    bit high_duty, low_duty;

    forever begin
      wait(cfg.en_monitor);
      dut_item = pwm_item::type_id::create("dut_item");
      dut_item.reset();
      fork
        begin : isolation_thread
          fork
            // calculate pulse duty
            begin
              @(posedge cfg.pwm_vif.pwm_en[channel]);
              `uvm_info(`gfn, "\n  monitor: get the posedge of pwm_en", UVM_DEBUG)
              @(negedge cfg.pwm_vif.clk_core); // phase shift to avoid hardzard
              `uvm_info(`gfn, "\n  monitor: phase shift to negedge clk_core ", UVM_DEBUG)
              while (cfg.pwm_vif.pwm_en[channel]) begin
                dut_item.en_cycles++;
                high_duty = !cfg.invert[channel] && cfg.pwm_vif.pwm[channel];
                low_duty  = cfg.invert[channel] && !cfg.pwm_vif.pwm[channel];
                if (high_duty || low_duty) begin
                  dut_item.duty_cycle++;
                end
                `uvm_info(`gfn, $sformatf("\n  monitor: counting en_cycles/duty_cycle %0d/%0d",
                    dut_item.en_cycles, dut_item.duty_cycle), UVM_DEBUG)
                @(negedge cfg.pwm_vif.clk_core);
              end
              item_port[channel].write(dut_item);
              `uvm_info(`gfn, $sformatf("\n--> monitor: send dut_item for channel %0d\n%s",
                  channel, dut_item.sprint()), UVM_DEBUG)
            end
            // handle reset
            @(posedge reset_asserted);
          join_any
          disable fork;
        end : isolation_thread
      join
    end
  endtask : collect_channel_trans

  virtual task reset_thread();
    forever begin
      @(negedge cfg.pwm_vif.rst_core_n);
      reset_asserted = 1'b1;
      @(posedge cfg.pwm_vif.rst_core_n);
      reset_asserted = 1'b0;
    end
  endtask : reset_thread

  // update of_to_end to prevent sim finished when there is any activity on the bus
  // ok_to_end = 0 (bus busy) / 1 (bus idle)
  virtual task monitor_ready_to_end();
    forever begin
      @(cfg.pwm_vif.pwm_en);
      ok_to_end = (cfg.pwm_vif.pwm_en === {PWM_NUM_CHANNELS{1'b0}});
    end
  endtask : monitor_ready_to_end

endclass : pwm_monitor
