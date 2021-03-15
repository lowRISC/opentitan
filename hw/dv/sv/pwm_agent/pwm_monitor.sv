// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_monitor extends dv_base_monitor #(
    .ITEM_T (pwm_item),
    .CFG_T  (pwm_agent_cfg),
    .COV_T  (pwm_agent_cov)
  );
  `uvm_component_utils(pwm_monitor)

  // the base class provides the following handles for use:
  // pwm_agent_cfg: cfg
  // pwm_agent_cov: cov

  uvm_analysis_port #(pwm_item) item_port[NUM_PWM_CHANNELS];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    for (uint i = 0; i < NUM_PWM_CHANNELS; i++) begin
      item_port[i] = new($sformatf("item_port[%0d]", i), this);
    end
  endfunction

  task run_phase(uvm_phase phase);
    wait(cfg.vif.rst_core_n);
    // TODO
    super.run_phase(phase);
  endtask : run_phase

  // collect transactions forever - already forked in dv_base_moditor::run_phase
  virtual protected task collect_trans(uvm_phase phase);
    forever begin
      // TODO: detect event

      // TODO: sample the interface

      // TODO: sample the covergroups

      // TODO: write trans to analysis_port

      // TODO: remove the line below: it is added to prevent zero delay loop in template code
      #1us;
    end
  endtask

  // update of_to_end to prevent sim finished when there is any activity on the bus
  // ok_to_end = 0 (bus busy) / 1 (bus idle)
  virtual task monitor_ready_to_end();
    forever begin
      @(cfg.vif.pwm_en, cfg.vif.pwm);
      ok_to_end = (cfg.vif.pwm_en === {NUM_PWM_CHANNELS{1'b0}}) &&
                  (cfg.vif.pwm === {NUM_PWM_CHANNELS{1'b0}});
    end
  endtask : monitor_ready_to_end

endclass : pwm_monitor
