// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_monitor extends dv_base_monitor #(
    .ITEM_T (pwm_item),
    .CFG_T  (pwm_monitor_cfg)
  );
  `uvm_component_utils(pwm_monitor)

  extern function new(string name = "", uvm_component parent = null);
  extern function void build_phase(uvm_phase phase);

  // collect transactions forever - already forked in dv_base_monitor::run_phase
  extern protected task collect_trans();

  extern task monitor_ready_to_end();
endclass

function pwm_monitor::new(string name = "", uvm_component parent = null);
  super.new(name, parent);
endfunction


function void pwm_monitor::build_phase(uvm_phase phase);
  super.build_phase(phase);
  // get config
  if (!uvm_config_db#(pwm_monitor_cfg)::get(this, "", "cfg", cfg)) begin
    `uvm_fatal(`gfn, $sformatf("failed to get cfg from uvm_config_db"))
  end

  // get interface
  if (!uvm_config_db#(virtual pwm_if)::get(this, "", "vif", cfg.vif)) begin
    `uvm_fatal(`gfn, $sformatf("failed to get vif handle from uvm_config_db"))
  end
endfunction

task pwm_monitor::collect_trans();
  uint count_cycles, active_cycles;
  logic pwm_prev = 0;

  wait(cfg.vif.rst_n);
  forever begin
    if (!cfg.active) begin
      wait (cfg.active);
      count_cycles = 0;
      active_cycles = 0;
    end

    @(cfg.vif.cb);
    count_cycles++;
    if (cfg.vif.cb.pwm != pwm_prev) begin
      `uvm_info(`gfn, $sformatf("Detected edge: %0b->%0b at %0d cycles (from last edge)",
                                pwm_prev, cfg.vif.cb.pwm, count_cycles), UVM_HIGH)
      pwm_prev = cfg.vif.cb.pwm;
      if (cfg.vif.cb.pwm == cfg.invert) begin
        // We got to the first (active) half duty cycle point. Save the count and restart.
        active_cycles = count_cycles;
      end else begin
        uint phase_count;
        pwm_item item = pwm_item::type_id::create("item");
        item.invert       = cfg.invert;
        item.monitor_id   = cfg.monitor_id;
        item.active_cnt   = active_cycles;
        item.inactive_cnt = count_cycles;
        item.period       = count_cycles + active_cycles;
        item.duty_cycle   = item.get_duty_cycle();

        // Each PWM pulse cycle is divided into 2^DC_RESN+1 beats, per beat the 16-bit
        // phase counter increments by 2^(16-DC_RESN-1)(modulo 65536)
        phase_count = ((item.period / (2 ** (cfg.resolution + 1))) *
                       (2 ** (16 - (cfg.resolution - 1))));
        item.phase = (phase_count % 65536);
        analysis_port.write(item);
      end
      count_cycles = 0;
    end
  end
endtask

// update of_to_end to prevent sim finished when there is any activity on the bus
// ok_to_end = 0 (bus busy) / 1 (bus idle)
task pwm_monitor::monitor_ready_to_end();
  forever begin
    @(cfg.vif.cb);
    ok_to_end = ~cfg.active;
  end
endtask
