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

  // Return true if we are currently in the active phase (the first half) of a transaction.
  extern function bit is_active();

  // Collect transactions forever whenever rst_n is high and cfg.active is true.
  extern protected task collect_trans();

  // Collect a single transaction. This is called in a loop by collect_trans and is safe to kill at
  // any time.
  extern protected task collect_transaction();

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

function bit pwm_monitor::is_active();
  // The active phase is the first part of the transaction. If invert is false, pwm is true for that
  // time.
  return cfg.vif.cb.pwm == !cfg.invert;
endfunction

task pwm_monitor::collect_trans();
  forever begin
    wait(cfg.vif.rst_n && cfg.active);
    fork begin : isolation_fork
      fork
        wait(!(cfg.vif.rst_n && cfg.active));
        forever collect_transaction();
      join_any
      disable fork;
    end join
  end
endtask

task pwm_monitor::collect_transaction();
  uint active_cycles = 0, inactive_cycles = 0;

  // Wait until the pwm signal is the 'active' value (marking the start of the first phase of the
  // transaction).
  while (!is_active()) @(cfg.vif.cb);

  // Measure the amount of time we are active measure how many cycles we were active.
  while (is_active()) begin
    active_cycles++;
    @(cfg.vif.cb);
  end

  // Finally, wait until the pwm signal becomes the 'active' value again, incrementing
  // inactive_cycles to measure how many cycles we were inactive.
  while (!is_active()) begin
    inactive_cycles++;
    @(cfg.vif.cb);
  end

  // At this point, we've just finished the first cycle of the active phase of the next transaction,
  // which will be counted correctly if we start collect_transaction again before any more time
  // elapses. Report the transaction that we have measured through the analysis port.
  begin
    uint phase_count;
    pwm_item item = pwm_item::type_id::create("item");
    item.invert       = cfg.invert;
    item.active_cnt   = active_cycles;
    item.inactive_cnt = inactive_cycles;
    item.period       = inactive_cycles + active_cycles;
    item.duty_cycle   = item.get_duty_cycle();

    // Each PWM pulse cycle is divided into 2^DC_RESN+1 beats, per beat the 16-bit
    // phase counter increments by 2^(16-DC_RESN-1)(modulo 65536)
    phase_count = ((item.period / (2 ** (cfg.resolution + 1))) *
                   (2 ** (16 - (cfg.resolution - 1))));
    item.phase = (phase_count % 65536);
    analysis_port.write(item);
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
