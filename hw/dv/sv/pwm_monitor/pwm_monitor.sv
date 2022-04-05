// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_monitor extends dv_base_monitor #(
    .ITEM_T (pwm_item),
    .CFG_T  (pwm_monitor_cfg)
  );
  `uvm_component_utils(pwm_monitor)

  // the base class provides the following handles for use:
//  pwm_monitor_cfg cfg;

  uvm_analysis_port #(pwm_item) item_port;

  //item
  pwm_item dut_item, item_clone;

  // interface handle
  virtual pwm_if vif;

  bit [15:0] clk_cnt          = '0;
  bit        prev_pwm_state   =  0;
  bit [15:0] cnt              =  0;

//  `uvm_component_new
  function new(string name, uvm_component parent);
    super.new(name, parent);
  endfunction


  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    item_port = new($sformatf("%s_item_port", this.get_name()), this);
    // get interface
    if (!uvm_config_db#(virtual pwm_if)::get(this, "*.env.m_pwm_monitor*",
                        $sformatf("%s_vif", get_name()), vif)) begin
      `uvm_fatal(`gfn, $sformatf("\n  mon: failed to get %s_vif handle from uvm_config_db",
                get_name()))
    end

    // get config
    if (!uvm_config_db#(pwm_monitor_cfg)::get(this, "*", $sformatf("%s_cfg", get_name()),cfg)) begin
      `uvm_fatal(`gfn, $sformatf("\n  mon: failed to get %s_cfg from uvm_config_db", get_name()))
    end
  endfunction

  // collect transactions forever - already forked in dv_base_monitor::run_phase
  virtual protected task collect_trans(uvm_phase phase);
    wait(vif.rst_n);
    `uvm_info(`gfn, $sformatf("getting delay %d", cfg.ok_to_end_delay_ns), UVM_HIGH)
    dut_item = pwm_item::type_id::create($sformatf("%s_item", this.get_name()));

    forever begin

      @(vif.cb);
      // always count the clock to get phase right
      clk_cnt += 1;
      if (cfg.active) begin
        if (cnt == 0) begin
        end

        // increment high/low cnt
        cnt     += 1;
        // detect event
        if (vif.cb.pwm != prev_pwm_state) begin
          `uvm_info(`gfn, $sformatf("edge detected %0b -> %0b", prev_pwm_state, vif.cb.pwm),
                     UVM_HIGH)
          if (vif.cb.pwm == cfg.invert) begin
            // store count in high count
            dut_item.active_cnt  = cnt;
          end else begin
            dut_item.inactive_cnt  = cnt;
            dut_item.phase         = 2**clk_cnt;
            dut_item.invert        = cfg.invert;
            dut_item.period        = cnt + dut_item.active_cnt;
            dut_item.monitor_id    = cfg.monitor_id;
            // item done
            `downcast(item_clone, dut_item.clone());
            item_port.write(item_clone);
            dut_item = new();
          end
          cnt = 0;
        end
        prev_pwm_state = vif.cb.pwm;
      end else begin
        // clear what was previously collected
        dut_item = new();
        cnt      = 0;
      end
    end
  endtask

  // update of_to_end to prevent sim finished when there is any activity on the bus
  // ok_to_end = 0 (bus busy) / 1 (bus idle)
  virtual task monitor_ready_to_end();
    forever begin
      @(vif.cb)
      ok_to_end = ~cfg.active;
    end
  endtask : monitor_ready_to_end

endclass : pwm_monitor
