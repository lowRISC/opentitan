// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_monitor #(
  parameter int NumPwmChannels = 6
) extends dv_base_monitor #(
  .CFG_T  (pwm_monitor_cfg#(NumPwmChannels)),
  .ITEM_T (pwm_item)
);

  `uvm_component_param_utils(pwm_monitor#(NumPwmChannels))
  `uvm_component_new

  uvm_analysis_port #(pwm_item) item_port[NumPwmChannels];
  local bit reset_asserted = 1'b0;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    for (uint i = 0; i < NumPwmChannels; i++) begin
      item_port[i] = new($sformatf("item_port[%0d]", i), this);
    end
    // get vif handle
    if (!uvm_config_db#(virtual pwm_if#(NumPwmChannels))::get(this, "", "vif", cfg.vif)) begin
      `uvm_fatal(`gfn, "\n  mon: failed to get vif handle from uvm_config_db")
    end
  endfunction : build_phase

  task run_phase(uvm_phase phase);
    wait(cfg.vif.rst_n);
    collect_trans(phase);
  endtask : run_phase

  virtual protected task collect_trans(uvm_phase phase);
    fork
      for (uint i = 0; i < NumPwmChannels; i++) begin
        fork
          automatic uint channel = i;
          collect_channel_trans(channel);
        join_none
      end
      reset_thread();
    join
  endtask : collect_trans

  virtual task collect_channel_trans(int channel);
    pwm_item item;
    bit channel_start =1'b0;
    int item_index;

    forever begin
      wait(cfg.en_monitor);
      item = pwm_item::type_id::create("mon_item");
      fork
        begin : isolation_thread
          fork
            // channel start
            begin
              channel_start = 1'b0;
              @(posedge cfg.vif.clk && cfg.pwm_en[channel] && cfg.cntr_en);
              item_index = 0;
              `uvm_info(`gfn, $sformatf("\n  mon: channel %0d is enabled", channel), UVM_HIGH)
              // ignore the first pulse since the first pulse can be incompletely generated
              get_pulse_edge(channel);
              `uvm_info(`gfn, $sformatf("\n  mon: channel %0d: ignore the first edge",
                  channel), UVM_HIGH)
              #1ps; // let duty_cycle_counting thread start after the first edge
              channel_start = 1'b1;
              fork
                begin : duty_cycle_counting
                  `uvm_info(`gfn, $sformatf("\n  mon: channel %0d: start capturing pulses",
                      channel), UVM_HIGH)
                  // calculate pulse duty
                  while (cfg.pwm_en[channel]) begin
                    // use negedge for counting duty to avoid metastability with posedge
                    @(negedge cfg.vif.clk);
                    item.duty_high += (cfg.vif.pwm[channel] == 1'b1);
                    item.duty_low  += (cfg.vif.pwm[channel] == 1'b0);
                  end : duty_cycle_counting
                  channel_start = 1'b0;
                  `uvm_info(`gfn, $sformatf("\n--> mon: channel %0d stops, channel_start %b",
                      channel, channel_start), UVM_HIGH)
                end
                begin : capture_item
                  while (channel_start) begin
                    get_pulse_edge(channel);
                    item_index++;
                    item.index = item_index;
                    if (is_valid_item(channel, item)) begin
                      item_port[channel].write(item);
                      `uvm_info(`gfn, $sformatf("\n--> mon: send item of channel %0d\n%s",
                          channel, item.sprint()), UVM_HIGH)
                    end
                    item = pwm_item::type_id::create("mon_item");
                  end : capture_item
                end
              join
            end
            // do until channel stop
            @(negedge channel_start && !cfg.pwm_en[channel]);
            // handle reset
            @(posedge reset_asserted);
          join_any
          disable fork;
        end : isolation_thread
      join
    end
  endtask : collect_channel_trans

  virtual task get_pulse_edge(int channel);
    @(negedge cfg.vif.clk);
    if (is_pulse_wrapped(channel) == PulseWrapped) begin
      if (cfg.invert[channel]) @(posedge cfg.vif.pwm[channel]);
      else                     @(negedge cfg.vif.pwm[channel]);
    end else begin  // PulseNoWrapped
      if (cfg.invert[channel]) @(negedge cfg.vif.pwm[channel]);
      else                     @(posedge cfg.vif.pwm[channel]);
    end
  endtask : get_pulse_edge

  virtual function pwm_pulse_wrap_e is_pulse_wrapped(int channel);
    int pulse_start = cfg.phase_delay[channel] + (cfg.duty_cycle_a[channel] % cfg.pulse_cycle);
    if (pulse_start >= cfg.pulse_cycle) return PulseWrapped;
    else                                return PulseNoWrapped;
  endfunction : is_pulse_wrapped

  virtual task reset_thread();
    forever begin
      @(negedge cfg.vif.rst_n);
      reset_asserted = 1'b1;
      @(posedge cfg.vif.rst_n);
      reset_asserted = 1'b0;
    end
  endtask : reset_thread

  virtual task monitor_ready_to_end();
    forever begin
      @(cfg.vif.pwm);
      ok_to_end = (cfg.vif.pwm === '0) && (cfg.pwm_en === '0) ;
    end
  endtask : monitor_ready_to_end

  virtual function int is_valid_item(int channel, pwm_item item);
    unique case (cfg.pwm_mode[channel])
      Heartbeat: begin
        // TODO
        return 1;
      end
      Blinking: begin
        return (item.index < cfg.blink_param_x[channel]) |
               ((item.index > cfg.blink_param_x[channel] + 1) &
               (item.index < cfg.num_pulses - 2));
      end
      Standard: begin
        return (item.index < cfg.num_pulses);
      end
    endcase
  endfunction : is_valid_item

endclass : pwm_monitor
