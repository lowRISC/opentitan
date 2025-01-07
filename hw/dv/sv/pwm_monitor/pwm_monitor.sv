// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_monitor extends dv_base_monitor #(
    .ITEM_T (pwm_item),
    .CFG_T  (pwm_monitor_cfg)
  );
  `uvm_component_utils(pwm_monitor)

  // Allow for (i) single cycle to reset phase counter and (ii) single register delay of
  // output signal.
  //
  // (This relies upon the internal details of the DUT because we're checking the phase
  //  delay exactly; alernatively we could just check the relative phases of the PWM
  //  output transitions, or allow a margin of error.)
  uint output_delay = 2;

  // Elapsed time in core clocks at the start of the most recent pulse cycle.
  int unsigned pulse_cycle_start = 0;
  // Duration of a pulse cycle in core clocks.
  int unsigned pulse_cycle_clks = 1;
  // Current elapsed time; core clocks.
  int unsigned clk_elapsed = 0;
  // Phase counter configuration.
  int unsigned clk_div = 0;
  int unsigned dc_resn = 0;
  // Are we still waiting to the first transition to the active state?
  bit first_activation = 1'b1;
  // Have we received valid configuration and are we monitoring the PWM output?
  bit monitoring = 1'b0;

  extern function new(string name = "", uvm_component parent = null);
  extern function void build_phase(uvm_phase phase);

  // One or more of the phase counter configuration parameters has been changed; ensure that our
  // measurement of elapsed pulse cycles is updated accordingly.
  extern function void phase_config_changed();

  // Send a sequence item to the scoreboard for checking.
  extern function void send_item(int unsigned inactive_cycles, int unsigned active_cycles);

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

// One or more of the phase counter configuration parameters has been changed; ensure that our
// measurement of elapsed pulse cycles is updated accordingly.
function void pwm_monitor::phase_config_changed();
  `uvm_info(`gfn, $sformatf("Collected phase counter config: clk_div 0x%0x dc_resn 0x%0x",
                            clk_div, dc_resn), UVM_HIGH)
  clk_elapsed = 0;
  // Remember that we have not yet seen an activation, because this means that we cannot know the
  // phase.
  first_activation = 1'b1;
  // Calculate how many core clocks a single pulse cycle takes; we require this information so
  // that we may detect a pulse cycle in which the PWM output is not asserted at all
  // (0% duty cycle).
  pulse_cycle_clks = (1 + clk_div) * (2 ** (dc_resn + 1));
  // Remember the start time of this pulse cycle in core clocks, but at the _output_ of the PWM
  // channel, ie. delayed by two cycles.
  pulse_cycle_start = output_delay;
  `uvm_info(`gfn, $sformatf("Core clocks/pulse cycle = 0x%0x", pulse_cycle_clks), UVM_HIGH)
endfunction

// Send a sequence item to the scoreboard for checking.
function void pwm_monitor::send_item(int unsigned inactive_cycles, int unsigned active_cycles);
  // Measure phase delay of PWM output assertion.
  uint phase_delay;

  pwm_item item = pwm_item::type_id::create("item");
  item.invert       = cfg.invert;
  item.monitor_id   = cfg.monitor_id;
  item.active_cnt   = active_cycles;
  item.inactive_cnt = inactive_cycles;
  item.period       = inactive_cycles + active_cycles;
  item.duty_cycle   = item.get_duty_cycle();

  if (first_activation && ~|active_cycles) begin
    // We cannot detect the phase of the PWM output if it has never been asserted. A zero duty
    // cycle can occur part-way through a sequence in the context of blinking/heartmode modes,
    // however, in which case we do have phase information still.
    item.phase = pwm_item::PhaseUnknown;
  end else begin
    // Each PWM pulse cycle is divided into 2^DC_RESN+1 beats, per beat the 16-bit
    // phase counter increments by 2^(16-DC_RESN-1)(modulo 65536)
    phase_delay = ((clk_elapsed - output_delay) / (1 + clk_div)) * (2 ** (15 - dc_resn));
    item.phase = phase_delay[15:0];
  end
  `uvm_info(`gfn, $sformatf("clk_elapsed %0x phase_delay %0x", clk_elapsed, item.phase),
            UVM_HIGH)

  analysis_port.write(item);
endfunction

task pwm_monitor::collect_trans();
  // Counting of core clocks for measuring the inactive and active phases of the PWM output.
  uint count_cycles, active_cycles;
  logic pwm_prev = 0;

  forever begin
    if (!cfg.vif.rst_n) begin
      // Wait until DUT comes out of reset.
      wait (cfg.vif.rst_n);
      // This is the reset state of the phase counter configuration.
      clk_div = 'h8000;
      dc_resn = 7;
      // Ensure that our other state is updated accordingly.
      phase_config_changed();
      monitoring = 1'b0;
    end

    @(cfg.vif.cb);

    // Do nothing until the phase counter has started; note that this does not necessarily mean
    // that the channel is enabled. We must monitor disabled channels too for completeness.
    if (cfg.active && cfg.vif.cb.start_cntr) begin
      // Pick up the new phase counter configuration.
      clk_div = cfg.clk_div;
      dc_resn = cfg.resolution;
      // Update other state relating to phase counter/pulse cycles.
      phase_config_changed();
      monitoring = 1'b1;
    end else begin
      // We need to keep track of the elapsed core clock cycles in order to ascertain
      // (i) when a complete pulse cycle has elapsed but no transition of the pwm output occurred.
      // (ii) the phase of a pwm activation within the pulse cycle.
      clk_elapsed++;
    end

    if (monitoring) begin
      count_cycles++;
      // Has the state of the PWM output changed?
      if (cfg.vif.cb.pwm != pwm_prev) begin
        `uvm_info(`gfn, $sformatf("Detected edge: %0b->%0b at %0d cycles (from last edge)",
                                  pwm_prev, cfg.vif.cb.pwm, count_cycles), UVM_HIGH)
        `uvm_info(`gfn, $sformatf(" (elapsed core clk cycles %0d)", clk_elapsed), UVM_HIGH)
        pwm_prev = cfg.vif.cb.pwm;
        if (cfg.vif.cb.pwm == cfg.invert) begin
          // The PWM output is now inactive. Save the count of 'active' cycles and start counting
          // the 'inactive' cycles.
          active_cycles = count_cycles;
        end else begin
          // The PWM output is now active, marking the end of the 'inactive' period.
          if (first_activation) begin
            // Swallow the first 'inactive' period because this is the switch on delay and any
            // phase delay up until the first assertion of the PWM output.
            first_activation = 1'b0;
          end else begin
            // Send the sequence item to the scoreboard for checking.
            send_item(count_cycles, active_cycles);
          end
          // Remember the start of the active phase as the beginning of a pulse cycle for this PWM
          // channel; if an entire pulse cycle elapses with no assertion this constitutes a cycle
          // for which the duty cycle is zero.
          pulse_cycle_start = clk_elapsed;
        end
        count_cycles = 0;
      end else if (clk_elapsed >= pulse_cycle_start + pulse_cycle_clks) begin
        // End of pulse cycle with no (further) change in the output; have we seen an 'active'
        // phase?
        if (!active_cycles) begin
          `uvm_info(`gfn, $sformatf("Idle PWM output detected (0x%0x cycle(s))", pulse_cycle_clks),
                    UVM_HIGH)
        end
        // Send a pulse cycle, showing any observed activity during that pulse cycle; this may be
        // nothing in the event of an idle output.
        //
        // Note: when the duty cycle transitions from non-zero to zero, the final pulse cycle that
        //       contains an assertion is reported here, because there is no ensuing transition to
        //       the 'asserted' state.
        send_item(pulse_cycle_clks - active_cycles, active_cycles);
        pulse_cycle_start = clk_elapsed;
        active_cycles = 0;
        count_cycles = 0;
      end
    end else begin
      count_cycles = 0;
      active_cycles = 0;
      // Capture the initial state of the PWM output signal; this is the 'inactive' state of the
      // PWM output, shortly before the channel is enabled.
      pwm_prev = cfg.vif.cb.pwm;
      first_activation = 1'b1;
    end

    // We still need to become inactive when requested....
    // May need to steal another signal from the DUT here to make this work reliably; 'cfg.active'
    // is set before the counter is disabled.
    if (!cfg.active) begin
      monitoring = 1'b0;
    end
  end
endtask

// update of_to_end to prevent sim finished when there is any activity on the bus
// ok_to_end = 0 (bus busy) / 1 (bus idle)
task pwm_monitor::monitor_ready_to_end();
  forever begin
    @(cfg.vif.cb);
    ok_to_end = ~monitoring;
  end
endtask
