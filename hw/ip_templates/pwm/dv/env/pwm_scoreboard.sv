// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class pwm_scoreboard extends cip_base_scoreboard #(
      .CFG_T(pwm_env_cfg),
      .RAL_T(pwm_reg_block),
      .COV_T(pwm_env_cov)
     );
  `uvm_component_utils(pwm_scoreboard)
  `uvm_component_new

  // TLM agent FIFOs.
  uvm_tlm_analysis_fifo #(pwm_item) item_fifo[PWM_NUM_CHANNELS];

  // Type definitions.
  typedef enum bit { CycleA = 1'b0, CycleB = 1'b1} state_e;
  typedef enum bit { LargeA = 1'b0, LargeB = 1'b1} dc_mod_e;

  // Every time the state is changed either from A to B or B to A, the initial transaction checking
  // goes out of sync between checker and DUT. So, ignore_state_change is changed to `SettleTime`.
  //
  // This gives the checker a window of four pulse cycles to sync to the DUT `pwm_o` pulse
  // accurately.
  // Because the monitors do not respond to the assertion of the channel enable but rather the phase
  // counter, if the phase counter is varying rapidly (ClkDiv=0, dcResn=0) the first blink phase can
  // be up to 4 pulse cycles out, but synchronization typically occurs when the blinking state
  // changes.
  localparam int SettleTime = 4;

  // global settings
  bit                        regwen           =  0;
  cfg_reg_t                  next_cfg         = '0;
  cfg_reg_t                  phase_cfg        = '0;
  bit [PWM_NUM_CHANNELS-1:0] channel_en       = '0;
  bit [PWM_NUM_CHANNELS-1:0] invert           = '0;
  bit [PWM_NUM_CHANNELS-1:0] first_activation = '1;
  // Have we synchronized yet? Once synchronized we tolerate no further deviations.
  bit [PWM_NUM_CHANNELS-1:0] synchronized     = '0;
  // Remember the previous item from the monitor so that we can spot blink state transitions and
  // synchronize exactly.
  pwm_item prev_item[PWM_NUM_CHANNELS];

  state_e                    blink_state[PWM_NUM_CHANNELS] = '{default:CycleA};
  int                        blink_cnt[PWM_NUM_CHANNELS]   = '{default:0};
  int                        ignore_state_change[PWM_NUM_CHANNELS] = '{default:SettleTime};
  // bit 16 is added for overflow
  bit [16:0]                 int_dc[PWM_NUM_CHANNELS] = '{default:0};
  param_reg_t                channel_param[PWM_NUM_CHANNELS];
  duty_cycle_t               duty_cycle[PWM_NUM_CHANNELS];
  blink_param_t              blink[PWM_NUM_CHANNELS];

  // UVM phases
  extern function void build_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);
  extern function void check_phase(uvm_phase phase);

  // Check and update predictions based on a single TL message seen at the 'ral_name' register
  // interface. 'channel' determines if the fields of 'item' capture either an A or D channel
  // message.
  extern virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);

  // Respond to a DUT reset.
  extern virtual function void reset(string kind = "HARD");

  // Monitor whether the TL-UL clock is running and whether the PWM output is changing.
  extern task monitor_clock(int channel);

  // Run forever, comparing items from the monitor on the given channel with the items that we
  // expect to be generated (based on the scoreboard's model of the config registers).
  extern task compare_trans(int unsigned channel);

  // We allow a little difference in the timing of the blink state transitions until we've
  // synchronized to this PWM output. Until that point a mismatch may legitimately occur between
  // the observed and predicted cycles.
  extern function bit blink_state_untrusted(int unsigned channel);

  // Adjust channel state to synchronize with the monitor/DUT output.
  extern function void synchronize_blink_state(int unsigned channel);

  // Advance the blink state at the end of the 'BLINK_PARAM.X+1' or 'BLINK_PARAM.Y+1' pulse cycles.
  extern function void advance_blink_state(int unsigned channel);

  // Compute an expected pwm_item that we would like the monitor to see, based on the current
  // configuration registers.
  extern function void generate_exp_item(ref pwm_item item, input int unsigned channel);

endclass : pwm_scoreboard

function void pwm_scoreboard::build_phase(uvm_phase phase);
  super.build_phase(phase);
  for (int i = 0; i < PWM_NUM_CHANNELS; i++) begin
    item_fifo[i] = new($sformatf("item_fifo[%0d]", i), this);
  end
endfunction

task pwm_scoreboard::run_phase(uvm_phase phase);
  super.run_phase(phase);
  if (cfg.en_scb) begin
    // For each PWM output create one checker process and one clock/output monitor process.
    foreach (item_fifo[channel]) begin
      // Ensure that the newly-created processes do not see changes to the 'channel' variable when
      // starting.
      automatic int ch = channel;
      fork
        compare_trans(ch);
        if (cfg.en_cov) begin
          monitor_clock(ch);
        end
      join_none
    end
  end
endtask

function void pwm_scoreboard::check_phase(uvm_phase phase);
  super.check_phase(phase);
  for (int i = 0; i < PWM_NUM_CHANNELS; i++) begin
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(pwm_item, item_fifo[i])
  end
endfunction

task pwm_scoreboard::process_tl_access(tl_seq_item   item,
                                       tl_channels_e channel,
                                       string        ral_name);
  string txt;
  uvm_reg csr;
  int unsigned idx;
  bit [TL_DW-1:0] reg_value;
  bit             do_read_check = 1'b1;
  bit             write = item.is_write();
  uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

  bit             addr_phase_write = (write && channel  == AddrChannel);
  bit             data_phase_read  = (!write && channel == DataChannel);

  // if access was to a valid csr, get the csr handle
  if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
    csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
    `DV_CHECK_NE_FATAL(csr, null)
    // Extract register index indicating the channel number.
    idx = get_multireg_idx(csr.get_name());
  end else begin
    `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
  end

  // The REGWEN register controls write access to all of the DUT registers, including itself.
  if (addr_phase_write && `gmv(ral.regwen.regwen)) begin
    // if incoming access is a write to a valid csr, then make updates right away
    void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr.get_name())
      "regwen": begin
        regwen = regwen & item.a_data[0];
        `uvm_info(`gfn, $sformatf("Register Write en: %0b", regwen), UVM_HIGH)
      end

      "pwm_en": begin
        int unsigned prev_en = channel_en;
        channel_en = item.a_data[PWM_NUM_CHANNELS-1:0];
        foreach (channel_en[ii]) begin
          if (channel_en[ii] & !prev_en[ii]) begin
            `uvm_info(`gfn, $sformatf("detected enabling of channel[%0d]", ii), UVM_HIGH)
            // Set up the prediction state for this channel.
            blink_cnt[ii] = blink[ii].X;
            blink_state[ii] = CycleA;
            int_dc[ii] = duty_cycle[ii].A;
          end
          // Alas we presently must ignore the first couple of items because the PWM configuration
          // is set up with an arbitrary phase relationship to the shared phase counter.
          ignore_state_change[ii] = SettleTime;
          txt = {txt, $sformatf("\n Channel[%d] : %0b", ii, channel_en[ii])};
        end
        `uvm_info(`gfn, $sformatf("Setting channel enables %s ", txt), UVM_MEDIUM)
      end

      "cfg": begin
        next_cfg.ClkDiv = get_field_val(ral.cfg.clk_div, item.a_data);
        next_cfg.DcResn = get_field_val(ral.cfg.dc_resn, item.a_data);
        next_cfg.CntrEn = get_field_val(ral.cfg.cntr_en, item.a_data);
        // Channel configuration is accepted only when phase counter becomes enabled.
        if (next_cfg.CntrEn & ~phase_cfg.CntrEn) begin
          phase_cfg.ClkDiv = next_cfg.ClkDiv;
          phase_cfg.DcResn = next_cfg.DcResn;
        end
        // Enable bit is always accepted; it must be possible to enable/disable the phase counter
        // at any point in its operation.
        phase_cfg.CntrEn = next_cfg.CntrEn;
        first_activation = '1;
        // None of the channels is now synchronized; discard any remembered observations and
        // restart the process of synchronizing with blink state transitions.
        synchronized = '0;
        foreach (prev_item[ii]) begin
          prev_item[ii] = null;
        end
        `uvm_info(`gfn,
                  $sformatf("PWM global cfg: \n Clk Div: %0h, \n Dc Resn: %0h, \n Cntr en: %0b:",
                            phase_cfg.ClkDiv, phase_cfg.DcResn, phase_cfg.CntrEn), UVM_MEDIUM)
      end

      "invert": begin
        invert = item.a_data[PWM_NUM_CHANNELS-1:0];
        foreach (invert[ii]) begin
          txt = {txt, $sformatf("\n Invert Channel[%0d] : %0b", ii, invert[ii])};
        end
        `uvm_info(`gfn, $sformatf("Setting channel Inverts %s ", txt), UVM_MEDIUM)
      end

      // PWM_PARAM_<i> registers; channel count is parameterized.
      $sformatf("pwm_param_%0d", idx): begin
        channel_param[idx].PhaseDelay = get_field_val(ral.pwm_param[idx].phase_delay,
                                                      item.a_data);
        channel_param[idx].HtbtEn     = get_field_val(ral.pwm_param[idx].htbt_en, item.a_data);
        channel_param[idx].BlinkEn    = get_field_val(ral.pwm_param[idx].blink_en, item.a_data);
        txt = $sformatf("\n Setting Param for channel[%0d]", idx);
        txt = {txt, $sformatf("\n ----| Phase Delay %0h", channel_param[idx].PhaseDelay)};
        txt = {txt, $sformatf("\n ----| Heart Beat enable: %0b", channel_param[idx].HtbtEn) };
        txt = {txt, $sformatf("\n ----| Blink enable: %0b", channel_param[idx].BlinkEn) };
        `uvm_info(`gfn, $sformatf("Setting Channel Param for CH[%0d], %s", idx, txt), UVM_MEDIUM)
      end

      // DUTY_CYCLE_<i> registers; channel count is parameterized.
      $sformatf("duty_cycle_%0d", idx): begin
        duty_cycle[idx].A = get_field_val(ral.duty_cycle[idx].a, item.a_data);
        duty_cycle[idx].B = get_field_val(ral.duty_cycle[idx].b, item.a_data);
        `uvm_info(`gfn, $sformatf("\n Setting channel[%0d] duty cycle A:%0h B:%0h", idx,
                                  duty_cycle[idx].A ,duty_cycle[idx].B), UVM_MEDIUM)
      end

      // BLINK_PARAM_<i> registers; channel count is parameterized.
      $sformatf("blink_param_%0d", idx): begin
        blink[idx].X = get_field_val(ral.blink_param[idx].x, item.a_data);
        blink[idx].Y = get_field_val(ral.blink_param[idx].y, item.a_data);
        `uvm_info(`gfn, $sformatf("\n Setting channel[%0d] Blink X:%0h Y:%0h", idx,
                                  blink[idx].X ,blink[idx].Y), UVM_MEDIUM)
      end

      default: begin
        `uvm_fatal(`gfn, $sformatf("\n  scb: invalid csr: %0s", csr.get_full_name()))
      end
    endcase
  end

  // Sample for coverage
  if (cfg.en_cov) begin
    cov.clock_cg.sample(cfg.get_clk_core_freq(), cfg.clk_rst_vif.clk_freq_mhz);
    cov.cfg_cg.sample(phase_cfg.ClkDiv, phase_cfg.DcResn, phase_cfg.CntrEn);
    foreach (channel_en[ii]) begin
      cov.pwm_chan_en_inv_cg.sample(channel_en, invert);
      cov.pwm_per_channel_cg.sample(channel_en,
                                    invert,
                                    channel_param[ii].PhaseDelay,
                                    channel_param[ii].BlinkEn,
                                    channel_param[ii].HtbtEn,
                                    duty_cycle[ii].A,
                                    duty_cycle[ii].B,
                                    blink[ii].X,
                                    blink[ii].Y);
    end
  end

  // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
  if (data_phase_read) begin
    if (do_read_check) begin
      `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data, $sformatf("reg name: %0s",
                                                                    csr.get_full_name()))
    end
    void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
  end
endtask

function void pwm_scoreboard::reset(string kind = "HARD");
  super.reset(kind);
  `uvm_info(`gfn, "Reset flushing all channels", UVM_MEDIUM)
  for (int unsigned channel = 0; channel < PWM_NUM_CHANNELS; channel++) begin
    // Discard any lingering pulse descriptions from the monitor.
    item_fifo[channel].flush();
  end
endfunction

// Monitor whether the TL-UL clock is running and whether the PWM output is changing.
task pwm_scoreboard::monitor_clock(int channel);
  forever begin
    // The core clock is always running so we may use this to monitor whether the TL-UL bus clock
    // is gated.
    cfg.clk_rst_core_vif.wait_clks(1);
    if (!cfg.under_reset) begin
      bit pwm = cfg.m_pwm_monitor_cfg[channel].vif.pwm;
      bit clk_gate = cfg.clk_rst_vif.clk_gate;
      `uvm_info(`gfn, $sformatf("Monitor %0d clk_gate %0d pwm %0d", channel, clk_gate, pwm),
                UVM_HIGH)
      cov.lowpower_cg.sample(clk_gate, pwm);
    end
  end
endtask

// We allow a little difference in the timing of the blink state transitions until we've
// synchronized to this PWM output. Until that point a mismatch may legitimately occur between
// the observed and predicted cycles.
function bit pwm_scoreboard::blink_state_untrusted(int unsigned channel);
  // Until we've synchronized, drift is permitted in either direction.
  return !synchronized[channel] &&
            (blink_cnt[channel] < SettleTime || ignore_state_change[channel] > 0);
endfunction

// Adjust channel state to synchronize with the monitor/DUT output.
function void pwm_scoreboard::synchronize_blink_state(int unsigned channel);
  `uvm_info(`gfn, $sformatf("Synchronizing on channel %0d (ignore %0d blink_cnt %0d)", channel,
                            ignore_state_change[channel], blink_cnt[channel]), UVM_MEDIUM)
  if (ignore_state_change[channel] > 0) begin
    // Expectation is ahead of the monitor/DUT, simply rewind the pulse cycle counter within the
    // current blinking phase.
    `uvm_info(`gfn, $sformatf("Synchronizing blink state for channel %0d", channel), UVM_MEDIUM)
    if (channel_param[channel].HtbtEn) begin
      // Heartbeat mode always `X` pulse cycles.
      blink_cnt[channel] = blink[channel].X;
    end else begin
      // We're remaining in the same blink phase and just resetting the counter, but remembering
      // that we've already observed the first pulse cycle of the phase.
      blink_cnt[channel] = (blink_state[channel] == CycleB) ? blink[channel].Y : blink[channel].X;
    end
  end else begin
    // Expectation is behind, so we need to advance to the next phase.
    advance_blink_state(channel);
  end
  synchronized[channel] = 1'b1;
  // We have now synchronized, but reset `ignore_state_change` for clarity/diagnostics only; it
  // should be ignored from now onwards.
  ignore_state_change[channel] = 0;
endfunction

task pwm_scoreboard::compare_trans(int unsigned channel);
  pwm_item compare_item = new($sformatf("expected_item_%0d", channel));
  pwm_item input_item   = new($sformatf("input_item_%0d", channel));
  // Count of predictions made.
  int unsigned predicted = 0;
  // Count of ignored sequence items.
  int unsigned ignored = 0;

  forever begin
    if (!cfg.under_reset) begin
      bit matched;
      item_fifo[channel].get(input_item);
      if (cfg.under_reset) begin
        // In the event that `regwen` has been set it is not possible to shut down the DUT cleanly
        // because the register cannot be altered; the DUT must be reset whilst it is still
        // operating at the end of `pwm_regwen_vseq` and we may still be awaiting a further sequence
        // item at that point.
        continue;
      end

      // We may need to ignore the first detected sequence item after initialization, but our
      // expectations change before the DUT blink state changes (after 'BLINK_PARAM.X+1' pulse
      // cycles), so we aim to synchronize at that transition.
      if (blink_state_untrusted(channel)) begin
        // If we spot a change during the 'settle time' we can use this to synchronize our
        // expectations with the monitor/DUT.
        if (prev_item[channel] != null && !input_item.compare(prev_item[channel])) begin
          // This mismatch with the previous observation likely indicates that the DUT has advanced
          // its blink state (after 'BLINK_PARAM.X+1' pulse cycles), so we can start counting the
          // 'BLINK_PARAM.X|Y+1' pulse cycles of this state.
          // This includes the one that we've just detected, and we will check it below.
          synchronize_blink_state(channel);
        end
      end

      // Form our expectation for this item; done after any synchronization so that we may also
      // check the first pulse cycle of the new blinking phase.
      generate_exp_item(compare_item, channel);

      // Does the observed pulse cycle match the expectation?
      matched = input_item.compare(compare_item);

      // Once synchronized, no further deviation is tolerated.
      if (synchronized[channel] || ignore_state_change[channel] <= 0) begin
        `uvm_info(`gfn, $sformatf("\n PWM :: Channel = [%0d] DUT CONTENT \n %s",
                                  channel, input_item.sprint()), UVM_MEDIUM)
        `uvm_info(`gfn, $sformatf("\n PWM :: Channel = [%0d] EXPECTED CONTENT \n %s",
                                  channel, compare_item.sprint()), UVM_MEDIUM)
        if (matched) begin
          `uvm_info(`gfn, $sformatf("\n PWM :: Channel = [%0d] MATCHED", channel), UVM_MEDIUM)
        end else begin
          // Terminate at the first mismatch.
          `uvm_fatal(`gfn, $sformatf("\n PWM :: Channel = [%0d] did not MATCH", channel))
        end
        // If this channel is not in blinking mode then there shall be no transitions.
        if (channel_en[channel] && channel_param[channel].BlinkEn) begin
          // Remember the most recent item that was received and successfully matched so that we can
          // spot blink state changes.
          prev_item[channel] = input_item;
        end else begin
          synchronized[channel] = 1'b1;
        end
      end else begin
        // It's important to be able to see what we're ignoring!
        `uvm_info(`gfn, $sformatf("\n PWM :: Channel = [%0d] DUT CONTENT \n %s",
                                  channel, input_item.sprint()), UVM_MEDIUM)
        `uvm_info(`gfn, $sformatf("\n PWM :: Channel = [%0d] IGNORED EXPECTATION %s",
                                  channel, compare_item.sprint()), UVM_MEDIUM)
        ignore_state_change[channel] -= 1;
        ignored++;
      end

      // Report a running average of the percentage of items ignored.
      predicted++;
      if (|predicted) begin
        `uvm_info(`gfn, $sformatf("Channel %0d ignored %0d%% so far", channel,
                                  (ignored * 100) / predicted), UVM_MEDIUM)
      end
    end else begin
      // Reset global state including regwen and phase counter.
      regwen = 1'b1;
      phase_cfg.ClkDiv = 'h8000;
      phase_cfg.DcResn = 7;
      channel_en[channel] = 1'b0;
      invert[channel] = 'b0;
      first_activation[channel] = 1'b1;
      // Reset the channel configuration.
      channel_param[channel].PhaseDelay = 'b0;
      channel_param[channel].BlinkEn = 1'b0;
      channel_param[channel].HtbtEn = 1'b0;
      duty_cycle[channel].A = 'h7fff;
      duty_cycle[channel].B = 'h7fff;
      int_dc[channel] = 'h7fff;
      blink[channel].X = 0;
      blink[channel].Y = 0;
      blink_cnt[channel] = 0;
      blink_state[channel] = CycleA;
      ignore_state_change[channel] = SettleTime;
      // Wait until we exit reset.
      cfg.clk_rst_vif.wait_clks(1);
    end
  end
endtask : compare_trans

// Advance the blink state at the end of the 'BLINK_PARAM.X+1' or 'BLINK_PARAM.Y+1' pulse cycles.
function void pwm_scoreboard::advance_blink_state(int unsigned channel);
  `uvm_info(`gfn, $sformatf("Advancing blink state for channel %0d", channel), UVM_HIGH)
  if (channel_param[channel].HtbtEn) begin
    dc_mod_e dc_mod = (duty_cycle[channel].A > duty_cycle[channel].B) ? LargeA : LargeB;

    // Modify the duty cycle for the next interval of 'BLINK_PARAM.X+1' pulse cycles.
    case (blink_state[channel])
      CycleA: begin
        // increment (decrement) int_dc by (BLINK_PARAM.Y+1)
        int_dc[channel] = (dc_mod == LargeA) ?
          (int_dc[channel] - (blink[channel].Y + 1)) :
          (int_dc[channel] + (blink[channel].Y + 1));
        // enter CycleB when higher duty cycle is reached
        case (dc_mod)
          LargeA: begin
            if (int_dc[channel][16] || int_dc[channel] <= duty_cycle[channel].B) begin
              blink_state[channel] = CycleB;
            end
          end
          LargeB: begin
            if (int_dc[channel][16] || int_dc[channel] >= duty_cycle[channel].B) begin
              blink_state[channel] = CycleB;
            end
          end
          default: begin
            `uvm_info(`gfn, $sformatf("Error: Invalid: dc_mod == %s.", dc_mod), UVM_HIGH)
          end
        endcase
      end
      CycleB: begin
        int_dc[channel] = (dc_mod == LargeB) ?
          (int_dc[channel] - (blink[channel].Y + 1)) :
          (int_dc[channel] + (blink[channel].Y + 1));
        case (dc_mod)
          LargeB: begin
            if (int_dc[channel][16] || int_dc[channel] <= duty_cycle[channel].A) begin
              blink_state[channel] = CycleA;
            end
          end
          LargeA: begin
            if (int_dc[channel][16] || int_dc[channel] >= duty_cycle[channel].A) begin
              blink_state[channel] = CycleA;
            end
          end
          default: begin
            `uvm_info(`gfn, $sformatf("Error: Invalid: dc_mod == %s.", dc_mod), UVM_HIGH)
          end
        endcase
      end
      default: `uvm_fatal(`gfn, "Invalid blink state")
    endcase
    blink_cnt[channel] = blink[channel].X;
  end else begin
    // Regular blinking, not heartbeat mode.
    if (blink_state[channel] == CycleB) begin
      blink_state[channel] = CycleA;
      blink_cnt[channel]   = blink[channel].X;
    end else begin
      blink_state[channel] = CycleB;
      blink_cnt[channel]   = blink[channel].Y;
    end
  end
endfunction

function void pwm_scoreboard::generate_exp_item(ref pwm_item item, input int unsigned channel);
  uint beats_cycle     = 0;
  uint period          = 0;
  uint active_cycles   = 0;
  uint inactive_cycles = 0;
  uint phase_delay;
  // Expected duty cycle.
  bit [16:0] dc = 0;

  // Report the channel state upon which this expectation is based.
  `uvm_info(`gfn, $sformatf("Generating expectation for channel %0d en %0d blink %0d htbt %0d",
                            channel, channel_en[channel], channel_param[channel].BlinkEn,
                            channel_param[channel].HtbtEn), UVM_HIGH)
  `uvm_info(`gfn, $sformatf(" - blink cnt 0x%0x state %s", blink_cnt[channel],
                            (blink_state[channel] == CycleA) ? "A" : "B"), UVM_HIGH)
  `uvm_info(`gfn, $sformatf(" - synchronized %0d", synchronized[channel]), UVM_HIGH)

  // Configured phase delay for this channel.
  phase_delay = channel_param[channel].PhaseDelay;

  if (!channel_en[channel]) begin
    // If the channel is disabled it remains in its inactive state and phase has no meaning;
    // we set it to zero because the `pwm_monitor` logic will be unable to measure the phase.
    phase_delay = 0;
  end else if (channel_param[channel].BlinkEn) begin
    // Unique case for violation report
    case (channel_param[channel].HtbtEn)
      1'b0: begin
        // When HTBT_EN is cleared, the standard blink behavior applies, meaning
        // that the output duty cycle alternates between DUTY_CYCLE.A for (BLINK_PARAM.X+1)
        // pulses and DUTY_CYCLE.B for (BLINK_PARAM.Y+1) pulses.
        dc = (blink_state[channel] == CycleA) ? duty_cycle[channel].A : duty_cycle[channel].B;
      end
      1'b1: begin
        dc_mod_e dc_mod = (duty_cycle[channel].A > duty_cycle[channel].B) ? LargeA : LargeB;

        // When HTBT_EN is set, the duty cycle increases (or decreases) linearly from
        // DUTY_CYCLE.A to DUTY_CYCLE.B and back, in steps of blink.B (BLINK_PARAM.Y+1) with an
        // increment (decrement) once every blink.A (BLINK_PARAM.X+1) PWM cycles.

        // current duty cycle
        dc = int_dc[channel];

        if (dc_mod == LargeB) begin
          // Overflow condition check
          if (dc[16]) begin
            if (cfg.en_cov) begin
              cov.dc_uf_ovf_tb_cg.sample(channel, 1);
            end
            dc = 16'hffff;
          end
        end else begin
          // Underflow condition check
          if (dc[16]) begin
            if (cfg.en_cov) begin
              cov.dc_uf_ovf_tb_cg.sample(channel, 0);
            end
            dc = 16'h0000;
          end
        end
      end
      default: begin
        `uvm_info(`gfn, $sformatf("Error: Channel %d: HtbtEn == %b is not a valid state.",
          channel, channel_param[channel].HtbtEn), UVM_HIGH)
      end
    endcase

    if (blink_cnt[channel] == 0) begin
      // Modify the duty cycle for the next interval of 'BLINK_PARAM.X+1/Y+1' pulse cycles.
      advance_blink_state(channel);
      ignore_state_change[channel] = SettleTime;
    end else begin
      blink_cnt[channel]--;
    end
  end else begin
    dc = duty_cycle[channel].A;
  end

  beats_cycle = 2**(phase_cfg.DcResn + 1);
  period      = beats_cycle * (phase_cfg.ClkDiv + 1);
  // This is the number of clock cycles within the pulse interval for which the output is asserted
  // (normally this means the number of cycles for which it is high, but if `invert` is set then
  //  it's the number of cycles for which the output is low).
  active_cycles = (dc[15:0] >> (16 - (phase_cfg.DcResn + 1))) * (phase_cfg.ClkDiv + 1);
  inactive_cycles = period - active_cycles;

  item.monitor_id      = channel;
  item.invert          = invert[channel];
  item.period          = period;
  item.active_cnt      = active_cycles;
  item.inactive_cnt    = inactive_cycles;
  item.duty_cycle      = item.get_duty_cycle();

  // If this channel has never produced a transition to the active state then the `pwm_monitor` will
  // not have been able to measure the phase.
  if (first_activation[channel] && !active_cycles) begin
    item.phase = pwm_item::PhaseUnknown;
  end else begin
    first_activation[channel] = 1'b0;

    // Each PWM pulse cycle is divided into 2^DC_RESN+1 beats; per beat, the 16-bit phase counter
    // increments by 2^(16-DC_RESN-1).
    phase_delay = phase_delay & ~((16'h1 << (15 - phase_cfg.DcResn)) - 16'h1);

    `uvm_info(`gfn, $sformatf("chan %d phase 0x%0x dcresn %0x mask %0x", channel,
                              channel_param[channel].PhaseDelay, phase_cfg.DcResn,
                              ~((16'h1 << (15 - phase_cfg.DcResn)) - 16'h1)), UVM_MEDIUM)
    item.phase = phase_delay;
  end
endfunction
