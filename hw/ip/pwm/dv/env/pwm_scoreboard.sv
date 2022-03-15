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
  pwm_item                          exp_item, exp_clone;

  // type definitions
  typedef enum bit { CycleA = 1'b0, CycleB = 1'b1} state_e;
  typedef enum bit { LargeA = 1'b0, LargeB = 1'b1} dc_mod_e;

  // global settings
  bit                               regwen                   =  0;
  cfg_reg_t                         channel_cfg              = '0;
  bit [PWM_NUM_CHANNELS-1:0]        channel_en               = '0;
  bit [PWM_NUM_CHANNELS-1:0]        prev_channel_en          = '0;
  bit [PWM_NUM_CHANNELS-1:0]        invert                   = '0;
  state_e                           blink_state[PWM_NUM_CHANNELS] = '{default:0};
  int                               blink_cnt[PWM_NUM_CHANNELS]   = '{default:0};
  param_reg_t                       channel_param[PWM_NUM_CHANNELS];
  dc_blink_t                        duty_cycle[PWM_NUM_CHANNELS];
  dc_blink_t                        blink[PWM_NUM_CHANNELS];
  string                            txt                      ="";

  local pwm_item   exp_item_q[PWM_NUM_CHANNELS][$];

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    exp_item  = new("exp_item");
    for (int i = 0; i < PWM_NUM_CHANNELS; i++) begin
      item_fifo[i] = new($sformatf("item_fifo[%0d]", i), this);
    end
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);

    for (int i = 0; i < PWM_NUM_CHANNELS; i++) begin
      fork
        automatic int channel = i;
        compare_trans(channel);
      join_none
    end
    wait fork;
  endtask : run_phase

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
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
      case (1)
        (!uvm_re_match("regwen", csr_name)): begin
          regwen = item.a_data[0];
          `uvm_info(`gfn, $sformatf("Register Write en: %0b", regwen), UVM_HIGH)
        end

        (!uvm_re_match("pwm_en", csr_name)): begin
          channel_en = item.a_data[PWM_NUM_CHANNELS-1:0];
          foreach(channel_en[ii]) begin
            // if channel was disabled
            if (prev_channel_en[ii] & ~channel_en[ii]) begin
              `uvm_info(`gfn, $sformatf("detected disable of channel[%d]", ii), UVM_HIGH)
              generate_exp_item(exp_item, ii);
              `downcast(exp_clone, exp_item.clone());
              exp_item_q[ii].push_front(exp_clone);
            end
            txt = { txt, $sformatf("\n Channel[%d] : %0b",ii, channel_en[ii]) };
          end
          `uvm_info(`gfn, $sformatf("Setting channel enables %s ", txt), UVM_HIGH)
          txt = "";
          prev_channel_en = channel_en;
        end

        (!uvm_re_match("cfg", csr_name)): begin
          channel_cfg.ClkDiv = get_field_val(ral.cfg.clk_div, item.a_data);
          channel_cfg.DcResn = get_field_val(ral.cfg.dc_resn, item.a_data);
          channel_cfg.CntrEn = get_field_val(ral.cfg.cntr_en, item.a_data);
          `uvm_info(`gfn,
                    $sformatf("PWM global cfg: \n Clk Div: %0h, \n Dc Resn: %0h, \n Cntr en: %0b:",
                              channel_cfg.ClkDiv, channel_cfg.DcResn, channel_cfg.CntrEn), UVM_HIGH)
        end

        (!uvm_re_match("invert", csr_name)): begin
          invert = item.a_data[PWM_NUM_CHANNELS-1:0];
          foreach(invert[ii]) begin
            txt = { txt, $sformatf("\n Invert Channel[%d] : %0b",ii, invert[ii]) };
          end
          `uvm_info(`gfn, $sformatf("Setting channel Inverts %s ", txt), UVM_HIGH)

        end

        (!uvm_re_match("pwm_param_*", csr_name)): begin
          int idx = get_multireg_idx(csr_name);
          channel_param[idx].PhaseDelay = get_field_val(ral.pwm_param[idx].phase_delay,
                                                        item.a_data);
          channel_param[idx].HtbtEn     = get_field_val(ral.pwm_param[idx].htbt_en, item.a_data);
          channel_param[idx].BlinkEn    = get_field_val(ral.pwm_param[idx].blink_en, item.a_data);
          txt = $sformatf("\n Setting Param for channel[%d]", idx);
          txt = { txt, $sformatf("\n ----| Phase Delay %0h", channel_param[idx].PhaseDelay)};
          txt = {txt,  $sformatf("\n ----| Heart Beat enable: %0b", channel_param[idx].HtbtEn) };
          txt = {txt,  $sformatf("\n ----| Blink enable: %0b", channel_param[idx].BlinkEn) };
          `uvm_info(`gfn, $sformatf("Setting Channel Param for CH[%d], %s",idx, txt), UVM_HIGH)
        end

        (!uvm_re_match("duty_cycle_*",csr_name)): begin
          int idx = get_multireg_idx(csr_name);
          duty_cycle[idx].A = get_field_val(ral.duty_cycle[idx].a, item.a_data);
          duty_cycle[idx].B = get_field_val(ral.duty_cycle[idx].b, item.a_data);
          `uvm_info(`gfn, $sformatf("\n Seeting channel[%d] duty cycle A:%0h B:%0h",
                                    idx, duty_cycle[idx].A ,duty_cycle[idx].B), UVM_HIGH)
        end

        (!uvm_re_match("blink_*",csr_name)): begin
          int idx = get_multireg_idx(csr_name);
          blink[idx].A = get_field_val(ral.blink_param[idx].x, item.a_data);
          blink[idx].B = get_field_val(ral.blink_param[idx].y, item.a_data);
          `uvm_info(`gfn, $sformatf("\n Setting channel[%d] Blink X:%0h Y:%0h",
                                    idx, blink[idx].A ,blink[idx].B), UVM_HIGH)
          blink_cnt[idx] = blink[idx].A;
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
    pwm_item compare_item = new();
    pwm_item input_item   = new($sformatf("input_item_%d", channel));
    string txt            = "";
    int    p = 0;

    // as this DUT signals needs to be evaluated over time
    // they are only evaluated when the channel is off.
    // this way it is known what the first and last item are
    // as they might deviate from the settings due to rounding
    // and termination.

    // The very first item will be when the monitor detects the first active edge
    // it will have no information
    item_fifo[channel].get(input_item);
    // wait for the first expected item
    wait( exp_item_q[channel].size() > 0);
    compare_item = exp_item_q[channel].pop_front();
    // drop the first pwm pulse as it will not match
    item_fifo[channel].get(input_item);
    `uvm_info(`gfn, $sformatf("dropped first item %s", input_item.convert2string()), UVM_HIGH)
    // keep going until channel is disabled.
    while (item_fifo[channel].used() > 1) begin
      // get next item and compare
      item_fifo[channel].get(input_item);
      if (!compare_item.compare(input_item)) begin
        txt = "\n.......| Exp Item |.......";
        txt = {txt, $sformatf("\n %s", compare_item.convert2string()) };
        txt = { txt, "\n.......| Actual Item |......."};
        txt = {txt, $sformatf("\n %s", input_item.convert2string()) };
        `uvm_fatal(`gfn, $sformatf("\n PWM pulse on Channel %d did not match %s", channel, txt ))
      end else begin
        `uvm_info(`gfn, $sformatf("Item %d Matched", p++), UVM_HIGH)
        // generate next predicted item - based on current
      end
      generate_exp_item(compare_item, channel);
    end
    // drop last item as it is not expected to match settings
    item_fifo[channel].get(input_item);
  endtask : compare_trans

  virtual task generate_exp_item(ref pwm_item item, input bit [PWM_NUM_CHANNELS-1:0] channel);
    int int_dc;
    int beats_cycle;
    int period;
    int high_cycles;
    int low_cycles;
    int initial_dc = 0;
    int subcycle_cnt = 0;
    dc_mod_e dc_mod;
    bit [15:0] resn_mask = '0;
    bit [15:0] phase_count = '0;

    // compare duty cycle for modifier
    dc_mod = (duty_cycle[channel].A > duty_cycle[channel].B) ? LargeA : LargeB;

    if (channel_param[channel].BlinkEn) begin
      // Unique case for violation report
      case (channel_param[channel].HtbtEn)
        1'b0: begin
          // When HTBT_EN is cleared, the standard blink behavior applies, meaning
          // that the output duty cycle alternates between DUTY_CYCLE.A for (BLINK_PARAM.X+1)
          // pulses and DUTY_CYCLE.B for (BLINK_PARAM.Y+1) pulses.
          if (blink_cnt[channel] == 0) begin
            if (blink_state[channel] == CycleB) begin
              blink_state[channel] = CycleA;
              blink_cnt[channel] = blink[channel].A;
              int_dc = duty_cycle[channel].A;
            end else begin
              blink_state[channel] = CycleB;
              blink_cnt[channel]   = blink[channel].B;
              int_dc = duty_cycle[channel].B;
            end
          end else begin
            int_dc = (blink_state[channel] == CycleA) ? duty_cycle[channel].A :
              duty_cycle[channel].B;
            blink_cnt[channel] -= 1;
          end
        end
        1'b1: begin
          // When HTBT_EN is set, the duty cycle increases (or decreases) linearly from
          // DUTY_CYCLE.A to DUTY_CYCLE.B and back, in steps of blink.A (BLINK_PARAM.Y+1) with an
          // increment (decrement) once every blink.B (BLINK_PARAM.X+1) PWM cycles.
          case (blink_state[channel])
            CycleA: begin
              // current duty cycle
              int_dc = (initial_dc) ? int_dc : duty_cycle[channel].A;
              // when subcycle_cnt is equal to (BLINK_PARAM.X+1)
              if (subcycle_cnt == (blink[channel].B + 1)) begin
                // increment (decrement) int_dc by (BLINK_PARAM.Y+1)
                int_dc = (dc_mod == 1'b0) ?
                  (int_dc - (blink[channel].A + 1)) :
                  (int_dc + (blink[channel].A + 1));
                // reset subcycle_cnt after increment (decrement)
                subcycle_cnt = 0;
                initial_dc++;
              end else begin
                // else increment subcycle_cnt
                subcycle_cnt++;
                initial_dc++;
              end
              // enter CycleB when duty cycle is reached
              case (dc_mod)
                LargeA: begin
                  if (int_dc <= duty_cycle[channel].B) begin
                    blink_state[channel] = CycleB;
                    subcycle_cnt = 0;
                    initial_dc = 0;
                  end
                end
                LargeB: begin
                  if (int_dc >= duty_cycle[channel].B) begin
                    blink_state[channel] = CycleB;
                    subcycle_cnt = 0;
                    initial_dc = 0;
                  end
                end
                default: begin
                  `uvm_info(`gfn, $sformatf("Error: Invalid: dc_mod == %s.", dc_mod), UVM_HIGH)
                end
              endcase
            end
            CycleB: begin
              int_dc = (subcycle_cnt) ? int_dc : duty_cycle[channel].B;
              if (subcycle_cnt == (blink[channel].B + 1'b1)) begin
                int_dc = (dc_mod == 1'b1) ?
                  (int_dc - (blink[channel].A + 1'b1)) :
                  (int_dc + (blink[channel].A + 1'b1));
                subcycle_cnt = 0;
                initial_dc++;
              end else begin
                subcycle_cnt++;
                initial_dc++;
              end
              case (dc_mod)
                LargeB: begin
                  if (int_dc <= duty_cycle[channel].A) begin
                    blink_state[channel] = CycleA;
                    subcycle_cnt = 0;
                    initial_dc = 0;
                  end
                end
                LargeA: begin
                  if (int_dc >= duty_cycle[channel].A) begin
                    blink_state[channel] = CycleA;
                    subcycle_cnt = 0;
                    initial_dc = 0;
                  end
                end
                default: begin
                  `uvm_info(`gfn, $sformatf("Error: Invalid: dc_mod == %s.", dc_mod), UVM_HIGH)
                end
              endcase
            end
            default: begin
              blink_state[channel] = CycleA;
            end
          endcase
        end
        default: begin
          `uvm_info(`gfn, $sformatf("Error: Channel %d: HtbtEn == %b is not a valid state.",
            channel, channel_param[channel].HtbtEn), UVM_HIGH)
        end
      endcase
    end else int_dc = duty_cycle[channel].A;

    beats_cycle = 2**(channel_cfg.DcResn + 1);
    period      = beats_cycle * (channel_cfg.ClkDiv + 1);
    high_cycles = (int_dc >> (16 - (channel_cfg.DcResn + 1))) * (channel_cfg.ClkDiv + 1);
    low_cycles  = period - high_cycles;
    // only interested in DcRsn+1 MSB
    resn_mask = {16{1'b1}} << (16 - (channel_cfg.DcResn + 1));
    // During each beat, the 16-bit phase counter increments by 2^(16-DC_RESN-1)
    phase_count = beats_cycle * (2**(16 - (channel_cfg.DcResn - 1)));

    item.monitor_id      = channel;
    item.invert          = invert[channel];
    item.period          = period;
    item.active_cnt      = invert[channel] ? low_cycles : high_cycles;
    item.inactive_cnt    = invert[channel] ? high_cycles : low_cycles;
    item.duty_cycle      = item.get_duty_cycle();
    item.phase           = phase_count;

  endtask // generate_exp_item

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
