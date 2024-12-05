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

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(pwm_item) item_fifo[PWM_NUM_CHANNELS];

  // type definitions
  typedef enum bit { CycleA = 1'b0, CycleB = 1'b1} state_e;
  typedef enum bit { LargeA = 1'b0, LargeB = 1'b1} dc_mod_e;
  localparam int Init = 0;
  localparam int LocalCount = 1;

  // Every time the state is changed either from A to B or B to A, the initial transaction checking
  // goes out of sync between checker and DUT. So, ignore_state_change is changed to 2 (SettleTime).
  // This gives checker two pulses buffer to sync to DUT pwm_o pulse accurately.
  localparam int SettleTime = 2;

  // global settings
  bit                               regwen                   =  0;
  cfg_reg_t                         channel_cfg              = '0;
  bit [PWM_NUM_CHANNELS-1:0]        channel_en               = '0;
  bit [PWM_NUM_CHANNELS-1:0]        prev_channel_en          = '0;
  bit [PWM_NUM_CHANNELS-1:0]        invert                   = '0;
  state_e                           blink_state[PWM_NUM_CHANNELS] = '{default:CycleA};
  int                               blink_cnt[PWM_NUM_CHANNELS]   = '{default:0};
  int                               ignore_start_pulse[PWM_NUM_CHANNELS]   = '{default:2};
  int                               ignore_state_change[PWM_NUM_CHANNELS]   = '{default:0};
  uint                              subcycle_cnt[PWM_NUM_CHANNELS]   = '{default:1};
  // bit 16 is added for overflow
  bit [16:0]                        int_dc[PWM_NUM_CHANNELS]   = '{default:0};
  param_reg_t                       channel_param[PWM_NUM_CHANNELS];
  dc_blink_t                        duty_cycle[PWM_NUM_CHANNELS];
  dc_blink_t                        blink[PWM_NUM_CHANNELS];
  uint                              initial_dc[PWM_NUM_CHANNELS]   = '{default:0};
  string                            txt                      ="";

  // UVM phases
  extern function void build_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);
  extern function void check_phase(uvm_phase phase);

  // Check and update predictions based on a single TL message seen at the 'ral_name' register
  // interface. 'channel' determines if the fields of 'item' capture either an A or D channel
  // message.
  extern virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);

  // Track a reset signal
  extern virtual function void reset(string kind = "HARD");

  // Run forever, comparing items from the monitor on the given channel with the items that we
  // expect to be generated (based on the scoreboard's model of the config registers)
  extern task compare_trans(int channel);

  // Compute an expected pwm_item that we would like the monitor to see, based on the current
  // configuration registers.
  extern task generate_exp_item(ref pwm_item item, input bit [PWM_NUM_CHANNELS-1:0] channel);

endclass : pwm_scoreboard

function void pwm_scoreboard::build_phase(uvm_phase phase);
  super.build_phase(phase);
  for (int i = 0; i < PWM_NUM_CHANNELS; i++) begin
    item_fifo[i] = new($sformatf("item_fifo[%0d]", i), this);
  end
endfunction

task pwm_scoreboard::run_phase(uvm_phase phase);
  super.run_phase(phase);

  forever begin
    `DV_SPINWAIT_EXIT(
      fork
        compare_trans(0);
        compare_trans(1);
        compare_trans(2);
        compare_trans(3);
        compare_trans(4);
        compare_trans(5);
      join,
      @(negedge cfg.clk_rst_vif.rst_n),
    )
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
    case (csr.get_name())
    "regwen": begin
      regwen = item.a_data[0];
      `uvm_info(`gfn, $sformatf("Register Write en: %0b", regwen), UVM_HIGH)
    end

    "pwm_en": begin
      channel_en = item.a_data[PWM_NUM_CHANNELS-1:0];
      foreach(channel_en[ii]) begin
      bit pwm_en = get_field_val(ral.pwm_en[0].en[ii],item.a_data);
        if (pwm_en)begin
          `uvm_info(`gfn, $sformatf("detected toggle of channel[%d]", ii), UVM_HIGH)
          blink_state[ii] = CycleA;
        end
        txt = { txt, $sformatf("\n Channel[%d] : %0b",ii, channel_en[ii]) };
        if (cfg.en_cov) begin
          cov.lowpower_cg.sample(cfg.clk_rst_vif.clk_gate,
                                 $sformatf("cfg.m_pwm_monitor_[%0d]_vif", ii));
        end
       end
        `uvm_info(`gfn, $sformatf("Setting channel enables %s ", txt), UVM_HIGH)
        txt = "";
        prev_channel_en = channel_en;
      end

    "cfg": begin
        channel_cfg.ClkDiv = get_field_val(ral.cfg.clk_div, item.a_data);
        channel_cfg.DcResn = get_field_val(ral.cfg.dc_resn, item.a_data);
        channel_cfg.CntrEn = get_field_val(ral.cfg.cntr_en, item.a_data);
        `uvm_info(`gfn,
                  $sformatf("PWM global cfg: \n Clk Div: %0h, \n Dc Resn: %0h, \n Cntr en: %0b:",
                            channel_cfg.ClkDiv, channel_cfg.DcResn, channel_cfg.CntrEn), UVM_HIGH)
      end

    "invert": begin
        invert = item.a_data[PWM_NUM_CHANNELS-1:0];
        foreach(invert[ii]) begin
          txt = {txt, $sformatf("\n Invert Channel[%d] : %0b",ii, invert[ii])};
        end
        `uvm_info(`gfn, $sformatf("Setting channel Inverts %s ", txt), UVM_HIGH)
      end

    "pwm_param_0",
    "pwm_param_1",
    "pwm_param_2",
    "pwm_param_3",
    "pwm_param_4",
    "pwm_param_5": begin
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

     "duty_cycle_0",
     "duty_cycle_1",
     "duty_cycle_2",
     "duty_cycle_3",
     "duty_cycle_4",
     "duty_cycle_5": begin
        int idx = get_multireg_idx(csr_name);
        duty_cycle[idx].A = get_field_val(ral.duty_cycle[idx].a, item.a_data);
        duty_cycle[idx].B = get_field_val(ral.duty_cycle[idx].b, item.a_data);
        `uvm_info(`gfn, $sformatf("\n Setting channel[%d] duty cycle A:%0h B:%0h",
                                  idx, duty_cycle[idx].A ,duty_cycle[idx].B), UVM_HIGH)
      end

      "blink_param_0",
      "blink_param_1",
      "blink_param_2",
      "blink_param_3",
      "blink_param_4",
      "blink_param_5": begin
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

  // Sample for coverage
  if (cfg.en_cov) begin
    cov.clock_cg.sample(cfg.get_clk_core_freq(), cfg.clk_rst_vif.clk_freq_mhz);
    cov.cfg_cg.sample(channel_cfg.ClkDiv, channel_cfg.DcResn, channel_cfg.CntrEn);
    foreach (channel_en[ii]) begin
     cov.pwm_chan_en_inv_cg.sample(channel_en, invert);
     cov.pwm_per_channel_cg.sample(
       channel_en,
       invert,
       channel_param[ii].PhaseDelay,
       channel_param[ii].BlinkEn,
       channel_param[ii].HtbtEn,
       duty_cycle[ii].A,
       duty_cycle[ii].B,
       blink[ii].A,
       blink[ii].B);
    end
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

function void pwm_scoreboard::reset(string kind = "HARD");
  super.reset(kind);
  for (int i = 0; i < PWM_NUM_CHANNELS; i++) begin
    item_fifo[i].flush();
  end
endfunction

task pwm_scoreboard::compare_trans(int channel);
  pwm_item compare_item = new($sformatf("expected_item_%0d", channel));
  pwm_item input_item   = new($sformatf("input_item_%0d", channel));
  string txt            = "";
  int    p = 0;

  forever begin
    // as this DUT signals needs to be evaluated over time they are only evaluated when the channel
    // is off. this way it is known what the first and last item are as they might deviate from the
    // settings due to rounding and termination.

    // The very first item will be when the monitor detects the first active edge
    // it will have no information
    // wait for the first expected item
    if((ignore_start_pulse[channel] == 2 ) || ( ignore_start_pulse[channel] == 1 )) begin
      item_fifo[channel].get(input_item);
      generate_exp_item(compare_item, channel);
    end else begin
      item_fifo[channel].get(input_item);
      generate_exp_item(compare_item, channel);
      // After the state has switched to different state, settings will change
      // Comparison ignored till two pulses
      if(!((ignore_state_change[channel] == 2 ) || (ignore_state_change[channel] == 1 ))) begin
        // ignore items when resolution would round the duty cycle to 0 or 100
        if((compare_item.active_cnt != 0) && (compare_item.inactive_cnt != 0)
           && (input_item.period == compare_item.period)) begin
          if(!input_item.compare(compare_item)) begin
            `uvm_error(`gfn, $sformatf("\n PWM :: Channel = [%0d] did not MATCH", channel))
            `uvm_info(`gfn, $sformatf("\n PWM :: Channel = [%0d] EXPECTED CONTENT \n %s",
                                      channel, compare_item.sprint()),UVM_HIGH)
            `uvm_info(`gfn, $sformatf("\n PWM :: Channel = [%0d] DUT CONTENT \n %s",
                                      channel, input_item.sprint()),UVM_HIGH)
          end else begin
            `uvm_info(`gfn, $sformatf("\n PWM :: Channel = [%0d] MATCHED", channel),UVM_HIGH)
            `uvm_info(`gfn, $sformatf("\n PWM :: Channel = [%0d] EXPECTED CONTENT \n %s",
                                      channel, compare_item.sprint()),UVM_HIGH)
            `uvm_info(`gfn, $sformatf("\n PWM :: Channel = [%0d] DUT CONTENT \n %s",
                                      channel, input_item.sprint()),UVM_HIGH)
          end
        end
      end
      ignore_state_change[channel] -= 1 ;
    end
    ignore_start_pulse[channel] -= 1 ;
  end
endtask : compare_trans

task pwm_scoreboard::generate_exp_item(ref pwm_item                     item,
                                       input bit [PWM_NUM_CHANNELS-1:0] channel);
  uint beats_cycle     = 0;
  uint period          = 0;
  uint high_cycles     = 0;
  uint low_cycles      = 0;
  uint phase_count     = 0;
  dc_mod_e dc_mod;

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
            int_dc[channel] = duty_cycle[channel].A;
          end else begin
            blink_state[channel] = CycleB;
            blink_cnt[channel]   = blink[channel].B;
            int_dc[channel] = duty_cycle[channel].B;
          end
          ignore_state_change[channel] = SettleTime ;
        end else begin
          int_dc[channel] = (blink_state[channel] == CycleA) ? duty_cycle[channel].A :
            duty_cycle[channel].B;
          blink_cnt[channel] -= 1;
        end
      end
      1'b1: begin
        // When HTBT_EN is set, the duty cycle increases (or decreases) linearly from
        // DUTY_CYCLE.A to DUTY_CYCLE.B and back, in steps of blink.B (BLINK_PARAM.Y+1) with an
        // increment (decrement) once every blink.A (BLINK_PARAM.X+1) PWM cycles.
        case (blink_state[channel])
          CycleA: begin
            // current duty cycle
            int_dc[channel] = (initial_dc[channel]) ? int_dc[channel] : duty_cycle[channel].A;
            // when subcycle_cnt is equal to (BLINK_PARAM.X+1)
            if (subcycle_cnt[channel] == (blink[channel].A + 1)) begin
              // increment (decrement) int_dc by (BLINK_PARAM.Y+1)
              int_dc[channel] = (dc_mod == 1'b0) ?
                (int_dc[channel] - (blink[channel].B + 1)) :
                (int_dc[channel] + (blink[channel].B + 1));
              // reset subcycle_cnt after increment (decrement)
              subcycle_cnt[channel] = LocalCount;
              ignore_state_change[channel] = SettleTime ;
              initial_dc[channel]++;
            end else begin
              // else increment subcycle_cnt
              subcycle_cnt[channel]++;
              initial_dc[channel]++;
            end
            // enter CycleB when duty cycle is reached
            case (dc_mod)
              LargeA: begin
                if (int_dc[channel] <= duty_cycle[channel].B) begin
                  blink_state[channel] = CycleB;
                  subcycle_cnt[channel] = LocalCount;
                  ignore_state_change[channel] = SettleTime ;
                  initial_dc[channel] = Init;
                end
              end
              LargeB: begin
                if (int_dc[channel] >= duty_cycle[channel].B) begin
                  blink_state[channel] = CycleB;
                  ignore_state_change[channel] = SettleTime ;
                  subcycle_cnt[channel] = LocalCount;
                  initial_dc[channel] = Init;
                end
              end
              default: begin
                `uvm_info(`gfn, $sformatf("Error: Invalid: dc_mod == %s.", dc_mod), UVM_HIGH)
              end
            endcase
          end
          CycleB: begin
            if (subcycle_cnt[channel] == (blink[channel].A + 1'b1)) begin
              int_dc[channel] = (dc_mod == 1'b1) ?
                (int_dc[channel] - (blink[channel].B + 1'b1)) :
                (int_dc[channel] + (blink[channel].B + 1'b1));
              subcycle_cnt[channel] = LocalCount;
              ignore_state_change[channel] = SettleTime ;
              initial_dc[channel]++;
            end else begin
              subcycle_cnt[channel]++;
              initial_dc[channel]++;
            end
            case (dc_mod)
              LargeB: begin
                if (int_dc[channel] <= duty_cycle[channel].A) begin
                  blink_state[channel] = CycleA;
                  ignore_state_change[channel] = SettleTime ;
                  subcycle_cnt[channel] = LocalCount;
                  initial_dc[channel] = Init;
                end
              end
              LargeA: begin
                if (int_dc[channel] >= duty_cycle[channel].A) begin
                  blink_state[channel] = CycleA;
                  ignore_state_change[channel] = SettleTime ;
                  subcycle_cnt[channel] = LocalCount;
                  initial_dc[channel] = Init;
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
  end else int_dc[channel] = duty_cycle[channel].A;
  if ( subcycle_cnt[channel] == blink[channel].A + 1'b1 ) begin
    ignore_state_change[channel] = SettleTime ;
  end

  // Overflow condition  check
  if ((int_dc[channel][16] == 1) && (duty_cycle[channel].B > duty_cycle[channel].A)) begin
      if (cfg.en_cov) begin
        cov.dc_uf_ovf_tb_cg.sample(channel, int_dc[channel][16]);
      end
      int_dc[channel][15:0] = 16'hFFFF;
      initial_dc[channel] = LocalCount;
      if (subcycle_cnt[channel] == (blink[channel].A + 1'b1)) begin
          // This calculation is done to bring back previous state of DC before overflow occurs
          // Instead of int_dc[channel] = int_dc[channel] - blink[channel].B + 1'b1 ;
          int_dc[channel][15:0] = duty_cycle[channel].A + 1 +
            (((16'hFFFF - duty_cycle[channel].A )/(blink[channel].B + 1'b1)))*blink[channel].B;
          int_dc[channel][16]   = 0 ;
          subcycle_cnt[channel] = LocalCount;
      end
      blink_state[channel] = CycleA;
  end
  // Underflow condition check
  if ((int_dc[channel][16] == 1) && (duty_cycle[channel].B < duty_cycle[channel].A)) begin
      if (cfg.en_cov) begin
        cov.dc_uf_ovf_tb_cg.sample(channel, ~int_dc[channel][16]);
      end
      int_dc[channel] = int_dc[channel] + blink[channel].B + 1'b1 ;
      int_dc[channel][16] = 0 ;
      subcycle_cnt[channel] = LocalCount;
      blink_state[channel] = CycleB;
  end

  beats_cycle = 2**(channel_cfg.DcResn + 1);
  period      = beats_cycle * (channel_cfg.ClkDiv + 1);
  high_cycles = (int_dc[channel][15:0] >> (16 - (channel_cfg.DcResn + 1)))
                * (channel_cfg.ClkDiv + 1);
  low_cycles  = period - high_cycles;
  // Each PWM pulse cycle is divided into 2^DC_RESN+1 beats, per beat the 16-bit phase counter
  // increments by 2^(16-DC_RESN-1)(modulo 65536)
  phase_count = (period / (2**(channel_cfg.DcResn + 1)) * (2**(16 - (channel_cfg.DcResn - 1))));

  item.monitor_id      = channel;
  item.invert          = invert[channel];
  item.period          = period;
  item.active_cnt      = high_cycles;
  item.inactive_cnt    = low_cycles;
  item.duty_cycle      = item.get_duty_cycle();
  item.phase           = (phase_count % 65536);

endtask
