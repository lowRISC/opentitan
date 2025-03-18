// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aon_timer_scoreboard extends cip_base_scoreboard #(
    .CFG_T(aon_timer_env_cfg),
    .RAL_T(aon_timer_reg_block),
    .COV_T(aon_timer_env_cov)
  );
  `uvm_component_utils(aon_timer_scoreboard)

  // local variables
  local bit  wkup_en;
  local bit  wkup_num_update_due;
  local bit [63:0] wkup_count;
  local uint prescaler;
  local bit [63:0] wkup_thold;

  local bit  wdog_en;
  local bit  wdog_regwen;
  local bit  wdog_pause_in_sleep;
  local bit  wdog_num_update_due;

  local uint wdog_count;
  local uint bark_thold;
  local uint bite_thold;

  local bit  wkup_cause;
  local bit [63:0] wkup_num;
  local bit [31:0] wdog_bark_num;
  local bit [31:0] wdog_bite_num;

  // expected values
  local bit [1:0] intr_status_exp;
  local bit wdog_rst_req_exp = 0;

  typedef enum logic {
    WKUP = 1'b0,
    WDOG = 1'b1
  } timers_e;

  // Prediction and checking of the loosely-timed registers.
  aon_timer_intr_timed_regs timed_regs;

  // BFM state information for the loosely-timed registers.
  typedef struct {
    uvm_reg_data_t r[aon_timer_intr_timed_regs::timed_reg_e];
  } bfm_timed_regs_t;

  // Previous state
  bfm_timed_regs_t prev_timed_regs;

  // UVM events to trigger the count for WDOG/WKUP timer to avoid any potential race condition
  uvm_event wkup_count_ev = new();
  uvm_event wdog_count_ev = new();

  event sample_wkup_timer_coverage;
  event sample_wdog_bark_timer_coverage;
  event sample_wdog_bite_timer_coverage;
  bit predicted_wkup_intr_q[$];
  bit predicted_wdog_intr_q[$];
  int unsigned ongoing_intr_state_read;

  // A write of 0 to wkup_cause may take some delay to arrive because of CDC crossing (from the TL
  // bus on the main clock to the register on the aon clock). This timing might overlap with an
  // expected watchdog interrupt. To avoid this causing a problem, we avoid checking the predicted
  // value (in run_wdog_bark_timer) if the timing collides.
  //
  // aon_clk_cycle is a counter of AON cycles which is kept in sync by track_aon_clk_cycle. It gets
  // snapshotted to last_wkup_cause_write_aon_clk_cycle in predict_wkup_cause when the write enable
  // for the aon_wkup_cause register drops. We can see that there has been a collision if the two
  // values are equal.
  // last_wkup_cause_write_aon_clk_cycle variable doesn't have a race condition even if both SYS and
  // AON clock have the pos-edge at the same time, since the variable is used a couple of sys-clock
  // ticks (or more, depending on CDC crossing) after the AON clock cycle because that's when the
  // interrupt check is carried out.
  int unsigned aon_clk_cycle = 0;
  int unsigned last_wkup_cause_write_aon_clk_cycle = 0;

  extern function new (string name="", uvm_component parent=null);
  extern function void build_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);
  extern function void check_phase(uvm_phase phase);
  // Convenience task which keeps count of a given AON clock cycle. Currently only used to
  // distinguish the case when a write to wkup_cause occurs at the same time as a interrupt being
  // high
  extern task track_aon_clk_cycle();
  // Collects interrupt coverage from RTL interrupts by directly sampling the RTL output
  extern task collect_fcov_from_rtl_interrupts();
  extern virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
  // Model the timers and interrupts for WKUP/WDOG and compare them against the actual values
  // the task doesn't return
  extern virtual task check_interrupt();
  // Whenever the WKUP or WDOG counters are enabled we recalculate the count in case the count had
  // changed since last time the counter was enabled
  extern task recalculate_num_cycles(timers_e tmr);
  // This tasks runs forever and it calculates the  number of clock cycles until an interrupt is
  // raised. The number of clock cycles is stored in variables wkup_num and wdog_bark/bite_num.
  // The WKUP timer takes the prescaler into consideration when it comes to calculating clock cycles
  extern virtual task compute_num_clks();
  // Blocks when the 'pause_in_sleep' signal is set as well as the internal RTL aon_sleep_mode
  // signal. Otherwise, the predictions may be late/early with regards to the RTL.
  extern virtual task wait_for_sleep();
  // The run_wkup_timer and run_wdog_bark/bite_timer are independent tasks which run forever and
  // can safely be killed.
  // Run wkup/wdog timers predicts the interrupt of each kind (or subkind for WDOG timer with bite
  // and bark) and check against the actual value when an interrupt is due.
  // The threads also contribute towards coverage and get killed whenever there is a reset or the
  // enable bit for their respective counter is not set
  extern virtual task run_wkup_timer();
  extern virtual task run_wdog_bark_timer();
  extern virtual task run_wdog_bite_timer();

  // Models the wdog_bite/bark behavior and checks the interrupt propagates. It receives by reference a
  // 'predicting_interrupt' flag which gets set when an interrupt is meant to propagate in spite of
  // the timer being disabled.
  extern task model_and_check_wdog_bite(ref bit predicting_interrupt);
  extern task model_and_check_wdog_bark(ref bit predicting_interrupt);
  // Models the wkup timer and checks interrupt propagates, it takes the argument 'predictin_interrupt'
  // by reference for moments in which an interrupt propagates even when the timer has just been disabled.
  extern task model_and_check_wkup(ref bit predicting_interrupt);

  // The three collect_*_coverage below tasks run forever and can be safely killed at any time.
  //
  // collect_wkup_timer_coverage: Whenever the sample_coverage event fires, sample the 64-bit
  // wkup_count counter, threshold value and interrupt for wake_up_timer_thold_hit_cg covergroup.
  extern task collect_wkup_timer_coverage(event sample_coverage);
  // collect_wdog_bark_timer_coverage: Whenever the sample_coverage event fires, sample the 32-bit
  // wdog_count counter, threshold value and interrupt for watchdog_timer_bark_thold_hit_cg
  // covergroup.
  extern task collect_wdog_bark_timer_coverage(event sample_coverage);
  // collect_wdog_bite_timer_coverage: Whenever the sample_coverage event fires, sample the 32-bit
  // wdog_count counter, threshold value and interrupt for watchdog_timer_bite_thold_hit_cg
  // covergroup.
  extern task collect_wdog_bite_timer_coverage(event sample_coverage);

  // Sets both predicted timed register (WKUP/WDOG) values, captured from intr_state_exp.
  extern function void capture_timed_regs(output bfm_timed_regs_t state);
  // The argument passed by reference `state` stores the value predicted for intr_state for each
  // type of timer, `r` and tmr refer to the type of timer to predict for the timed and the expected
  // interrupts respectively
  extern function void capture_timed_regs_independently(ref bfm_timed_regs_t state,
                                                        aon_timer_intr_timed_regs::timed_reg_e r,
                                                        timers_e tmr);
  // Initialise the timed regs (called in the build_phase)
  extern function void init_timed_regs();
  // need separate wdog/wkup update functions in case they are called at the same time
  extern function void update_timed_regs_independently(timers_e tmr);
  // Update the model side of the WKUP/WDOG(or both) timed registers
  extern function void update_timed_regs();
  extern function void update_timed_regs_wdog();
  extern function void update_timed_regs_wkup();

  // Predicts register wkup_cause whenever the busy flag is 0 and blocks other parts of the TB to
  // predict it's value until an ongoing prediction finishes
  // In addition, the prediction can be delayed by setting 'wait_for_we' if the TB wants the
  // prediction to proceed after the wkup_cause write crosses the CDC boundary to be in sync with
  // the RTL.
  extern task predict_wkup_cause(bit wkup_cause, bit wait_for_we);
  // Predicts register intr_state whenever the busy flag is 0. It checks the prediction went through
  // and blocks other parts of the TB to predict its value until an ongoing prediction finishes
  extern task predict_intr_state(bit [1:0] pred_intr_state, bit field_only = 0, bit is_wkup = 0);

  // Update tasks wait for the value to cross CDC boundaries by checking the write enable
  // before the TB starts counting
  extern task update_wdog_or_wkup_reg_timely(string path, timers_e timer_type);
  extern task update_wdog_count_timely();
  extern task update_wdog_bite_thold_timely();
  extern task update_wdog_bark_thold_timely();
  extern task update_wkup_count_lo_timely();
  extern task update_wkup_count_hi_timely();
  extern task update_wkup_thold_lo_timely();
  extern task update_wkup_thold_hi_timely();

  // Pushes predicted values for wdog/wkup_interrupt in a queue and keeps track of the RTL until
  // the committed value propagates and becomes the register value
  extern task wkup_intr_predicted_values(bit exp_wkup_intr);
  extern task wdog_intr_predicted_values(bit exp_wdog_intr);
  // Checks the predicted interrupt value is the current RTL value by backdoor reads
  extern task check_intr_value_propagated(timers_e timer_type);

  // Converts from timers_e to 'timed_reg_e'
  extern function aon_timer_intr_timed_regs::timed_reg_e timers_e2time_reg_e(timers_e timer_type);
  // Check the value of `intr_wdog_timer_bark/wkup_timer_expired_o' matched the one in the
  // intr_state register by the timed registers.
  // intr_status_exp[WDOG] can't be used to compare since its value may have been wiped out by the
  // time the comparison is carried out
  extern function void check_aon_domain_interrupt(timers_e timer_type);
  // Returns either `predicted_wdog_intr_q` or `predicted_wkup_intr_q` by reference depending on the
  // timer type passed
  extern function void return_pred_intr_q(timers_e timer_type, ref bit pred_q[$]);
  // Checks the expected mirrored value against the value returned in the TL-UL read for intr_state
  extern function void check_intr_state_bit(timers_e timer_type, bit actual_value);

  // Convenience function to check if the wkup/wdog_ctrl.enable bits are set or not depending on
  // whether the enable argument is 0 or 1.
  extern task wait_for_wdog_enable_matching(bit enable);
  extern task wait_for_wkup_enable_matching(bit enable);

  extern virtual function void reset(string kind = "HARD");

endclass : aon_timer_scoreboard

function aon_timer_scoreboard::new (string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction : new

function void aon_timer_scoreboard::build_phase(uvm_phase phase);
  super.build_phase(phase);

  // Set-up timed registers (intr_state):
  timed_regs = aon_timer_intr_timed_regs::type_id::create("timed_regs");
  timed_regs.clk_rst_vif = cfg.clk_rst_vif;
  timed_regs.ral = ral;
  init_timed_regs();
endfunction : build_phase

function void aon_timer_scoreboard::check_phase(uvm_phase phase);
  super.check_phase(phase);
  if (ongoing_intr_state_read > 0) begin
    `uvm_fatal(`gfn, $sformatf("%m - ongoing_intr_state_read=%0d should be 0",
                               ongoing_intr_state_read))
  end
endfunction

task aon_timer_scoreboard::run_phase(uvm_phase phase);
  super.run_phase(phase);
  fork
    track_aon_clk_cycle();
    compute_num_clks();
    check_interrupt();
    collect_fcov_from_rtl_interrupts();
    timed_regs.check_predictions(cfg.under_reset);
    collect_wkup_timer_coverage(sample_wkup_timer_coverage);
    collect_wdog_bark_timer_coverage(sample_wdog_bark_timer_coverage);
    collect_wdog_bite_timer_coverage(sample_wdog_bite_timer_coverage);
  join_none
endtask : run_phase

task aon_timer_scoreboard::track_aon_clk_cycle();
  forever begin
    cfg.aon_clk_rst_vif.wait_clks(1); // enabled is synchronised to the aon domain
    aon_clk_cycle++;
  end
endtask

function void aon_timer_scoreboard::capture_timed_regs(output bfm_timed_regs_t state);
  aon_timer_intr_timed_regs::timed_reg_e r = aon_timer_intr_timed_regs::TimedIntrStateWdogBark;
  timers_e tmr_type = WDOG;
  capture_timed_regs_independently(.state(state), .r(r), .tmr(tmr_type));
  r = aon_timer_intr_timed_regs::TimedIntrStateWkupExpired;
  tmr_type = WKUP;
  capture_timed_regs_independently(.state(state), .r(r), .tmr(tmr_type));
endfunction : capture_timed_regs

function void aon_timer_scoreboard::capture_timed_regs_independently(ref bfm_timed_regs_t state,
                                                                     aon_timer_intr_timed_regs::
                                                                     timed_reg_e r, timers_e tmr);
  state.r[r] = intr_status_exp[tmr];
endfunction : capture_timed_regs_independently

function void aon_timer_scoreboard::init_timed_regs();
  bfm_timed_regs_t init_regs;
  aon_timer_intr_timed_regs::timed_reg_e r;
  // Maximum delay (in DUT clock cycles) for a prediction to be met; most delays should take
  // only a few cycles for internal changes to propagate, but some are substantially longer
  // oweing to the immediate operation of the functional model.
  int unsigned max_delay = 5;
  // Capture the initial state of the loosely-timed registers.
  capture_timed_regs(init_regs);

  // Remember the register state.
  prev_timed_regs = init_regs;
  // Create the register descriptions.
  r = r.first();
  for (int i = 0; i < r.num(); i++) begin
    timed_reg tr = timed_reg::type_id::create("tr");
    uvm_reg_data_t init_val = 0;
    dv_base_reg_field fields[$];
    // Collect the field descriptions for this register.
    if (!(r inside {aon_timer_intr_timed_regs::TimedIntrStateWdogBark,
                    aon_timer_intr_timed_regs::TimedIntrStateWkupExpired}))
      `uvm_fatal(`gfn, "Invalid/unknown register")
    ral.intr_state.get_dv_base_reg_fields(fields);

    // Report the initial value of this register as predicted by the BFM.
    `uvm_info(`gfn, $sformatf("Reg %p : initial value 0x%0x", r, init_regs.r[r]), UVM_MEDIUM)
    // Collect the initial values of the register fields, dropping any that we cannot predict.
    foreach(fields[f]) begin
      string field_name = fields[f].get_name();
      // Extract the initial value of this register field from the modeled register state.
      uvm_reg_data_t mask = (1 << fields[f].get_n_bits()) - 1;
      init_val = (init_regs.r[r] >> fields[f].get_lsb_pos()) & mask;
      tr.add_field(fields[f], init_val, max_delay);
      `uvm_info(`gfn, $sformatf("Register %p field %s : initially 0x%0x", r,
                                field_name, init_val), UVM_MEDIUM)
    end
    timed_regs.timed[r] = tr;
    r = r.next();
  end
endfunction : init_timed_regs

// Update the expectations for the timed registers; this should be called after any operation on
// the BFM that could affect the state of one or more of the timed registers.
function void aon_timer_scoreboard::update_timed_regs();
  aon_timer_intr_timed_regs::timed_reg_e r = r.first();
  bfm_timed_regs_t new_regs;
  capture_timed_regs(new_regs);
  `uvm_info(`gfn, "After capturing timed regs", UVM_DEBUG)
  r = r.first();
  for (int i = 0; i < r.num(); i++) begin
    // Has there been a change in the bits that we can predict?
    uvm_reg_data_t unpred_mask = timed_regs.timed[r].unpred_mask;
    if ((new_regs.r[r] & ~unpred_mask) != (prev_timed_regs.r[r] & ~unpred_mask)) begin
      timed_regs.predict(r, prev_timed_regs.r[r], new_regs.r[r]);
    end
    r = r.next();
  end
  // Remember the register state.
  prev_timed_regs = new_regs;
endfunction : update_timed_regs

// Updates timed register independently
function void aon_timer_scoreboard::update_timed_regs_independently(timers_e tmr);
  bfm_timed_regs_t new_regs;
  aon_timer_intr_timed_regs::timed_reg_e r = timers_e2time_reg_e(tmr);
  uvm_reg_data_t unpred_mask = timed_regs.timed[r].unpred_mask;

  capture_timed_regs_independently(.state(new_regs), .r(r), .tmr(tmr));
  `uvm_info(`gfn, $sformatf("Updating Timed regs #intr_state - %0s",tmr.name()), UVM_DEBUG)

  // Has there been a change in the bits that we can predict?
  if ((new_regs.r[r] & ~unpred_mask) != (prev_timed_regs.r[r] & ~unpred_mask)) begin
    timed_regs.predict(r, prev_timed_regs.r[r], new_regs.r[r]);
  end
  // Remember the register state.
  prev_timed_regs = new_regs;
endfunction : update_timed_regs_independently

// need separate wdog/wkup update functions in case they are called at the same time
function void aon_timer_scoreboard::update_timed_regs_wdog();
  update_timed_regs_independently(.tmr(timers_e'(WDOG)));
endfunction : update_timed_regs_wdog

function void aon_timer_scoreboard::update_timed_regs_wkup();
  update_timed_regs_independently(.tmr(timers_e'(WKUP)));
endfunction : update_timed_regs_wkup

task aon_timer_scoreboard::collect_fcov_from_rtl_interrupts();
  forever begin
    @(cfg.aon_intr_vif.pins);
    // Sample interrupt pin coverage for interrupt pins
    if (cfg.en_cov) begin
      foreach (cfg.aon_intr_vif.pins[i]) begin
        cov.intr_pins_cg.sample(i, cfg.aon_intr_vif.sample_pin(.idx(i)));
      end
    end
  end
endtask : collect_fcov_from_rtl_interrupts

task aon_timer_scoreboard::predict_wkup_cause(bit wkup_cause, bit wait_for_we);
  fork
    begin : non_blocking_fork
      fork
        begin : iso_fork
          fork
            begin : wkup_cause_timely
              // Blocks only if 'predicting_value' = 1
              if (wait_for_we)
                cfg.wait_for_we_pulse(".u_reg.aon_wkup_cause_we");

              if (!ral.wkup_cause.predict(.value(wkup_cause), .kind(UVM_PREDICT_READ)))
                `uvm_fatal(`gfn, $sformatf("%s prediction failed", `gmv(ral.wkup_cause)))
              `uvm_info(`gfn, $sformatf("Updated predicted WKUP-CAUSE to 0x%0x", wkup_cause),
                        UVM_DEBUG)
              if (wait_for_we)
                last_wkup_cause_write_aon_clk_cycle = aon_clk_cycle;
            end : wkup_cause_timely
            begin : reset_kill
              wait (under_reset);
            end : reset_kill
          join_any
          disable fork;
        end : iso_fork
      join
    end : non_blocking_fork
  join_none
endtask : predict_wkup_cause

// Update functions waits for the value to cross CDC boundaries before the TB starts counting
task aon_timer_scoreboard::update_wdog_or_wkup_reg_timely(string path, timers_e timer_type);
  fork
    begin: iso_fork
      fork
        begin : hdl_read_wdog_wkup_reg_we
          cfg.wait_for_we_pulse(path);
          // Update once the changes have kicked in.
          case(timer_type)
            WKUP: wkup_num_update_due = 1;
            WDOG: wdog_num_update_due = 1;
            default: `uvm_fatal(`gfn, $sformatf("Incorrect timer type:%0s", timer_type.name()))
          endcase
        end : hdl_read_wdog_wkup_reg_we
        begin : reset_kill
          wait (under_reset);
        end : reset_kill
      join_any
      disable fork;
    end : iso_fork
  join
endtask : update_wdog_or_wkup_reg_timely

// Update functions waits for the value to cross CDC boundaries before the TB starts counting
task aon_timer_scoreboard::update_wdog_count_timely();
  fork
    begin : non_blocking_fork
      update_wdog_or_wkup_reg_timely(.path(".u_reg.aon_wdog_count_we"), .timer_type(WDOG));
      -> sample_wdog_bite_timer_coverage;
      -> sample_wdog_bark_timer_coverage;
    end : non_blocking_fork
  join_none
endtask : update_wdog_count_timely

task aon_timer_scoreboard::update_wdog_bite_thold_timely();
  fork
    begin : non_blocking_fork
      update_wdog_or_wkup_reg_timely(.path(".u_reg.aon_wdog_bite_thold_gated_we"),
                                     .timer_type(WDOG));
      -> sample_wdog_bite_timer_coverage;
    end : non_blocking_fork
  join_none
endtask : update_wdog_bite_thold_timely

task aon_timer_scoreboard::update_wdog_bark_thold_timely();
  fork
    begin : non_blocking_fork
      update_wdog_or_wkup_reg_timely(.path(".u_reg.aon_wdog_bark_thold_gated_we"),
                                     .timer_type(WDOG));
      -> sample_wdog_bark_timer_coverage;
    end : non_blocking_fork
  join_none
endtask : update_wdog_bark_thold_timely

task aon_timer_scoreboard::update_wkup_count_lo_timely();
  fork
    begin : non_blocking_fork
      update_wdog_or_wkup_reg_timely(.path(".u_reg.aon_wkup_count_lo_we"), .timer_type(WKUP));
      -> sample_wkup_timer_coverage;
    end : non_blocking_fork
  join_none
endtask : update_wkup_count_lo_timely

task aon_timer_scoreboard::update_wkup_count_hi_timely();
  fork
    begin : non_blocking_fork
      update_wdog_or_wkup_reg_timely(.path(".u_reg.aon_wkup_count_hi_we"), .timer_type(WKUP));
      -> sample_wkup_timer_coverage;
    end : non_blocking_fork
  join_none
endtask : update_wkup_count_hi_timely

task aon_timer_scoreboard::update_wkup_thold_lo_timely();
  fork
    begin : non_blocking_fork
      update_wdog_or_wkup_reg_timely(.path(".u_reg.aon_wkup_thold_lo_we"), .timer_type(WKUP));
      -> sample_wkup_timer_coverage;
    end : non_blocking_fork
  join_none
endtask : update_wkup_thold_lo_timely

task aon_timer_scoreboard::update_wkup_thold_hi_timely();
  fork
    begin : non_blocking_fork
      update_wdog_or_wkup_reg_timely(.path(".u_reg.aon_wkup_thold_hi_we"), .timer_type(WKUP));
      -> sample_wkup_timer_coverage;
    end: non_blocking_fork
  join_none
endtask : update_wkup_thold_hi_timely

task aon_timer_scoreboard::predict_intr_state(bit [1:0] pred_intr_state, bit field_only = 0,
                                              bit is_wkup=0);
  fork
    begin: non_blocking_fork
      `uvm_info(`gfn, $sformatf("%m - pred_intr_state = 0x%0x",pred_intr_state), UVM_DEBUG)
      fork
        begin: iso_fork
          fork
            begin : intr_state_timely
              bit exit_loop;
              // The update can occur at the same time as a read access. This could occur in the A
              // or D channels.
              // If we predicted an update during the A or D-phase, we need to hold the prediction
              // until after the whole access finishes.
              // If prediction occurs at the D-phase, we check the 'ongoing_intr_state_read' flag,
              // which was set in `process_tl_access` during the A-phase. We need to do this because
              // D-phase handshake doesn't give information related to the TL-access and address.
              while (cfg.m_tl_agent_cfg.vif.h2d.a_valid && cfg.m_tl_agent_cfg.vif.d2h.a_ready) begin
                if (cfg.m_tl_agent_cfg.vif.h2d.a_opcode == tlul_pkg::Get) begin
                  bit [AddrWidth - 1   : 0] a_addr = cfg.m_tl_agent_cfg.vif.h2d.a_address;
                  string                    ral_name = "aon_timer_reg_block";
                  uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(a_addr);
                  if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
                    uvm_reg csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);

                    if(csr != null) begin
                      if(csr.get_name() == "intr_state")
                        cfg.clk_rst_vif.wait_n_clks(1);
                      else
                        exit_loop = 1;
                    end
                    else
                      exit_loop = 1;
                  end
                  else
                    exit_loop = 1;
                end
                else
                  exit_loop = 1;

                if (exit_loop)
                  break;
              end
              // If the update occurs during the D-phase, we wait until the D-phase ends
              if (ongoing_intr_state_read > 0) begin
                while (cfg.m_tl_agent_cfg.vif.d2h.d_valid) begin
                  if (cfg.m_tl_agent_cfg.vif.h2d.d_ready) begin
                    cfg.clk_rst_vif.wait_n_clks(1);
                    // Leaving loop 1-cycle after handshake completion
                    break;
                  end
                  cfg.clk_rst_vif.wait_n_clks(1);
                end
              end

              if (!field_only) begin
                if (!ral.intr_state.predict(.value(pred_intr_state), .kind(UVM_PREDICT_READ) ))
                  `uvm_fatal(`gfn, $sformatf("%s prediction failed", ral.intr_state.get_name()))
              end
              else begin
                if (is_wkup) begin
                  if (!ral.intr_state.wkup_timer_expired.predict(.value(pred_intr_state[WKUP]),
                                                                 .kind(UVM_PREDICT_READ) ))
                    `uvm_fatal(`gfn, $sformatf("%s prediction failed",
                                               ral.intr_state.wkup_timer_expired.get_name()))
                end
                else begin
                  if (!ral.intr_state.wdog_timer_bark.predict(.value(pred_intr_state[WDOG]),
                                                              .kind(UVM_PREDICT_READ) ))
                    `uvm_fatal(`gfn, $sformatf("%s prediction failed",
                                               ral.intr_state.wdog_timer_bark.get_name()))
                end
              end
            end : intr_state_timely
            begin : reset_kill
              wait (under_reset);
            end : reset_kill
          join_any
          disable fork;
        end : iso_fork
      join
    end : non_blocking_fork
    join_none
endtask : predict_intr_state

task aon_timer_scoreboard::wkup_intr_predicted_values(bit exp_wkup_intr);
  static int unsigned last_cycle_count = 0;
  fork
    begin : non_blocking_fork
      if (last_cycle_count != timed_regs.time_now) begin
        `uvm_info(`gfn, $sformatf("%m - Predicted wkup_intr = 0x%0x", exp_wkup_intr), UVM_DEBUG)
        predicted_wkup_intr_q.push_back(exp_wkup_intr);
        last_cycle_count = timed_regs.time_now;
        fork
          begin: iso_fork
            fork
              begin : wait_values_to_propagate
                // do backdoor read and delete values no longer valid.
                check_intr_value_propagated(WKUP);
              end : wait_values_to_propagate
              begin : reset_kill
                wait (under_reset);
              end : reset_kill
            join_any
            disable fork;
          end : iso_fork
        join
      end
    end : non_blocking_fork
  join_none
endtask : wkup_intr_predicted_values

task aon_timer_scoreboard::wdog_intr_predicted_values(bit exp_wdog_intr);
  static int unsigned last_cycle_count = 0;
  fork
    begin : non_blocking_fork
      if (last_cycle_count != timed_regs.time_now) begin
        `uvm_info(`gfn, $sformatf("%m - Predicted wdog_intr = 0x%0x", exp_wdog_intr), UVM_DEBUG)
        predicted_wdog_intr_q.push_back(exp_wdog_intr);
        last_cycle_count = timed_regs.time_now;
        fork
          begin: iso_fork
            fork
              begin : wait_values_to_propagate
                // do backdoor read and delete values no longer valid.
                check_intr_value_propagated(WDOG);
              end : wait_values_to_propagate
              begin : reset_kill
                wait (under_reset);
              end : reset_kill
            join_any
            disable fork;
          end : iso_fork
        join
      end // if (last_cycle_count != timed_regs.time_now)
    end : non_blocking_fork
  join_none
endtask : wdog_intr_predicted_values

task aon_timer_scoreboard::check_intr_value_propagated(timers_e timer_type);
  int unsigned idx; // Idx to the latest prediction
  bit          exp_value;
  bit          act_data;
  bit          value_matched;

  case(timer_type)
    WKUP: begin
      if (predicted_wkup_intr_q.size == 0)
        `uvm_fatal(`gfn, "'predicted_wkup_intr_q' Queue is empty")
      idx = predicted_wkup_intr_q.size -1;
      // Synchronise with the next neg-edge
      cfg.clk_rst_vif.wait_n_clks(1);
      do begin
        csr_rd(.ptr(ral.intr_state.wkup_timer_expired),   .value(act_data), .backdoor(1));
        if (predicted_wkup_intr_q[idx] == act_data && ongoing_intr_state_read == 0) begin
          value_matched = 1;
          // Remove all the other predictions no longer valid:
          for (int i = 0; i < idx; i++)
            void'(predicted_wkup_intr_q.pop_front());
        end
        else //negedge to avoid a race condition
          cfg.clk_rst_vif.wait_n_clks(1);
      end
      while (value_matched == 0);
    end
    WDOG: begin
      if (predicted_wdog_intr_q.size == 0)
        `uvm_fatal(`gfn, "'predicted_wdog_intr_q' Queue is empty")
      idx = predicted_wdog_intr_q.size -1;
      // Synchronise with the next neg-edge
      cfg.clk_rst_vif.wait_n_clks(1);
      do begin
        csr_rd(.ptr(ral.intr_state.wdog_timer_bark),   .value(act_data), .backdoor(1));
        if (predicted_wdog_intr_q[idx] == act_data && ongoing_intr_state_read == 0) begin
          value_matched = 1;
          // Remove all the other predictions no longer valid:
          for (int i = 0; i < idx; i++)
            void'(predicted_wdog_intr_q.pop_front());
        end
        else
          cfg.clk_rst_vif.wait_n_clks(1);
      end
      while (value_matched == 0);

    end
  endcase
endtask : check_intr_value_propagated

task aon_timer_scoreboard::process_tl_access(tl_seq_item item, tl_channels_e channel,
                                             string ral_name);
  uvm_reg csr;
  bit     do_read_check   = 1'b1;
  bit     write           = item.is_write();
  uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

  bit addr_phase_read   = (!write && channel == AddrChannel);
  bit addr_phase_write  = (write && channel == AddrChannel);
  bit data_phase_read   = (!write && channel == DataChannel);
  bit data_phase_write  = (write && channel == DataChannel);

  // if access was to a valid csr, get the csr handle
  if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
    csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
    `DV_CHECK_NE_FATAL(csr, null)
  end
  else begin
    `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
  end

  // if incoming access is a write to a valid csr, then make updates right away
  if (addr_phase_write) begin
    // intr_state / wkup_cause are predicted in their own process
    if(csr.get_name() == "intr_state" || csr.get_name() == "wkup_cause")
      `uvm_info(`gfn, $sformatf("Write to %s", csr.get_name()), UVM_DEBUG)
    else begin
      if (!csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)))
        `uvm_fatal(`gfn, $sformatf("%s prediction failed", csr.get_name()))
    end
    if (cfg.en_cov) begin
      //Sample configuration coverage
      cov.timer_cfg_cg.sample(prescaler, bark_thold, bite_thold,
                              wkup_thold, wdog_regwen, wdog_pause_in_sleep, wkup_cause);
    end
  end

  // Counter to let the model know if a current read is being carried out. Otherwise, the TB may
  // think the actual RTL intr_state value is different from the value being reported back if the
  // change happens right around the same time as the access
  if (csr.get_name() == "intr_state" && addr_phase_read)
    ongoing_intr_state_read++;

  // process the csr req
  // for write, update local variable and fifo at address phase
  // for read, update predication at address phase and compare at data phase
  case (csr.get_name())
    // add individual case item for each csr
    "intr_state": begin
      // Interrupt state reads are checked here
      do_read_check = 1'b0;
      if (addr_phase_write) begin
        uint intr_state_val = item.a_mask[0] ? item.a_data : 0;
        bit update_prediction;
        `uvm_info(`gfn, $sformatf("Prior to update: intr_status_exp = 0x%0x",intr_status_exp),
                  UVM_DEBUG)
        if (intr_state_val[WKUP]) begin
          intr_status_exp[WKUP] = 1'b0;
          update_prediction = 1;
          wkup_intr_predicted_values(intr_status_exp[WKUP]);
        end
        if (intr_state_val[WDOG]) begin
          intr_status_exp[WDOG] = 1'b0;
          update_prediction = 1;
          wdog_intr_predicted_values(intr_status_exp[WDOG]);
        end

        if (update_prediction) begin
          uvm_reg_data_t predicted_intr_status;
          predicted_intr_status[WDOG] = intr_status_exp[WDOG];
          predicted_intr_status[WKUP] = intr_status_exp[WKUP];
          `uvm_info(`gfn, $sformatf("Updated intr_status_exp = 0x%0x",intr_status_exp),
                    UVM_DEBUG)
          predict_intr_state(predicted_intr_status);
          // The timed registers predictions need to be independent of each other
          if (intr_state_val[WDOG])
            update_timed_regs_wdog();
          if (intr_state_val[WKUP])
            update_timed_regs_wkup();
        end
      end
      else if (data_phase_read) begin
        check_intr_state_bit(.timer_type(WKUP), .actual_value(item.d_data[WKUP]));
        check_intr_state_bit(.timer_type(WDOG), .actual_value(item.d_data[WDOG]));
      end
      // INTR_EN register does not exists in AON timer because the interrupts are
      // enabled as long as timers are enabled.
      if (cfg.en_cov && data_phase_read) begin
        cov.intr_cg.sample(WKUP, wkup_en, item.d_data[WKUP]);
        cov.intr_cg.sample(WDOG, wdog_en, item.d_data[WDOG]);
      end
      if (cfg.en_cov) begin
        bit [1:0] intr_test_mv = `gmv(ral.intr_test);
        cov.intr_test_cg.sample(WKUP, intr_test_mv[WKUP],
                                wkup_en, intr_status_exp[WKUP]);
        cov.intr_test_cg.sample(WDOG, intr_test_mv[WDOG],
                                wdog_en, intr_status_exp[WDOG]);
      end
    end
    "wkup_ctrl": begin
      bit current_enable;
      `uvm_info(`gfn, "ACCESSING Wkup_ctrl", UVM_DEBUG)
      prescaler = get_reg_fld_mirror_value(ral, csr.get_name(), "prescaler");
      wkup_en   = get_reg_fld_mirror_value(ral, csr.get_name(), "enable");
      csr_rd(.ptr(ral.wkup_ctrl.enable), .value(current_enable), .backdoor(1));
      // Only trigger recalculation if enable was unset before this write
      if (wkup_en && (wkup_en != current_enable) && addr_phase_write)
        recalculate_num_cycles(WKUP);
      if (cfg.en_cov) begin
        bit [1:0] intr_test_mv = `gmv(ral.intr_test);
        cov.intr_test_cg.sample(WKUP, intr_test_mv[WKUP],
                                wkup_en, intr_status_exp[WKUP]);
      end
    end
    "wkup_cause": begin
      if (data_phase_read) begin
        // Check mirrored value matched
        `DV_CHECK_EQ(`gmv(ral.wkup_cause), item.d_data[0],
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end else if (data_phase_write && item.a_mask[0] && item.a_data[0] == 0) begin
        // Predict new wkup_cause after the write
        predict_wkup_cause(.wkup_cause(0), .wait_for_we(1));
      end
    end
    "wkup_count_lo": begin
      wkup_count[31:0] =  csr.get_mirrored_value();
      if (data_phase_write)
        update_wkup_count_lo_timely();
    end
    "wkup_count_hi": begin
      wkup_count[63:32] =  csr.get_mirrored_value();
      if (data_phase_write)
        update_wkup_count_hi_timely();
    end
    "wkup_thold_lo": begin
      wkup_thold[31:0] =  csr.get_mirrored_value();
      `uvm_info(`gfn, $sformatf("Written wkup_thold[31:0]=0x%0x",wkup_thold[31:0]), UVM_DEBUG)
      if (data_phase_write)
        update_wkup_thold_lo_timely();
    end
    "wkup_thold_hi": begin
      wkup_thold[63:32] =  csr.get_mirrored_value();
      `uvm_info(`gfn, $sformatf("Written wkup_thold[63:22]=0x%0x",wkup_thold[63:22]), UVM_DEBUG)
      if (data_phase_write)
        update_wkup_thold_hi_timely();
    end
    "wdog_ctrl": begin
      bit current_enable;
      `uvm_info(`gfn, "Accessing Wdog_ctrl", UVM_DEBUG)
      wdog_en = get_reg_fld_mirror_value(ral, csr.get_name(), "enable");
      wdog_pause_in_sleep = get_reg_fld_mirror_value(ral, csr.get_name(), "pause_in_sleep");
      csr_rd(.ptr(ral.wdog_ctrl.enable), .value(current_enable), .backdoor(1));
      // Only trigger recalculation if enable was unset before this write
      if (wdog_en && (current_enable != wdog_en) && addr_phase_write)
        recalculate_num_cycles(WDOG);
      if (cfg.en_cov) begin
        bit [1:0] intr_test_mv = `gmv(ral.intr_test);
        cov.intr_test_cg.sample(WDOG, intr_test_mv[WDOG],
                                wdog_en, intr_status_exp[WDOG]);
      end
    end
    "wdog_count": begin
      wdog_count =  csr.get_mirrored_value();
      if (data_phase_write)
        update_wdog_count_timely();
    end
    "wdog_regwen": begin
      wdog_regwen =  csr.get_mirrored_value();
    end
    "wdog_bark_thold": begin
      bark_thold =  csr.get_mirrored_value();
      if (data_phase_write)
        update_wdog_bark_thold_timely();
    end
    "wdog_bite_thold": begin
      bite_thold =  csr.get_mirrored_value();
      if (data_phase_write)
        update_wdog_bite_thold_timely();
    end
    "intr_test": begin
      uint intr_test_val = item.a_data;
      if (addr_phase_write) begin
        // The timed registers predictions need to be independent of each other
        if (intr_test_val[WKUP]) begin
          intr_status_exp[WKUP] = 1'b1;
          `uvm_info(`gfn, "Setting intr_status_exp[WKUP]", UVM_DEBUG)
          update_timed_regs_wkup();
          wkup_intr_predicted_values(intr_status_exp[WKUP]);
          `uvm_info(`gfn, "Updating intr_state[WDOG] due to intr_test[WKUP] write", UVM_DEBUG)
          predict_intr_state(.pred_intr_state(intr_status_exp), .field_only(1), .is_wkup(1));
        end
        if (intr_test_val[WDOG]) begin
          intr_status_exp[WDOG] = 1'b1;
          `uvm_info(`gfn, "Setting intr_status_exp[WDOG]", UVM_DEBUG)
          update_timed_regs_wdog();
          wdog_intr_predicted_values(intr_status_exp[WDOG]);
          `uvm_info(`gfn, "Updating intr_state[WDOG] due to intr_test[WDOG] write", UVM_DEBUG)
          predict_intr_state(.pred_intr_state(intr_status_exp), .field_only(1), .is_wkup(0));
        end

        if (cfg.en_cov) begin
          cov.intr_test_cg.sample(WKUP, intr_test_val[WKUP],
                                  wkup_en, intr_status_exp[WKUP]);
          cov.intr_test_cg.sample(WDOG, intr_test_val[WDOG],
                                  wdog_en, intr_status_exp[WDOG]);
        end
      end // if (addr_phase_write)
    end // case: "intr_test"
    default: begin
      // No other special behaviour for writes
    end
  endcase // case (csr.get_name())

  // Unset flag at the end of the read phase
  if (csr.get_name() == "intr_state" && data_phase_read)
    ongoing_intr_state_read--;

  // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
  if (data_phase_read) begin
    if (do_read_check) begin
      `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                   $sformatf("reg name: %0s", csr.get_full_name()))
    end
    void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
  end
endtask : process_tl_access

task aon_timer_scoreboard::check_interrupt();
  forever begin
    wait (!under_reset);

    fork : isolation_fork
      fork
        wait (under_reset);
        run_wkup_timer();
        run_wdog_bark_timer();
        run_wdog_bite_timer();
      join_any

      // run_wkup_timer and run_wdog_timer never return so if we've got here then we've gone into
      // reset. Kill the two timer processes then go around and wait until we come out of reset
      // again.
      disable fork;
    join
  end
endtask : check_interrupt

task aon_timer_scoreboard::recalculate_num_cycles(timers_e tmr);
  fork
    begin
      if (tmr == WDOG) begin
        wait_for_wdog_enable_matching(.enable(1));
        // Recalculate wdog_count. This is because it's possible WDOG timer  is disabled mid-way
        // through (before wdog_count > thold) and re-enabled at a later point without writing a
        // new count value. TB does a backdoor read to ensure count calculations are up to date.
        csr_rd(.ptr(ral.wdog_count), .value(wdog_count), .backdoor(1));
        wdog_num_update_due = 1;
      end
      else if (tmr == WKUP) begin
        wait_for_wkup_enable_matching(.enable(1));
        // Recalculate wkup_count. This is because it's possible WKUP timer  is disabled mid-way
        // through (before wkup_count > thold) and re-enabled at a later point without writing a
        // new count value. TB does a backdoor read to ensure count calculations are up to date.
        csr_rd(.ptr(ral.wkup_count_lo), .value(wkup_count[31:0]),  .backdoor(1));
        csr_rd(.ptr(ral.wkup_count_hi), .value(wkup_count[63:32]), .backdoor(1));
        wkup_num_update_due = 1;
      end
      else
        `uvm_fatal(`gfn, $sformatf("Incorrect timer type passed (%0s)", tmr.name()))
    end
  join_none
endtask

task aon_timer_scoreboard::compute_num_clks();
  fork
    begin : WKUP_thread
      bit enable;
      forever begin
        @(wkup_num_update_due);
        wait(!under_reset);
        if (wkup_num_update_due) begin
          wait_for_wkup_enable_matching(.enable(1));

          if (wkup_count <= wkup_thold) begin
            wkup_num = ((wkup_thold - wkup_count) * (prescaler + 1));
          end
          else begin
            wkup_num = 0;
          end
          `uvm_info(`gfn, $sformatf("Calculated WKUP_NUM: %d (wkup_count: %0d, wkup_thold = %0d",
                                    wkup_num, wkup_count, wkup_thold), UVM_HIGH)
        end
        wkup_num_update_due = 0;

        `uvm_info(`gfn, "Triggering UVM event 'wkup_count_ev'", UVM_DEBUG)
        wkup_count_ev.trigger();
      end // forever begin
    end
    begin : WDOG_thread
      // WDOG:
      forever begin
        @(wdog_num_update_due);
        if (wdog_num_update_due) begin
          // calculate wdog bark/bite
          wait_for_wdog_enable_matching(.enable(1));

          if (wdog_count < bark_thold) begin
            wdog_bark_num = bark_thold - wdog_count;
          end
          else begin
            wdog_bark_num = 0;
          end
          `uvm_info(`gfn, $sformatf("Calculated wdog_bark_num: %d", wdog_bark_num), UVM_HIGH)

          if (wdog_count < bite_thold) begin
            wdog_bite_num = bite_thold - wdog_count;
          end
          else begin
            wdog_bite_num = 0;
          end
          `uvm_info(`gfn, $sformatf("Calculated wdog_bite_num: %d", wdog_bite_num), UVM_HIGH)
        end
        wdog_num_update_due = 0;
        `uvm_info(`gfn, "Triggering UVM event 'wdog_count_ev'", UVM_DEBUG)
        wdog_count_ev.trigger();
      end // forever begin
    end // block: WDOG_thread
  join
endtask : compute_num_clks

task aon_timer_scoreboard::wait_for_sleep();
  // Using the RTL's internal synchronised signal to ensure we make the predictions in
  // sync with the rtl
  bit   synchronised_sleep_mode_i;
  do begin
    synchronised_sleep_mode_i = cfg.hdl_read_bit(.path(".aon_sleep_mode"));
    if ( (wdog_pause_in_sleep & synchronised_sleep_mode_i))
      cfg.aon_clk_rst_vif.wait_clks(1);
  end while ( (wdog_pause_in_sleep & synchronised_sleep_mode_i));
endtask : wait_for_sleep

task aon_timer_scoreboard::collect_wkup_timer_coverage(event sample_coverage);
  forever begin
    @ (sample_coverage);
    if (cfg.en_cov) begin
      bit [63:0] rtl_count;
      //reading RTL value since TB doesn't keep track of count
      csr_rd(.ptr(ral.wkup_count_lo), .value(rtl_count[31:0]), .backdoor(1));
      csr_rd(.ptr(ral.wkup_count_lo), .value(rtl_count[63:32]), .backdoor(1));
      cov.wake_up_timer_thold_hit_cg.sample(intr_status_exp[WKUP], wkup_thold, rtl_count);
    end
  end
endtask : collect_wkup_timer_coverage

task aon_timer_scoreboard::model_and_check_wkup(ref bit predicting_interrupt);
  // trying to count how many cycles we need to count
  uint count          = 0;
  bit local_interrupt = 0;
  bit local_intr_exp = 0;

  wkup_count_ev.wait_ptrigger();
  `uvm_info(`gfn, "Start WKUP timer UVM event 'wkup_count_ev' Received", UVM_DEBUG)

  `uvm_info(`gfn, $sformatf("WKUP: Start the count (count=%0d < wkup_num=%0d)",
                            count, wkup_num), UVM_DEBUG)
  -> sample_wkup_timer_coverage;
  while (count < wkup_num) begin
    cfg.aon_clk_rst_vif.wait_clks(1);
    // reset the cycle counter when we update the cycle count needed
    count = wkup_num_update_due ? 0 : (count + 1);
    `uvm_info(`gfn, $sformatf("WKUP Timer count: %d (wkup_num=%0d)",
                              count, wkup_num), UVM_DEBUG)
    -> sample_wkup_timer_coverage;
  end

  // If prescaler is 0, the wkup_incr signal will be high the moment count >= threshold
  // Otherwise, there will be 'prescaler' clock cycles before we set wkup_incr. And if
  // the timer is disabled before then the interrupt won't fire.
  // predicting_interrupt = 1 blocks the thread from being killed if the counter gets disabled.
  cfg.aon_clk_rst_vif.wait_clks(prescaler+1);
  wait_for_wkup_enable_matching(.enable(1));
  predicting_interrupt = 1;

  `uvm_info(`gfn, $sformatf("WKUP Timer expired check for interrupts"), UVM_HIGH)

  // Using a local interrupt flag in case 'intr_status_exp[WKUP]' changes
  // due to TL-UL accesses
  local_interrupt = 1;
  intr_status_exp[WKUP] = local_interrupt;
  wkup_cause = `gmv(ral.wkup_cause);
  wkup_cause |= intr_status_exp[WKUP];
  `uvm_info(`gfn, $sformatf("Predicting wkup_cause = 0x%0x",wkup_cause), UVM_DEBUG)
  predict_wkup_cause(.wkup_cause(wkup_cause), .wait_for_we(0));
  -> sample_wkup_timer_coverage;

  // WKUP interrupt ('intr_status_exp[WKUP]')  may have been cleared by the time we reach
  // the AON delay, so we overwrite it and revert it to its original value after
  // updating timed regs
  local_interrupt = intr_status_exp[WKUP];
  intr_status_exp[WKUP] = 1;
  wkup_intr_predicted_values(intr_status_exp[WKUP]);
  intr_status_exp[WKUP] = local_interrupt;

  // Synchronising to the pos-edge before counting edges in case the current cycle is already
  // ongoing to avoid updating the mirrored value too early
  @(cfg.clk_rst_vif.cb);
  // The TB predicts intr_state at the right time by calling predict when DE is set and D
  // signal carries the predicted value to ensure predictions are on time to avoid mismatches
  while (!(cfg.hdl_read_bit(".hw2reg.intr_state.wkup_timer_expired.de") == 1 &&
           cfg.hdl_read_bit(".hw2reg.intr_state.wkup_timer_expired.d") == 1)) begin
    cfg.clk_rst_vif.wait_n_clks(1); // extra cycle to update intr_state in time
  end

  local_interrupt       = intr_status_exp[WKUP];
  intr_status_exp[WKUP] = 1;
  local_intr_exp        = intr_status_exp;
  update_timed_regs_wkup();
  // Predict intr_state.wkup field only
  predict_intr_state(.pred_intr_state(local_intr_exp), .field_only(1), .is_wkup(1));
  // Restoring the value for 'intr_status_exp[WKUP]'
  intr_status_exp[WKUP] = local_interrupt;

  // From the moment DE is set until the interrupt makes it way to the outside there's
  //  2 cycles delay
  cfg.clk_rst_vif.wait_clks(2);
  check_aon_domain_interrupt(.timer_type(WKUP));
  // Check wakeup pin
  `DV_CHECK_CASE_EQ(1,
                    cfg.aon_intr_vif.sample_pin(.idx(1)))

  `uvm_info(`gfn, $sformatf("WKUP Timer checks passed."), UVM_HIGH)

endtask : model_and_check_wkup

task aon_timer_scoreboard::run_wkup_timer();
  bit predicting_interrupt;
  forever begin
    wait (cfg.clk_rst_vif.rst_n === 1);
    wait_for_wkup_enable_matching(.enable(1));
    `uvm_info(`gfn, "WKUP ctrl.enable signal is set", UVM_DEBUG)

    predicting_interrupt = 0;
    fork
      wait (under_reset);
      model_and_check_wkup(predicting_interrupt);
      begin
        wait_for_wkup_enable_matching(.enable(0));
        `uvm_info(`gfn, $sformatf("WKUP Timer disabled, quit scoring"), UVM_HIGH)
        // Only delay the killing of the thread if there's an interrupt to be predicted
        // and reset isn't active
        cfg.clk_rst_vif.wait_clks(1);
        wait (predicting_interrupt==0);
      end
    join_any
    disable fork;
  end
endtask : run_wkup_timer

function aon_timer_intr_timed_regs::timed_reg_e aon_timer_scoreboard::timers_e2time_reg_e(timers_e
                                                                                          timer_type
                                                                                          );
  aon_timer_intr_timed_regs::timed_reg_e return_value;

  if (timer_type == WDOG)
    return_value = aon_timer_intr_timed_regs::TimedIntrStateWdogBark;
  else if (timer_type == WKUP)
    return_value = aon_timer_intr_timed_regs::TimedIntrStateWkupExpired;
  else
    `uvm_fatal(`gfn, $sformatf("Wrong timer index passed (%s)",timer_type.name))

  return return_value;
endfunction

function void aon_timer_scoreboard::check_aon_domain_interrupt(timers_e timer_type);
  bit cdc_reg_compared = 0;
  aon_timer_intr_timed_regs::timed_reg_e reg_idx = timers_e2time_reg_e(timer_type);

  for(int i=0; i < timed_regs.timed[reg_idx].fields.size(); i++) begin
    if (timed_regs.timed[reg_idx].fields[i].pred_valid) begin
      `DV_CHECK_CASE_EQ(timed_regs.timed[reg_idx].fields[i].pred_latest.val_new,
                        cfg.intr_vif.sample_pin(.idx(timer_type)))
      cdc_reg_compared = 1;
    end
  end

  if (!cdc_reg_compared) begin
    `uvm_fatal(`gfn, $sformatf({"TB failed to compare sys-clock %s  interrupt pin - ",
                               "likely due to the CDC timed register not having a prediction"},
                               timer_type.name))
  end
  `uvm_info(`gfn, $sformatf("'intr_%0s=0x%0x' comparison matched",
                            timer_type == WKUP ? "wkup_timer_expired_o" : "wdog_timer_bark_o",
                            cfg.intr_vif.sample_pin(.idx(timer_type))), UVM_DEBUG)
endfunction : check_aon_domain_interrupt

function void aon_timer_scoreboard::return_pred_intr_q(timers_e timer_type, ref bit pred_q[$]);
  if (timer_type == WDOG)
    pred_q = predicted_wdog_intr_q;
  else if (timer_type == WKUP)
    pred_q = predicted_wkup_intr_q;
  else
    `uvm_fatal(`gfn, $sformatf("Wrong timer index passed (%s)",timer_type.name))

  if (pred_q.size == 0)
    `uvm_fatal(`gfn, {"'predicted_", timer_type == WKUP ? "wkup" : "wdog", "_intr_q.size = 0'"})
endfunction

function void aon_timer_scoreboard::check_intr_state_bit(timers_e timer_type, bit actual_value);
  bit cdc_reg_compared = 0;
  bit pred_q[$];

  return_pred_intr_q(timer_type, pred_q);
  `uvm_info(`gfn, $sformatf("Comparing 'intr_state.%0s'", timer_type.name), UVM_DEBUG)
  `DV_CHECK_CASE_EQ(pred_q[0], // Comparing against the oldes predicted value
                    actual_value)

  `uvm_info(`gfn, $sformatf("'intr_state.%0s=0x%0x' comparison matched",
                            timer_type.name, actual_value), UVM_DEBUG)
endfunction : check_intr_state_bit

task aon_timer_scoreboard::collect_wdog_bark_timer_coverage(event sample_coverage);
  forever begin
    @ (sample_coverage);
    if (cfg.en_cov) begin
      bit [31:0] rtl_count;
      //reading RTL value since TB doesn't keep track of count
      csr_rd(.ptr(ral.wdog_count), .value(rtl_count), .backdoor(1));
      cov.watchdog_timer_bark_thold_hit_cg.sample(intr_status_exp[WDOG], bark_thold, rtl_count);
    end
  end
endtask : collect_wdog_bark_timer_coverage

task aon_timer_scoreboard::model_and_check_wdog_bark(ref bit predicting_interrupt);
  // trying to count how many cycles we need to count
  uint count = 0;
  bit is_enabled  = 0;
  bit local_interrupt = 0;
  // Used to ensure the correct value is passed to predict intr_state
  bit [1:0] local_intr_exp;
  bit [1:0] backdoor_intr_state;

  wdog_count_ev.wait_ptrigger();
  `uvm_info(`gfn, "Start WDOG - bark timer UVM event 'wdog_count_ev' Triggered", UVM_DEBUG)

  `uvm_info(`gfn, $sformatf("WDOG: Start the count (count=%0d < wdog_num=%0d)",
                            count, wdog_bark_num),UVM_DEBUG)
  -> sample_wdog_bark_timer_coverage;
  // Need to check for sleep input before the loop in case the count >= thold already
  wait_for_sleep();
  while (count < wdog_bark_num) begin
    cfg.aon_clk_rst_vif.wait_clks(1);
    wait_for_sleep();
    // reset the cycle counter when we update the cycle count needed
    count = wdog_num_update_due ? 0 : (count + 1);
    `uvm_info(`gfn, $sformatf("WDOG Bark Timer count: %d (wdog_bark_num=%0d)",
                              count, wdog_bark_num), UVM_HIGH)
    -> sample_wdog_bark_timer_coverage;
  end
  // Wait until negedge to see if enable stays high a whole tick, otherwise
  // the interrupt won't propagate
  cfg.aon_clk_rst_vif.wait_n_clks(1);
  wait_for_wdog_enable_matching(.enable(1));
  // If the enable becomes unset after this time the prediction needs to finish
  predicting_interrupt = 1;

  `uvm_info(`gfn, $sformatf("WDOG Bark Timer expired check for interrupts"), UVM_HIGH)
  `uvm_info(`gfn, "Setting 'intr_status_exp[WDOG]'", UVM_DEBUG)
  intr_status_exp[WDOG] = 1'b1;

  wkup_cause = `gmv(ral.wkup_cause);
  wkup_cause |= intr_status_exp[WDOG];
  predict_wkup_cause(.wkup_cause(wkup_cause), .wait_for_we(0));
  -> sample_wdog_bark_timer_coverage;
  // Propagation delay of one cycle from aon_core to interrupt pins.
  cfg.aon_clk_rst_vif.wait_clks(1);

  // Using flag to predict the interrupt
  local_interrupt = intr_status_exp[WDOG];
  intr_status_exp[WDOG] = 1;
  // If not using an aux variable 'intr_status_exp' may update prior to the call to
  // predict_intr_state and end up predicting wrong value
  local_intr_exp = intr_status_exp;
  wdog_intr_predicted_values(local_intr_exp[WDOG]);
  intr_status_exp[WDOG] = local_interrupt;

  // Synchronising to the pos-edge before counting edges in case the current cycle is already
  // ongoing to avoid updating the mirrored value too early
  @(cfg.clk_rst_vif.cb);
  // The TB predicts intr_state at the right time by calling predict when DE is set and D
  // signal carries the predicted value to ensure predictions are on time to avoid mismatches
  while (!(cfg.hdl_read_bit(".hw2reg.intr_state.wdog_timer_bark.de") == 1 &&
           cfg.hdl_read_bit(".hw2reg.intr_state.wdog_timer_bark.d") == 1)) begin
    cfg.clk_rst_vif.wait_n_clks(1); // extra cycle to update intr_state in time
  end

  // Using flag to predict the interrupt
  local_interrupt = intr_status_exp[WDOG];
  intr_status_exp[WDOG] = 1;
  update_timed_regs_wdog();

  // If not using aux variable 'intr_status_exp' may update prior to the call to
  // predict_intr_state and end up predicting wrong value
  local_intr_exp = intr_status_exp;
  wdog_intr_predicted_values(local_intr_exp[WDOG]);
  // Predicting only the WDOG field
  predict_intr_state(.pred_intr_state(local_intr_exp), .field_only(1), .is_wkup(0));
  intr_status_exp[WDOG] = local_interrupt;

  // From the moment DE is set until the interrupt makes it way to the outside there's
  //  2 cycles delay
  cfg.clk_rst_vif.wait_clks(2);
  // Check `intr_wdog_timer_bark_o`
  check_aon_domain_interrupt(.timer_type(WDOG));

  // It could happen intr_state reg was written betwen the time intr_status_exp[WDOG] was
  // set until the output 'intr_wdog_timer_bark' was compared and set, if that's the case
  // we set the variable to the value it should be
  csr_rd(.ptr(ral.intr_state), .value(backdoor_intr_state), .backdoor(1));

  if (backdoor_intr_state[WDOG] == 1 && intr_status_exp[WDOG]==0) begin
    `uvm_info(`gfn, {"Tweaking 'intr_status_exp[WDOG]=1' due to a write",
                     "since the value was predicted"}, UVM_DEBUG)
    intr_status_exp[WDOG] = 1; // Set again to ensure TB is in sync
  end
  // Reading actual enable to see if the output will be set
  csr_rd(.ptr(ral.wdog_ctrl.enable), .value(is_enabled), .backdoor(1));
  // Check reset_req pins:
  if (is_enabled) begin
    bit predicted_wkup_req = `gmv(ral.wkup_cause);
    // If the write to wkup_cause wasn't absorved in this same cycle, we compare against the
    // prediction
    if (last_wkup_cause_write_aon_clk_cycle != aon_clk_cycle) begin
      `DV_CHECK_CASE_EQ(predicted_wkup_req, cfg.aon_intr_vif.sample_pin(.idx(1)))
    end
    else if (!(cfg.aon_intr_vif.sample_pin(.idx(1)) inside {0, predicted_wkup_req})) begin
      // Otherwise, check whether the write to wkup_cause(0x0) unset the interrupt or
      // whether it matches the predicted value
      `uvm_fatal(`gfn, $sformatf("aon_wkup_req_o comparison failed (not matching 0/%0d)",
                                 predicted_wkup_req))
    end
  end // if (is_enabled)
  else begin
    // If disabled, wkup_output will be 0/1 depending on the value the flop ended up latching.
    // Hence we don't compare
  end
  `uvm_info(`gfn,$sformatf("WDOG INTR Bark: %d", intr_status_exp[WDOG]), UVM_HIGH)
  predicting_interrupt = 0;

endtask : model_and_check_wdog_bark

task aon_timer_scoreboard::run_wdog_bark_timer();
  // Used as a flag when enable=0 at the same time the interrupt propagates
  bit predicting_interrupt;
  forever begin
    wait(cfg.under_reset == 0);
    wait_for_wdog_enable_matching(.enable(1));
    `uvm_info(`gfn, "wdog_ctrol.WDOG_EN = 1, allow watchdog to count", UVM_DEBUG)
    fork
      // Reset kills the thread inmediately
      wait (under_reset);
      model_and_check_wdog_bark(predicting_interrupt);
      begin
        wait_for_wdog_enable_matching(.enable(0));
        `uvm_info(`gfn, $sformatf("%m - WDOG Timer disabled, quit scoring"), UVM_HIGH)
        // Waiting a sys clock to see if the interrupt will propagate after the module
        // just got disabled
        cfg.clk_rst_vif.wait_clks(1);
        wait (predicting_interrupt == 0);
        wdog_en = 0;
      end
    join_any
    disable fork;
  end
endtask : run_wdog_bark_timer

task aon_timer_scoreboard::wait_for_wdog_enable_matching(bit enable);
  bit local_enable;
  do begin
    csr_rd(.ptr(ral.wdog_ctrl.enable), .value(local_enable), .backdoor(1));
    `uvm_info(`gfn, $sformatf("[backdoor read] : WDOG_CTRL.enable = 0x%0x - matching against = %0d",
                              local_enable, enable), UVM_DEBUG)
    if (local_enable != enable)
      cfg.aon_clk_rst_vif.wait_clks(1);
  end
  while(local_enable != enable);
endtask : wait_for_wdog_enable_matching

task aon_timer_scoreboard::wait_for_wkup_enable_matching(bit enable);
  bit local_enable;
  do begin
    csr_rd(.ptr(ral.wkup_ctrl.enable), .value(local_enable), .backdoor(1));
    `uvm_info(`gfn, $sformatf("[backdoor read] : WKUP_CTRL.enable = 0x%0x",local_enable),
              UVM_DEBUG)
    if (local_enable != enable)
      cfg.aon_clk_rst_vif.wait_clks(1);
  end
  while(local_enable != enable);
endtask : wait_for_wkup_enable_matching

task aon_timer_scoreboard::collect_wdog_bite_timer_coverage(event sample_coverage);
  forever begin
    @ (sample_coverage);
    if (cfg.en_cov) begin
      bit [31:0] rtl_count;
      //reading RTL value since TB doesn't keep track of count
      csr_rd(.ptr(ral.wdog_count), .value(rtl_count), .backdoor(1));
      cov.watchdog_timer_bite_thold_hit_cg.sample(wdog_rst_req_exp, bite_thold, rtl_count);
    end
  end
endtask : collect_wdog_bite_timer_coverage

task aon_timer_scoreboard::model_and_check_wdog_bite(ref bit predicting_interrupt);
  // trying to count how many cycles we need to count
  uint count = 0;

  wdog_count_ev.wait_ptrigger();
  `uvm_info(`gfn, "Start WDOG - bite timer UVM event 'wdog_count_ev' Received", UVM_DEBUG)
  -> sample_wdog_bite_timer_coverage;
  // Need to check for sleep input before the loop in case the count >= thold already
  wait_for_sleep();
  while (count < wdog_bite_num) begin
    cfg.aon_clk_rst_vif.wait_clks(1);
    wait_for_sleep();
    // reset the cycle counter when we update the cycle count needed
    // OG:
    count = wdog_num_update_due ? 0 : (count + 1);
    `uvm_info(`gfn, $sformatf("WDOG Bite Timer count: %d, wdog_bite_num: %0d",
                              count, wdog_bite_num), UVM_HIGH)
    -> sample_wdog_bite_timer_coverage;
  end
  `uvm_info(`gfn, $sformatf("WDOG Bite Timer expired check for interrupts"), UVM_HIGH)
  wdog_rst_req_exp = 1'b1;
  -> sample_wdog_bite_timer_coverage;

  // Propagation delay of one cycle from aon_core to interrupt pins.
  cfg.aon_clk_rst_vif.wait_clks(1);
  wait_for_wdog_enable_matching(.enable(1));
  predicting_interrupt = 1;
  // Wait a further 5 clocks for the interrupt to propagate through logic in the clk domain
  // to become visible on the top-level pins.
  cfg.clk_rst_vif.wait_clks(5);
  // Check reset_req pin
  `DV_CHECK_CASE_EQ(wdog_rst_req_exp,
                    cfg.aon_intr_vif.sample_pin(.idx(0)))
  `uvm_info(`gfn,$sformatf("WDOG INTR Bite: %d", wdog_rst_req_exp), UVM_HIGH)
  predicting_interrupt = 0;
endtask

task aon_timer_scoreboard::run_wdog_bite_timer();
  bit predicting_interrupt;
  forever begin
    wait(cfg.under_reset == 0);
    wait_for_wdog_enable_matching(.enable(1));
    `uvm_info(`gfn, "WDOG ctrl.enable signal is set", UVM_DEBUG)
    predicting_interrupt = 0;
    fork
      // Reset kills the thread inmediately
      wait (under_reset);
      model_and_check_wdog_bite(predicting_interrupt);
      begin
        wait_for_wdog_enable_matching(.enable(0));
        `uvm_info(`gfn, $sformatf("%m - WDOG Timer disabled, quit scoring"), UVM_HIGH)
        // Waiting a sys clock to see if the interrupt will propagate after the module
        // just got disabled
        cfg.clk_rst_vif.wait_clks(1);
        wait (predicting_interrupt == 0);
        wdog_en = 0;
      end
    join_any
    disable fork;
  end
endtask : run_wdog_bite_timer

function void aon_timer_scoreboard::reset(string kind = "HARD");
  super.reset(kind);
  // reset local fifos queues and variables
  `uvm_info(`gfn, "Resetting scoreboard", UVM_DEBUG)
  intr_status_exp = 0;
  wkup_cause = 0;

  ongoing_intr_state_read = 0;
  predicted_wkup_intr_q = {};
  predicted_wdog_intr_q = {};
  // the register is initialised to 0x0
  predicted_wdog_intr_q.push_back(0);
  predicted_wkup_intr_q.push_back(0);
endfunction : reset
