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

  bit predicted_wkup_intr_q[$];
  bit predicted_wdog_intr_q[$];
  bit ongoing_intr_state_read;

  // TLM agent fifos

  // local queues to hold incoming packets pending comparison


  extern function new (string name="", uvm_component parent=null);
  extern function void build_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);
  extern task monitor_interrupts();
  extern virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
  extern virtual task check_interrupt();
  extern virtual task compute_num_clks();
  extern virtual task wait_for_sleep();
  extern virtual task run_wkup_timer();
  extern virtual task run_wdog_bark_timer();
  extern virtual task run_wdog_bite_timer();
  extern task collect_wkup_timer_coverage(ref event sample_coverage);
  extern task collect_wdog_bark_timer_coverage(ref event sample_coverage);

  extern function void capture_timed_regs(output bfm_timed_regs_t state);
  extern function void capture_timed_regs_wdog(ref bfm_timed_regs_t state);
  extern function void capture_timed_regs_wkup(ref bfm_timed_regs_t state);
  extern function void init_timed_regs();
  extern function void update_timed_regs();
  extern function void update_timed_regs_wdog();
  extern function void update_timed_regs_wkup();

  extern function bit hdl_read_bit(string path);
  extern task wait_for_we_pulse(input string path);

  extern task predict_wkup_cause(bit wkup_cause, bit wait_for_we = 0);
  extern task predict_intr_state(bit [1:0] pred_intr_state);


  extern task update_wdog_count_timely();
  extern task update_wdog_bite_thold_timely();
  extern task update_wdog_bark_thold_timely();

  extern task update_wkup_count_lo_timely();
  extern task update_wkup_count_hi_timely();
  extern task update_wkup_thold_lo_timely();
  extern task update_wkup_thold_hi_timely();

  extern task wkup_intr_predicted_values(bit exp_wkup_intr);
  extern task wdog_intr_predicted_values(bit exp_wdog_intr);
  extern task check_intr_value_propagated(timers_e timer_type);

  extern function void check_aon_domain_interrupt(timers_e timer_type);
  extern function void check_intr_state_bit(timers_e timer_type, bit actual_value);
  extern function void check_wkup_timer_expired();

  extern task wait_for_wdog_enable_matching(bit enable);
  extern task wait_for_wkup_enable_matching(bit enable);

  extern task collect_wdog_bite_timer_coverage(ref event sample_coverage);
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

task aon_timer_scoreboard::run_phase(uvm_phase phase);
  super.run_phase(phase);
  fork
    compute_num_clks();
    check_interrupt();
    monitor_interrupts();
    timed_regs.check_predictions(cfg.under_reset);
  join_none
endtask : run_phase

function void aon_timer_scoreboard::capture_timed_regs(output bfm_timed_regs_t state);
  capture_timed_regs_wdog(state);
  capture_timed_regs_wkup(state);
endfunction : capture_timed_regs


function void aon_timer_scoreboard::capture_timed_regs_wdog(ref bfm_timed_regs_t state);
  state.r[aon_timer_intr_timed_regs::TimedIntrStateWdogBark   ] = intr_status_exp[WDOG];
endfunction : capture_timed_regs_wdog


function void aon_timer_scoreboard::capture_timed_regs_wkup(ref bfm_timed_regs_t state);
  state.r[aon_timer_intr_timed_regs::TimedIntrStateWkupExpired] = intr_status_exp[WKUP];
endfunction : capture_timed_regs_wkup


function void aon_timer_scoreboard::init_timed_regs();
  bfm_timed_regs_t init_regs;
  aon_timer_intr_timed_regs::timed_reg_e r;
  // Capture the initial state of the loosely-timed registers.
  capture_timed_regs(init_regs);

  // Remember the register state.
  prev_timed_regs = init_regs;
  // Create the register descriptions.
  r = r.first();
  forever begin
    timed_reg tr = timed_reg::type_id::create("tr");
    uvm_reg_data_t init_val = 0;
    dv_base_reg_field fields[$];
    // Collect the field descriptions for this register.
    case (r)
      aon_timer_intr_timed_regs::TimedIntrStateWkupExpired:  begin
        ral.intr_state.get_dv_base_reg_fields(fields);
      end
      aon_timer_intr_timed_regs::TimedIntrStateWdogBark:  begin
        ral.intr_state.get_dv_base_reg_fields(fields);
      end
      default: `uvm_fatal(`gfn, "Invalid/unknown register")
    endcase
    // Report the initial value of this register as predicted by the BFM.
    `uvm_info(`gfn, $sformatf("Reg %p : initial value 0x%0x", r, init_regs.r[r]), UVM_MEDIUM)
    // Collect the initial values of the register fields, dropping any that we cannot predict.
    for (int unsigned f = 0; f < fields.size(); f++) begin
      string field_name = fields[f].get_name();
      // Maximum delay (in DUT clock cycles) for a prediction to be met; most delays should take
      // only a few cycles for internal changes to propagate, but some are substantially longer
      // oweing to the immediate operation of the functional model.
      int unsigned max_delay = 16;
      bit          include_field = 1'b1;
      //TODO: is the delay below correct?

      // TODO: do we need to override max delay
      max_delay = 5;
      case (r)
        aon_timer_intr_timed_regs::TimedIntrStateWkupExpired:  begin
          //            max_delay = 5;
        end
        aon_timer_intr_timed_regs::TimedIntrStateWdogBark:  begin
        end
        // All other loosely-timed registers may be fully predicted.
        default: include_field = 1'b1;
      endcase
      if (include_field) begin
        // Extract the initial value of this register field from the modeled register state.
        uvm_reg_data_t mask = (1 << fields[f].get_n_bits()) - 1;
        init_val = (init_regs.r[r] >> fields[f].get_lsb_pos()) & mask;
        tr.add_field(fields[f], init_val, max_delay);
      end
      `uvm_info(`gfn, $sformatf("Register %p field %s : initially 0x%0x included %d", r,
                                field_name, init_val, include_field), UVM_MEDIUM)
    end
    timed_regs.timed[r] = tr;
    if (r == r.last()) break;
    r = r.next();
  end // forever begin
endfunction : init_timed_regs

// Update the expectations for the timed registers; this should be called after any operation on
// the BFM that could affect the state of one or more of the timed registers.
function void aon_timer_scoreboard::update_timed_regs();
  aon_timer_intr_timed_regs::timed_reg_e r = r.first();
  bfm_timed_regs_t new_regs;
  capture_timed_regs(new_regs);
  `uvm_info(`gfn, "After capturing timed regs", UVM_DEBUG)
  forever begin
    // Has there been a change in the bits that we can predict?
    uvm_reg_data_t unpred_mask = timed_regs.timed[r].unpred_mask;
    if ((new_regs.r[r] & ~unpred_mask) != (prev_timed_regs.r[r] & ~unpred_mask)) begin
      timed_regs.predict(r, prev_timed_regs.r[r], new_regs.r[r]);
    end
    if (r == r.last()) break;
    r = r.next();
  end
  // Remember the register state.
  prev_timed_regs = new_regs;
endfunction : update_timed_regs

// neeed separate wdog/wkup update functions in case they are called at the same time
function void aon_timer_scoreboard::update_timed_regs_wdog();
  aon_timer_intr_timed_regs::timed_reg_e r = aon_timer_intr_timed_regs::TimedIntrStateWdogBark;
  bfm_timed_regs_t new_regs;
  uvm_reg_data_t unpred_mask = timed_regs.timed[r].unpred_mask;
  `uvm_info(`gfn, "Updating Timed regs #intr_state - WDOG", UVM_DEBUG)

  capture_timed_regs_wdog(new_regs);
  `uvm_info(`gfn, "After capturing timed regs WDOG", UVM_DEBUG)

  // Has there been a change in the bits that we can predict?
  if ((new_regs.r[r] & ~unpred_mask) != (prev_timed_regs.r[r] & ~unpred_mask)) begin
    timed_regs.predict(r, prev_timed_regs.r[r], new_regs.r[r]);
  end
  // Remember the register state.
  prev_timed_regs = new_regs;
endfunction : update_timed_regs_wdog

function void aon_timer_scoreboard::update_timed_regs_wkup();
  aon_timer_intr_timed_regs::timed_reg_e r = aon_timer_intr_timed_regs::TimedIntrStateWkupExpired;
  bfm_timed_regs_t new_regs;
  uvm_reg_data_t unpred_mask = timed_regs.timed[r].unpred_mask;
  `uvm_info(`gfn, "Updating Timed regs #intr_state - WKUP", UVM_DEBUG)

  capture_timed_regs_wkup(new_regs);
  `uvm_info(`gfn, "After capturing timed regs WKUP", UVM_DEBUG)

  // Has there been a change in the bits that we can predict?
  if ((new_regs.r[r] & ~unpred_mask) != (prev_timed_regs.r[r] & ~unpred_mask)) begin
    timed_regs.predict(r, prev_timed_regs.r[r], new_regs.r[r]);
  end
  // Remember the register state.
  prev_timed_regs = new_regs;
endfunction : update_timed_regs_wkup

task aon_timer_scoreboard::monitor_interrupts();
  forever begin
    @(cfg.aon_intr_vif.pins);
    // Sample interrupt pin coverage for interrupt pins
    if (cfg.en_cov) begin
      foreach (cfg.aon_intr_vif.pins[i]) begin
        cov.intr_pins_cg.sample(i, cfg.aon_intr_vif.sample_pin(.idx(i)));
      end
    end
  end
endtask : monitor_interrupts

// Predicts register wkup_cause whenever the busy flag is 0 and  blocks other parts of the TB to
// predict it's value until an ongoing prediction finishes
// In addition, the prediction can be delayed via setting 'wait_for_we' if the TB wants the
// prediction to proceed after the wkup_cause write crosses the CDC boundary to be in sync with
// the RTL.
// The advice is to wrap this task around a fork...join_none to avoid blocking
task aon_timer_scoreboard::predict_wkup_cause(bit wkup_cause, bit wait_for_we = 0);
  fork
    begin : iso_fork
      fork
        begin : wkup_cause_timely
          wait (ral.wkup_cause.predicting_value == 0);
          if (wait_for_we) begin
            bit we;
            do begin
              we = hdl_read_bit("tb.dut.u_reg.aon_wkup_cause_we");
              if (we === 0)
                cfg.aon_clk_rst_vif.wait_clks(1); // enabled is synchronised to the aon domain
            end while (!we);
            ral.wkup_cause.predicting_value = 1;
            do begin
              we = hdl_read_bit("tb.dut.u_reg.aon_wkup_cause_we");
              if (we === 1)
                cfg.aon_clk_rst_vif.wait_clks(1); // enabled is synchronised to the aon domain
            end while (we);
          end // if (wait_for_we)
          else
            ral.wkup_cause.predicting_value = 1;

          // The predict method may fail if the register has just been accessed:
          // block here to avoid error
          wait (ral.wkup_cause.is_busy()==0);

          if (!ral.wkup_cause.predict(.value(wkup_cause), .kind(UVM_PREDICT_DIRECT)))
            `uvm_fatal(`gfn, $sformatf("%s prediction failed", `gmv(ral.wkup_cause)))
          `uvm_info(`gfn, $sformatf("Updated predicted WKUP-CAUSE to 0x%0x", wkup_cause), UVM_DEBUG)
          ral.wkup_cause.predicting_value = 0;
        end : wkup_cause_timely
        begin : reset_kill
          wait (under_reset);
        end : reset_kill
      join_any
      disable fork;
    end : iso_fork
  join
endtask : predict_wkup_cause


// Convenience function to avoid repeating same boilerplate code
function bit aon_timer_scoreboard::hdl_read_bit(string path);
  bit hdl_bit;
  if (! uvm_hdl_read(path, hdl_bit))
		`uvm_error (`gfn, $sformatf("HDL Read from %s failed", path))
  return hdl_bit;
endfunction : hdl_read_bit


// Does HDL reads to be in sync with when the values kick-in the RTL
// It needs to be called the moment the TL-access occurs, otherwise the thread may hang if the WE
// has risen already
task aon_timer_scoreboard::wait_for_we_pulse(input string path);
  bit we;

  do begin
    we = hdl_read_bit(path);
    if (we === 0)
      cfg.aon_clk_rst_vif.wait_clks(1);
  end while (!we);
  do begin
    we = hdl_read_bit(path);
    if (we === 1)
      cfg.aon_clk_rst_vif.wait_clks(1);
  end while (we);
endtask : wait_for_we_pulse

// Update functions waits for the value to cross CDC boundaries before the TB starts counting
task aon_timer_scoreboard::update_wdog_count_timely();
  fork
    begin: iso_fork
      fork
        begin : hdl_read_wdog_count_we
          wait_for_we_pulse("tb.dut.u_reg.aon_wdog_count_we");
          // Update once the changes have kicked in.
          wdog_num_update_due = 1;
        end : hdl_read_wdog_count_we
        begin : reset_kill
          wait (under_reset);
        end : reset_kill
      join_any
      disable fork;
    end  : iso_fork
  join
endtask : update_wdog_count_timely

task aon_timer_scoreboard::update_wdog_bite_thold_timely();
  fork
    begin: iso_fork
      fork
        begin : hdl_read_wdog_bite_thold_we
          wait_for_we_pulse("tb.dut.u_reg.aon_wdog_bite_thold_gated_we");
          // Update once the changes have kicked in.
          wdog_num_update_due = 1;
        end : hdl_read_wdog_bite_thold_we
        begin : reset_kill
          wait (under_reset);
        end : reset_kill
      join_any
      disable fork;
    end  : iso_fork
  join
endtask : update_wdog_bite_thold_timely

task aon_timer_scoreboard::update_wdog_bark_thold_timely();
  fork
    begin: iso_fork
      fork
        begin : hdl_read_wdog_bark_thold_we
          wait_for_we_pulse("tb.dut.u_reg.aon_wdog_bark_thold_gated_we");
          // Update once the changes have kicked in.
          wdog_num_update_due = 1;
        end : hdl_read_wdog_bark_thold_we
        begin : reset_kill
          wait (under_reset);
        end : reset_kill
      join_any
      disable fork;
    end  : iso_fork
  join
endtask : update_wdog_bark_thold_timely

task aon_timer_scoreboard::update_wkup_count_lo_timely();
  fork
    begin: iso_fork
      fork
        begin : hdl_read_wkup_count_lo_we
          wait_for_we_pulse("tb.dut.u_reg.aon_wkup_count_lo_we");
          // Update once the changes have kicked in.
          wkup_num_update_due = 1;
        end : hdl_read_wkup_count_lo_we
        begin : reset_kill
          wait (under_reset);
        end : reset_kill
      join_any
      disable fork;
    end  : iso_fork
  join
endtask : update_wkup_count_lo_timely
task aon_timer_scoreboard::update_wkup_count_hi_timely();
  fork
    begin: iso_fork
      fork
        begin : hdl_read_wkup_count_hi_we
          wait_for_we_pulse("tb.dut.u_reg.aon_wkup_count_hi_we");
          // Update once the changes have kicked in.
          wkup_num_update_due = 1;
        end : hdl_read_wkup_count_hi_we
        begin : reset_kill
          wait (under_reset);
        end : reset_kill
      join_any
      disable fork;
    end  : iso_fork
  join
endtask : update_wkup_count_hi_timely


task aon_timer_scoreboard::update_wkup_thold_lo_timely();
  fork
    begin: iso_fork
      fork
        begin : hdl_read_wkup_thold_lo_we
          wait_for_we_pulse("tb.dut.u_reg.aon_wkup_thold_lo_we");
          // Update once the changes have kicked in.
          wkup_num_update_due = 1;
        end : hdl_read_wkup_thold_lo_we
        begin : reset_kill
          wait (under_reset);
        end : reset_kill
      join_any
      disable fork;
    end  : iso_fork
  join
endtask : update_wkup_thold_lo_timely

task aon_timer_scoreboard::update_wkup_thold_hi_timely();
  fork
    begin: iso_fork
      fork
        begin : hdl_read_wkup_thold_hi_we
          wait_for_we_pulse("tb.dut.u_reg.aon_wkup_thold_hi_we");
          // Update once the changes have kicked in.
          wkup_num_update_due = 1;
        end : hdl_read_wkup_thold_hi_we
        begin : reset_kill
          wait (under_reset);
        end : reset_kill
      join_any
      disable fork;
    end  : iso_fork
  join
endtask : update_wkup_thold_hi_timely

// Predicts register intr_state whenever the busy flag is 0. It checks the prediction went through
//  and blocks other parts of the TB to predict it's value until an ongoing prediction finishes
// The advice is to wrap this task around a fork...join_none to avoid blocking
task aon_timer_scoreboard::predict_intr_state(bit [1:0] pred_intr_state);
  `uvm_info(`gfn, $sformatf("%m - pred_intr_state = 0x%0x",pred_intr_state), UVM_DEBUG)
  fork
    begin: iso_fork
      fork
        begin : intr_state_timely
          ral.intr_state.predicting_value  = 1;
          wait (ral.intr_state.is_busy()==0);
          if (!ral.intr_state.predict(.value(pred_intr_state), .kind(UVM_PREDICT_DIRECT)))
            `uvm_fatal(`gfn, $sformatf("%s prediction failed", ral.intr_state.get_name()))

          `uvm_info(`gfn, $sformatf("%m - predicted intr_state=0x%0x",pred_intr_state), UVM_DEBUG)
          ral.intr_state.predicting_value  = 0;
        end : intr_state_timely
        begin : reset_kill
          wait (under_reset);
        end : reset_kill
      join_any
      disable fork;
    end : iso_fork
  join
endtask : predict_intr_state

// Pushes predicted values for wkup_interrupt and monitors the value from being update in the RTL
// advice is to wrap the task around fork... join_none
task aon_timer_scoreboard::wkup_intr_predicted_values(bit exp_wkup_intr);
  static int unsigned last_cycle_count = 0;

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
endtask : wkup_intr_predicted_values

// Pushes predicted values for wdog_interrupt and monitors the value from being update in the RTL
// advice is to wrap the task around fork... join_none
task aon_timer_scoreboard::wdog_intr_predicted_values(bit exp_wdog_intr);
  static int unsigned last_cycle_count = 0;

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
  end
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
    else
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    if (cfg.en_cov) begin
      //Sample configuration coverage
      cov.timer_cfg_cg.sample(prescaler, bark_thold, bite_thold,
                              wkup_thold, wdog_regwen, wdog_pause_in_sleep, wkup_cause);
    end
  end

  // Flag to let the model know if a current read is being carried out. Otherwise, the TB may
  // think the actual RTL intr_state value is different to the value being reported back if the
  // change happens right around the same time as the access
  if (csr.get_name() == "intr_state" && !write)
    ongoing_intr_state_read = 1;
  else
    ongoing_intr_state_read = 0;

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
        if (intr_state_val[WKUP]) begin
          intr_status_exp[WKUP] = 1'b0;
          update_prediction = 1;
          fork wkup_intr_predicted_values(intr_status_exp[WKUP]); join_none
        end
        if (intr_state_val[WDOG]) begin
          intr_status_exp[WDOG] = 1'b0;
          update_prediction = 1;
          fork wdog_intr_predicted_values(intr_status_exp[WDOG]); join_none
        end

        if (update_prediction) begin
          uvm_reg_data_t predicted_intr_status;
          predicted_intr_status[WDOG] = intr_status_exp[WDOG];
          predicted_intr_status[WKUP] = intr_status_exp[WKUP];
          `uvm_info(`gfn, $sformatf("Updated intr_status_exp = 0x%0x",intr_status_exp),
                    UVM_DEBUG)
          fork predict_intr_state(predicted_intr_status); join_none

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
    end
    "wkup_ctrl": begin
      `uvm_info(`gfn, "ACCESSING Wkup_ctrl", UVM_DEBUG)
      prescaler = get_reg_fld_mirror_value(ral, csr.get_name(), "prescaler");
      wkup_en   = get_reg_fld_mirror_value(ral, csr.get_name(), "enable");
      if (data_phase_write) wkup_num_update_due = 1;
    end
    "wkup_cause": begin
      if (data_phase_read) begin
        // Check mirrored value matched
        `DV_CHECK_EQ(`gmv(ral.wkup_cause), item.d_data[0],
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end else if (data_phase_write && item.a_mask[0] && item.a_data[0] == 0) begin
        // Predict new wkup_cause after the write
        fork
          predict_wkup_cause(.wkup_cause(0), .wait_for_we(1));
          begin
            wait (ral.wkup_cause.predicting_value == 0);
            wkup_cause = 0;
          end
        join_none
      end
    end
    "wkup_count_lo": begin
      wkup_count[31:0] =  csr.get_mirrored_value();
      if (data_phase_write)
        fork update_wkup_count_lo_timely(); join_none
    end
    "wkup_count_hi": begin
      wkup_count[63:32] =  csr.get_mirrored_value();
      if (data_phase_write)
        fork update_wkup_count_hi_timely(); join_none
    end
    "wkup_thold_lo": begin
      wkup_thold[31:0] =  csr.get_mirrored_value();
      `uvm_info(`gfn, $sformatf("Written wkup_thold[31:0]=0x%0x",wkup_thold[31:0]), UVM_DEBUG)
      if (data_phase_write)
        fork update_wkup_thold_lo_timely(); join_none
    end
    "wkup_thold_hi": begin
      wkup_thold[63:32] =  csr.get_mirrored_value();
      `uvm_info(`gfn, $sformatf("Written wkup_thold[63:22]=0x%0x",wkup_thold[63:22]), UVM_DEBUG)
      if (data_phase_write)
        fork update_wkup_thold_hi_timely(); join_none
    end
    "wdog_ctrl": begin
      `uvm_info(`gfn, "Accessing Wdog_ctrl", UVM_DEBUG)
      wdog_en = get_reg_fld_mirror_value(ral, csr.get_name(), "enable");
      wdog_pause_in_sleep = get_reg_fld_mirror_value(ral, csr.get_name(), "pause_in_sleep");
    end
    "wdog_count": begin
      wdog_count =  csr.get_mirrored_value();
      if (data_phase_write)
        fork update_wdog_count_timely(); join_none
    end
    "wdog_regwen": begin
      wdog_regwen =  csr.get_mirrored_value();
    end
    "wdog_bark_thold": begin
      bark_thold =  csr.get_mirrored_value();
      if (data_phase_write)
        fork update_wdog_bark_thold_timely(); join_none
    end
    "wdog_bite_thold": begin
      bite_thold =  csr.get_mirrored_value();
      if (data_phase_write)
        fork update_wdog_bite_thold_timely(); join_none
    end
    "intr_test": begin
      uint intr_test_val = item.a_data;
      if (addr_phase_write) begin
        // The timed registers predictions need to be independent of each other
        if (intr_test_val[WKUP]) begin
          intr_status_exp[WKUP] = 1'b1;
          `uvm_info(`gfn, "Setting intr_status_exp[WKUP]", UVM_DEBUG)
          update_timed_regs_wkup();
          fork wkup_intr_predicted_values(intr_status_exp[WKUP]); join_none
        end
        if (intr_test_val[WDOG]) begin
          intr_status_exp[WDOG] = 1'b1;
          `uvm_info(`gfn, "Setting intr_status_exp[WDOG]", UVM_DEBUG)
          update_timed_regs_wdog();
          fork wdog_intr_predicted_values(intr_status_exp[WDOG]); join_none
        end

        if (intr_test_val[WDOG] | intr_test_val[WKUP]) begin
          `uvm_info(`gfn, "Updating intr_state due to intr_test write", UVM_DEBUG)
          // The call to intr_state.busy() may block and hence we update when possible
          fork predict_intr_state(intr_status_exp); join_none
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

  // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
  if (data_phase_read) begin
    if (do_read_check) begin
      `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                   $sformatf("reg name: %0s", csr.get_full_name()))
    end
    void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
  end
endtask : process_tl_access

// Task : check_interrupt
// wait for expected # of clocks and check for interrupt state reg and pin
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
    if (! uvm_hdl_read("tb.dut.aon_sleep_mode",synchronised_sleep_mode_i))
			`uvm_error (`gfn, "HDL Read from tb.dut.aon_sleep_mode failed")

    if ( (wdog_pause_in_sleep & synchronised_sleep_mode_i))
      cfg.aon_clk_rst_vif.wait_clks(1);

  end while ( (wdog_pause_in_sleep & synchronised_sleep_mode_i));
endtask : wait_for_sleep

task aon_timer_scoreboard::collect_wkup_timer_coverage(ref event sample_coverage);
  forever begin
    @(sample_coverage.triggered);
    if (cfg.en_cov) begin
      bit [63:0] rtl_count;
      //reading RTL value since TB doesn't keep track of count
      csr_rd(.ptr(ral.wkup_count_lo), .value(rtl_count[31:0]), .backdoor(1));
      csr_rd(.ptr(ral.wkup_count_lo), .value(rtl_count[63:32]), .backdoor(1));
      cov.wake_up_timer_thold_hit_cg.sample(intr_status_exp[WKUP], wkup_thold, rtl_count);
    end
  end
endtask : collect_wkup_timer_coverage

task aon_timer_scoreboard::run_wkup_timer();
    event sample_coverage;
    bit   wkup_enabled;
    forever begin
      wait_for_wkup_enable_matching(.enable(1));
      `uvm_info(`gfn, "WKUP ctrl.enable signal is set", UVM_DEBUG)

      fork
        begin
          collect_wkup_timer_coverage(sample_coverage);
        end
        begin
          // trying to count how many cycles we need to count
          uint count          = 0;
          bit local_interrupt = 0;
          bit local_intr_exp = 0;
          bit is_enabled      = 0;
          bit cdc_reg_compared = 0;
          bit [63:0] count_backdoor_value = 0;
          bit [11:0] preloaded_prescaler_value;

          wkup_count_ev.wait_ptrigger();
          `uvm_info(`gfn, "Start WKUP timer UVM event 'wkup_count_ev' Received", UVM_DEBUG)

          `uvm_info(`gfn, $sformatf("WKUP: Start the count (count=%0d < wkup_num=%0d)",
                                    count, wkup_num), UVM_DEBUG)
          while (count < wkup_num) begin
            cfg.aon_clk_rst_vif.wait_clks(1);
            // reset the cycle counter when we update the cycle count needed
            count = wkup_num_update_due ? 0 : (count + 1);
            `uvm_info(`gfn, $sformatf("WKUP Timer count: %d (wkup_num=%0d)",
                                      count, wkup_num), UVM_HIGH)
            -> sample_coverage;
          end
          wait_for_wkup_enable_matching(.enable(1));
          `uvm_info(`gfn, $sformatf("WKUP Timer expired check for interrupts"), UVM_HIGH)

          // Using a local interrupt flag in case 'intr_status_exp[WKUP]' changes
          // due to TL-UL accesses
          local_interrupt = 1;
          intr_status_exp[WKUP] = local_interrupt;

          wkup_cause = `gmv(ral.wkup_cause);
          wkup_cause |= intr_status_exp[WKUP];
          `uvm_info(`gfn, $sformatf("Predicting wkup_cause = 0x%0x",wkup_cause), UVM_DEBUG)
          fork predict_wkup_cause(.wkup_cause(wkup_cause), .wait_for_we(0)); join_none


          -> sample_coverage;

          // TODO: fix after RTL fix (RTL currently doesn't reset the prescale_count_q when
          // wkup_ctrl is written
          if (! uvm_hdl_read("tb.dut.u_core.prescale_count_q", preloaded_prescaler_value))
			      `uvm_error (`gfn, "HDL Read from tb.dut.u_core.prescale_count_q")

          // Interrupt should happen N+1 clock ticks after count == wkup_num.
          // Oriignal delay:
          //          cfg.aon_clk_rst_vif.wait_clks(prescaler+1);
          if (prescaler==0) begin
            cfg.aon_clk_rst_vif.wait_clks(1);
          end
          // TODO: applies to else_if/ese fix after RTL fix (RTL currently doesn't reset the
          // prescale_count_q when wkup_ctrl is written
          else if ((prescaler + 1) > preloaded_prescaler_value) begin
            cfg.aon_clk_rst_vif.wait_clks((prescaler + 1 - preloaded_prescaler_value));
          end
          else begin
            bit wkup_incr;
            bit [63:0] wkup_count, wkup_thold;
            // Note: This is a bug/feature in the RTL. If the RTL was counting with
            // wkup_ctrl.enable=1, prescaler = X, and by the time SW sends a wup_ctrl.enable=0
            // the internal prescaler counter `prescale_count_q` has a value of Y, if once we enable
            // the wkup_ctrl.enable=1, the value written to wkup_ctrl.prescaler is lower than the
            // value already in `prescaler_count_q`, the prescaler will have to overflow before the
            // new prescaler value becomes effective

            // RTL's `prescale_count_q` may have a "pre-counted" value in it, and unless
            // there's a reset, the interrupt won't propagate to the output until:
            // prescale_count_q == reg2hw_i.wkup_ctrl.prescaler.q (In other words until
            // wkup_incr is true

            // Read threshold, and count and see if we've incremented
            do begin
              csr_rd(.ptr(ral.wkup_count_lo), .value(wkup_count[31:0]), .backdoor(1));
              csr_rd(.ptr(ral.wkup_count_hi), .value(wkup_count[63:32]), .backdoor(1));

              csr_rd(.ptr(ral.wkup_thold_lo), .value(wkup_thold[31:0]), .backdoor(1));
              csr_rd(.ptr(ral.wkup_thold_hi), .value(wkup_thold[63:32]), .backdoor(1));

              if (wkup_count < wkup_thold)
                cfg.aon_clk_rst_vif.wait_clks(1);
            end while (wkup_count < wkup_thold);

            do begin
              if (! uvm_hdl_read("tb.dut.u_core.wkup_incr",wkup_incr))
			          `uvm_error (`gfn, "HDL Read from tb.dut.u_core.wkup_incr failed")
              if (!wkup_incr)
                cfg.aon_clk_rst_vif.wait_clks(1);

            end while(!wkup_incr);
            // Extra delay to allow the interrupt to propagate
            cfg.aon_clk_rst_vif.wait_clks(1);
          end // else: !if((prescaler + 1) > preloaded_prescaler_value)

          // WKUP interrupt ('intr_status_exp[WKUP]')  may have been cleared by the time we reach
          // the AON delay, so we overwrite it and revert it to its original value after
          // updating timed regs
          local_interrupt = intr_status_exp[WKUP];
          intr_status_exp[WKUP] = 1;

          // Push the local_interrupt
          fork wkup_intr_predicted_values(intr_status_exp[WKUP]); join_none

          local_intr_exp = intr_status_exp;
          fork predict_intr_state(local_intr_exp); join_none

          update_timed_regs_wkup();
          // Restoring the value for 'intr_status_exp[WKUP]'
          intr_status_exp[WKUP] = local_interrupt;

          // Wait a further 5 clocks for the interrupt to propagate through logic in the clk domain
          // to become visible on the top-level pins.
          cfg.clk_rst_vif.wait_clks(5);
          check_aon_domain_interrupt(.timer_type(WKUP));

          // Check wakeup pin
          `DV_CHECK_CASE_EQ(ral.wkup_cause.predicting_value ?
                            intr_status_exp[WKUP] : `gmv(ral.wkup_cause),
                            cfg.aon_intr_vif.sample_pin(.idx(1)))

          `uvm_info(`gfn, $sformatf("WKUP Timer checks passed."), UVM_HIGH)
        end
        begin
          wait (!wkup_en || !cfg.aon_clk_rst_vif.rst_n);
          wkup_en = 0;
          wait_for_wkup_enable_matching(.enable(0));
          `uvm_info(`gfn, $sformatf("WKUP Timer disabled, quit scoring"), UVM_HIGH)
        end
      join_any
      disable fork;
    end
  endtask : run_wkup_timer

// Check the value of `intr_wdog_timer_bark/wkup_timer_expired_o' matched the one in the
// intr_state register via using the timed registers.
// intr_status_exp[WDOG/] can't be use to compare since its value may have been wiped out by the
// time the comparison is carried out
function void aon_timer_scoreboard::check_aon_domain_interrupt(timers_e timer_type);
  bit cdc_reg_compared = 0;
  aon_timer_intr_timed_regs::timed_reg_e reg_idx;

  if (timer_type == WDOG)
    reg_idx = aon_timer_intr_timed_regs::TimedIntrStateWdogBark;
  else if (timer_type == WKUP)
    reg_idx = aon_timer_intr_timed_regs::TimedIntrStateWkupExpired;
       else
         `uvm_fatal(`gfn, $sformatf("Wrong timer index passed (%s)",timer_type.name))

  for(int i=0; i < timed_regs.timed[reg_idx].fields.size(); i++) begin
    if (timed_regs.timed[reg_idx].fields[i].pred_valid) begin
      `DV_CHECK_CASE_EQ(timed_regs.timed[reg_idx].fields[i].pred_latest.val_new,
                        cfg.intr_vif.sample_pin(.idx(timer_type)))
      cdc_reg_compared = 1;
    end
  end

  if (!cdc_reg_compared) begin
    `uvm_fatal(`gfn, {$sformatf("TB failed to compare sys-clock %s  interrupt pin - ",
                                timer_type.name),
                      "likely due to the CDC timed register not having a prediction"})
  end
  `uvm_info(`gfn, $sformatf("'intr_%0s=0x%0x' comparison matched",
                            timer_type == WKUP ? "wkup_timer_expired_o" : "wdog_timer_bark_o",
                            cfg.intr_vif.sample_pin(.idx(timer_type))), UVM_DEBUG)
endfunction : check_aon_domain_interrupt

function void aon_timer_scoreboard::check_intr_state_bit(timers_e timer_type, bit actual_value);
  bit cdc_reg_compared = 0;
  aon_timer_intr_timed_regs::timed_reg_e reg_idx;
  bit pred_value;
  if (timer_type == WDOG)
    reg_idx = aon_timer_intr_timed_regs::TimedIntrStateWdogBark;
  else if (timer_type == WKUP)
    reg_idx = aon_timer_intr_timed_regs::TimedIntrStateWkupExpired;
       else
         `uvm_fatal(`gfn, $sformatf("Wrong timer index passed (%s)",timer_type.name))


  if (timer_type == WDOG) begin
    if(predicted_wdog_intr_q.size == 0)
      `uvm_fatal(`gfn, "'predicted_wdog_intr_q.size = 0'")
    pred_value = predicted_wdog_intr_q[0];
  end
  else if (timer_type == WKUP) begin
    if(predicted_wkup_intr_q.size == 0)
      `uvm_fatal(`gfn, "'predicted_wkup_intr_q.size = 0'")
    pred_value = predicted_wkup_intr_q[0];
  end
       else
         `uvm_fatal(`gfn, $sformatf("Wrong timer index passed (%s)",timer_type.name))

  `DV_CHECK_CASE_EQ(pred_value,
                    actual_value)

  `uvm_info(`gfn, $sformatf("'intr_state.%0s=0x%0x' comparison matched",
                            timer_type.name, actual_value), UVM_DEBUG)
endfunction : check_intr_state_bit


// Check the value of `intr_wkup_timer_expired' matched the one in the intr_state register via
// using the timed registers.
// intr_status_exp[WKUP] can't be use to compare since its value may have been wiped out by the
// time the comparison is carried out
function void aon_timer_scoreboard::check_wkup_timer_expired();
  bit cdc_reg_compared = 0;
  aon_timer_intr_timed_regs::
    timed_reg_e reg_idx = aon_timer_intr_timed_regs::TimedIntrStateWkupExpired;
  int unsigned iter = timed_regs.timed[reg_idx].fields.size();

  for(int i=0; i < timed_regs.timed[reg_idx].fields.size(); i++) begin
    if (timed_regs.timed[reg_idx].fields[i].pred_valid) begin
      `DV_CHECK_CASE_EQ(timed_regs.timed[reg_idx].fields[i].pred_latest.val_new,
                        cfg.intr_vif.sample_pin(.idx(WKUP)))
      cdc_reg_compared = 1;
    end
  end

  if (!cdc_reg_compared) begin
    `uvm_fatal(`gfn, {"TB failed to compare sys-clock WKUP  interrupt pin - ",
                      "likely due to the CDC timed register not having a prediction"})
  end

  `uvm_info(`gfn, $sformatf("'intr_wkup_timer_expired_o=0x%0x' comparison matched",
                            cfg.intr_vif.sample_pin(.idx(WKUP))), UVM_DEBUG)
endfunction : check_wkup_timer_expired

task aon_timer_scoreboard::collect_wdog_bark_timer_coverage(ref event sample_coverage);
  forever begin
    @(sample_coverage.triggered);
    if (cfg.en_cov) begin
      bit [31:0] rtl_count;
      //reading RTL value since TB doesn't keep track of count
      csr_rd(.ptr(ral.wdog_count), .value(rtl_count), .backdoor(1));
      cov.watchdog_timer_bark_thold_hit_cg.sample(intr_status_exp[WDOG], bark_thold, rtl_count);
    end
  end
endtask : collect_wdog_bark_timer_coverage

task aon_timer_scoreboard::run_wdog_bark_timer();
  event sample_coverage;
  // Used as a flag when enable=0 at the same time the interrupt propagates
  bit   predicting_interrupt;
  forever begin
    wait_for_wdog_enable_matching(.enable(1));
    `uvm_info(`gfn, "wdog_ctrol.WDOG_EN = 1, allow watchdog to count", UVM_DEBUG)
    fork
      begin
        collect_wdog_bark_timer_coverage(sample_coverage);
      end
      begin
        // trying to count how many cycles we need to count
        uint count = 0;
        bit is_enabled  = 0;
        bit local_interrupt = 0;
        bit cdc_reg_compared = 0;
        bit [31:0] count_backdoor_value;
        bit        wkup_cause_updated;
        // Used to ensure the correct value is passed to predict intr_state
        bit [1:0]  local_intr_exp;
        bit [1:0]  backdoor_intr_state;

        wdog_count_ev.wait_ptrigger();
        `uvm_info(`gfn, "Start WDOG - bark timer UVM event 'wdog_count_ev' Triggered", UVM_DEBUG)

        `uvm_info(`gfn, $sformatf("WDOG: Start the count (count=%0d < wdog_num=%0d)",
                                  count, wdog_bark_num),UVM_DEBUG)

        while (count < wdog_bark_num) begin
          wait_for_sleep();
          cfg.aon_clk_rst_vif.wait_clks(1);
          // reset the cycle counter when we update the cycle count needed
          count = wdog_num_update_due ? 0 : (count + 1);
          `uvm_info(`gfn, $sformatf("WDOG Bark Timer count: %d (wdog_bark_num=%0d)",
                                    count, wdog_bark_num), UVM_HIGH)
          -> sample_coverage;
        end

        wait_for_wdog_enable_matching(.enable(1));
        `uvm_info(`gfn, $sformatf("WDOG Bark Timer expired check for interrupts"), UVM_HIGH)
        `uvm_info(`gfn, "Setting 'intr_status_exp[WDOG]'", UVM_DEBUG)
        intr_status_exp[WDOG] = 1'b1;

        wkup_cause = `gmv(ral.wkup_cause);
        wkup_cause |= intr_status_exp[WDOG];


        // Avoid blocking in case "is_busy==1" so the rest of the timely checks don't stall
        fork predict_wkup_cause(.wkup_cause(wkup_cause), .wait_for_we(0)); join_none
        -> sample_coverage;

        // Propagation delay of one cycle from aon_core to interrupt pins.
        cfg.aon_clk_rst_vif.wait_clks(1);
        // If the enable becomes unset at this time the prediction needs to finish
        predicting_interrupt = 1;

        // Using flag to predict the interrupt
        local_interrupt = intr_status_exp[WDOG];
        intr_status_exp[WDOG] = 1;
        // If not using aux variable 'intr_status_exp' may update prior to the call to
        // predict_intr_state and end up predicting wrong value
        local_intr_exp = intr_status_exp;
        fork wdog_intr_predicted_values(local_intr_exp[WDOG]); join_none

        fork predict_intr_state(local_intr_exp); join_none

        update_timed_regs_wdog();
        intr_status_exp[WDOG] = local_interrupt;

        // Wait a further 5 clocks for the interrupt to propagate through logic in the clk domain
        // to become visible on the top-level pins.
        cfg.clk_rst_vif.wait_clks(5);
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
        // Check reset_req pins
        `DV_CHECK_CASE_EQ((ral.wkup_cause.predicting_value==0) ?
                          `gmv(ral.wkup_cause) : wkup_cause, cfg.aon_intr_vif.sample_pin(.idx(1)))
        `uvm_info(`gfn,$sformatf("WDOG INTR Bark: %d", intr_status_exp[WDOG]), UVM_HIGH)
        predicting_interrupt = 0;
      end
      begin
        wait (cfg.aon_clk_rst_vif.rst_n);
        wait_for_wdog_enable_matching(.enable(0));
        `uvm_info(`gfn, $sformatf("WDOG Timer disabled, quit scoring"), UVM_HIGH)
        // Waiting a sys clock to see if the interrupt will propagate after the module
        // just got disabled
        cfg.clk_rst_vif.wait_clks(1);
        wait (predicting_interrupt==0 || !cfg.aon_clk_rst_vif.rst_n);
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
    `uvm_info(`gfn, $sformatf("[backdoor read] : WDOG_CTRL.enable = 0x%0x",local_enable),
              UVM_DEBUG)
    if (local_enable != enable)
      cfg.aon_clk_rst_vif.wait_clks(1);
  end
  while(local_enable != enable);
endtask : wait_for_wdog_enable_matching

task aon_timer_scoreboard::wait_for_wkup_enable_matching(bit enable);
  bit local_enable;
  do begin
    csr_rd(.ptr(ral.wkup_ctrl.enable), .value(local_enable), .backdoor(1));
    `uvm_info(`gfn, $sformatf("[backdoor read] : WDOG_CTRL.enable = 0x%0x",local_enable),
              UVM_DEBUG)
    if (local_enable != enable)
      cfg.aon_clk_rst_vif.wait_clks(1);
  end
  while(local_enable != enable);
endtask : wait_for_wkup_enable_matching

task aon_timer_scoreboard::collect_wdog_bite_timer_coverage(ref event sample_coverage);
  forever begin
    @(sample_coverage.triggered);
    if (cfg.en_cov) begin
      bit [31:0] rtl_count;
      //reading RTL value since TB doesn't keep track of count
      csr_rd(.ptr(ral.wdog_count), .value(rtl_count), .backdoor(1));
      cov.watchdog_timer_bite_thold_hit_cg.sample(wdog_rst_req_exp, bite_thold, rtl_count);
    end
  end
endtask : collect_wdog_bite_timer_coverage

task aon_timer_scoreboard::run_wdog_bite_timer();
  event sample_coverage;
  forever begin
    wait_for_wdog_enable_matching(.enable(1));
    `uvm_info(`gfn, "WDOG ctrl.enable signal is set", UVM_DEBUG)
    fork
      begin
        collect_wdog_bite_timer_coverage(sample_coverage);
      end
      begin
        // trying to count how many cycles we need to count
        uint count = 0;

        wdog_count_ev.wait_ptrigger();
        `uvm_info(`gfn, "Start WDOG - bite timer UVM event 'wdog_count_ev' Received", UVM_DEBUG)
        `uvm_info(`gfn, "Start WDOG - bark Start to count", UVM_DEBUG)
        while (count < wdog_bite_num) begin
          wait_for_sleep();
          cfg.aon_clk_rst_vif.wait_clks(1);
          // reset the cycle counter when we update the cycle count needed
          // OG:
          count = wdog_num_update_due ? 0 : (count + 1);
          `uvm_info(`gfn, $sformatf("WDOG Bite Timer count: %d, wdog_bite_num: %0d",
                                    count, wdog_bite_num), UVM_HIGH)
          -> sample_coverage;
        end
        `uvm_info(`gfn, $sformatf("WDOG Bite Timer expired check for interrupts"), UVM_HIGH)
        wdog_rst_req_exp = 1'b1;
        -> sample_coverage;

        // Propagation delay of one cycle from aon_core to interrupt pins.
        cfg.aon_clk_rst_vif.wait_clks(1);
        // Wait a further 5 clocks for the interrupt to propagate through logic in the clk domain
        // to become visible on the top-level pins.
        cfg.clk_rst_vif.wait_clks(5);
        // Check reset_req pin
        `DV_CHECK_CASE_EQ(wdog_rst_req_exp,
                          cfg.aon_intr_vif.sample_pin(.idx(0)))
        `uvm_info(`gfn,$sformatf("WDOG INTR Bite: %d", wdog_rst_req_exp), UVM_HIGH)
      end
      begin
        wait (!wdog_en || !cfg.aon_clk_rst_vif.rst_n);
        wdog_en = 0;

        wait_for_wdog_enable_matching(.enable(0));
        `uvm_info(`gfn, $sformatf("WDOG Timer disabled, quit scoring"), UVM_HIGH)
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
