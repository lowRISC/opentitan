// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ac_range_check_scoreboard extends cip_base_scoreboard #(
    .CFG_T(ac_range_check_env_cfg),
    .RAL_T(ac_range_check_reg_block),
    .COV_T(ac_range_check_env_cov)
  );
  `uvm_component_utils(ac_range_check_scoreboard)

  // Local objects
  ac_range_check_dut_cfg   dut_cfg;
  ac_range_check_predictor predict;

  // Local variables
  int a_chan_matching_cnt;    // Number of matching transactions on A channel
  int d_chan_matching_cnt;    // Number of matching transactions on D channel
  int act_unfilt_d_chan_cnt;
  int act_filt_a_chan_cnt;
  uvm_event exp_tl_filt_ev;
  uvm_event exp_tl_unfilt_ev;

  // Local queues
  ac_range_check_scb_item exp_tl_filt_a_chan_q[$];    // Expected tl_filt items from the predictor
  ac_range_check_scb_item exp_tl_unfilt_d_chan_q[$];  // Expected tl_unfilt items from the predictor

  // TLM FIFOs for incoming transactions from the monitors
  uvm_tlm_analysis_fifo #(tl_seq_item) tl_unfilt_d_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item) tl_filt_a_chan_fifo;

  // Incoming transactions from the predictor
  uvm_blocking_put_imp_filt   #(ac_range_check_scb_item, ac_range_check_scoreboard) tl_filt_imp;
  uvm_blocking_put_imp_unfilt #(ac_range_check_scb_item, ac_range_check_scoreboard) tl_unfilt_imp;

  // Standard SV/UVM methods
  extern function new(string name="", uvm_component parent=null);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);
  extern function void check_phase(uvm_phase phase);
  extern function void report_phase(uvm_phase phase);

  // Class specific methods
  extern task get_tl_unfilt_d_chan_item(output ac_range_check_scb_item tl_unfilt);
  extern task get_tl_filt_a_chan_item(output ac_range_check_scb_item tl_filt);
  extern task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
  extern task tl_filt_wait_and_compare();
  extern task tl_unfilt_wait_and_compare();
  extern task put_filt(ac_range_check_scb_item tl_filt);
  extern task put_unfilt(ac_range_check_scb_item tl_unfilt);
  extern function void reset(string kind = "HARD");
  extern function void compare_tl_item(string tl_type, ac_range_check_scb_item exp,
    ac_range_check_scb_item act);
endclass : ac_range_check_scoreboard


function ac_range_check_scoreboard::new(string name="", uvm_component parent=null);
  super.new(name, parent);
endfunction : new

function void ac_range_check_scoreboard::build_phase(uvm_phase phase);
  super.build_phase(phase);
  dut_cfg               = ac_range_check_dut_cfg::type_id::create("dut_cfg");
  predict               = ac_range_check_predictor::type_id::create("predict", this);
  predict.dut_cfg       = dut_cfg;
  predict.cov           = cov;
  predict.env_cfg       = cfg;
  exp_tl_filt_ev        = new();
  exp_tl_unfilt_ev      = new();
  tl_unfilt_d_chan_fifo = new("tl_unfilt_d_chan_fifo", this);
  tl_filt_a_chan_fifo   = new("tl_filt_a_chan_fifo", this);
  tl_filt_imp           = new("tl_filt_imp", this);
  tl_unfilt_imp         = new("tl_unfilt_imp", this);
  // TODO: remove once support alert checking
  do_alert_check = 0;
endfunction : build_phase

function void ac_range_check_scoreboard::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
  predict.tl_filt_put.connect(this.tl_filt_imp);
  predict.tl_unfilt_put.connect(this.tl_unfilt_imp);
endfunction : connect_phase

task ac_range_check_scoreboard::run_phase(uvm_phase phase);
  super.run_phase(phase);
  wait(cfg.under_reset);
  forever begin
    wait(!cfg.under_reset);
    // This isolation fork is needed to ensure that "disable fork" call won't kill any other
    // processes at the same level from the parent classes
    fork begin : isolation_fork
      fork
        begin : main_thread
          fork
            predict.manage_tl_fifos();
            tl_filt_wait_and_compare();
            tl_unfilt_wait_and_compare();
          join
        end
        begin : reset_thread
          wait(cfg.under_reset);
        end
      join_any
      disable fork;   // Terminates all descendants and sub-descendants of isolation_fork
    end join
  end
endtask : run_phase

task ac_range_check_scoreboard::tl_filt_wait_and_compare();
  ac_range_check_scb_item act_tl_filt_a_chan;
  ac_range_check_scb_item exp_tl_filt_a_chan;

  forever begin
    // Wait until a transaction has been fed from the predictor
    if (exp_tl_filt_a_chan_q.size() == 0) begin
      exp_tl_filt_ev.wait_trigger;
    end
    // Get item from the exp_tl_filt_a_chan_q
    exp_tl_filt_a_chan = exp_tl_filt_a_chan_q.pop_front();
    // Get item from the tl_filt_a_chan_fifo
    get_tl_filt_a_chan_item(act_tl_filt_a_chan);
    // Finally do the comparison of the filtered A channel items
    compare_tl_item("tl_filt_a_chan", exp_tl_filt_a_chan, act_tl_filt_a_chan);
  end
endtask : tl_filt_wait_and_compare

task ac_range_check_scoreboard::tl_unfilt_wait_and_compare();
  ac_range_check_scb_item act_tl_unfilt_d_chan;
  ac_range_check_scb_item exp_tl_unfilt_d_chan;

  forever begin
    // Wait until a transaction has been fed from the predictor
    if (exp_tl_unfilt_d_chan_q.size() == 0) begin
      exp_tl_unfilt_ev.wait_trigger;
    end
    // Get item from the exp_tl_unfilt_d_chan_q
    exp_tl_unfilt_d_chan = exp_tl_unfilt_d_chan_q.pop_front();
    // Get item from the tl_unfilt_d_chan_fifo
    get_tl_unfilt_d_chan_item(act_tl_unfilt_d_chan);
    // Finally do the comparison of the unfiltered D channel items
    compare_tl_item("tl_unfilt_d_chan", exp_tl_unfilt_d_chan, act_tl_unfilt_d_chan);
  end
endtask : tl_unfilt_wait_and_compare

// As required by the macro uvm_blocking_put_imp_decl, we need to implement this task which will be
// called from the predictor when calling the "put" method
task ac_range_check_scoreboard::put_filt(ac_range_check_scb_item tl_filt);
  exp_tl_filt_a_chan_q.push_back(tl_filt);
  exp_tl_filt_ev.trigger;
endtask : put_filt

// As required by the macro uvm_blocking_put_imp_decl, we need to implement this task which will be
// called from the predictor when calling the "put" method
task ac_range_check_scoreboard::put_unfilt(ac_range_check_scb_item tl_unfilt);
  exp_tl_unfilt_d_chan_q.push_back(tl_unfilt);
  exp_tl_unfilt_ev.trigger;
endtask : put_unfilt

task ac_range_check_scoreboard::get_tl_unfilt_d_chan_item(output ac_range_check_scb_item tl_unfilt);
  tl_unfilt = ac_range_check_scb_item::type_id::create("tl_unfilt");
  // Timeout with an error if the FIFO remains empty
  fork
    `DV_WAIT_TIMEOUT(10_000_000, `gfn, "Unable to get any item from tl_unfilt_d_chan_fifo.", 0)
    tl_unfilt_d_chan_fifo.get(tl_unfilt.item);
  join_any
  act_unfilt_d_chan_cnt++;
  tl_unfilt.cnt = act_unfilt_d_chan_cnt;
  `uvm_info(`gfn, $sformatf("Received tl_unfilt_d_chan ACTUAL filtered item #%0d:\n%0s",
            act_unfilt_d_chan_cnt, tl_unfilt.item.sprint()), UVM_HIGH)
  `uvm_info(`gfn, $sformatf({"ACTUAL filtered item #%0d on tl_unfilt_d_chan has been ",
            "forwarded for comparison"}, act_unfilt_d_chan_cnt), UVM_LOW)
endtask : get_tl_unfilt_d_chan_item

task ac_range_check_scoreboard::get_tl_filt_a_chan_item(output ac_range_check_scb_item tl_filt);
  tl_filt = ac_range_check_scb_item::type_id::create("tl_filt");
  // Timeout with an error if the FIFO remains empty
  fork
    `DV_WAIT_TIMEOUT(10_000_000, `gfn, "Unable to get any item from tl_filt_a_chan_fifo.", 0)
    tl_filt_a_chan_fifo.get(tl_filt.item);
  join_any
  act_filt_a_chan_cnt++;
  tl_filt.cnt = act_filt_a_chan_cnt;
  `uvm_info(`gfn, $sformatf("Received tl_filt_a_chan ACTUAL filtered item #%0d:\n%0s",
                            act_filt_a_chan_cnt, tl_filt.item.sprint()), UVM_HIGH)
  `uvm_info(`gfn, $sformatf({"ACTUAL filtered item #%0d on tl_filt_a_chan has been ",
            "forwarded for comparison"}, act_filt_a_chan_cnt), UVM_LOW)
endtask : get_tl_filt_a_chan_item

function void ac_range_check_scoreboard::compare_tl_item(string tl_type,
                                                         ac_range_check_scb_item exp,
                                                         ac_range_check_scb_item act);
  int unsigned matching_cnt_increment = 0;

  `uvm_info(`gfn, $sformatf("EXPECTED %0s item:\n%0s", tl_type, exp.item.sprint()), UVM_HIGH)

  // Compare DUT output against the expected data
  if (act.item.compare(exp.item)) begin
    matching_cnt_increment = 1;
    `uvm_info(`gfn, $sformatf("ACTUAL item matched the prediction for the %0s item #%0d",
              tl_type, act.cnt), UVM_LOW)
  end else begin
    `uvm_info(`gfn, $sformatf("Trying to compare %0s ACTUAL item #%0d vs EXPECTED item #%0d",
              tl_type, act.cnt, exp.cnt), UVM_LOW)
    `uvm_error(`gfn, $sformatf({"ACTUAL and EXPECTED %0s items are not matching:\n\nACTUAL: \n%0s",
                " \nEXPECTED: \n%0s"}, tl_type, act.item.sprint(), exp.item.sprint()))
  end

  if (tl_type == "tl_filt_a_chan") begin
    a_chan_matching_cnt += matching_cnt_increment;
  end else if (tl_type == "tl_unfilt_d_chan") begin
    d_chan_matching_cnt += matching_cnt_increment;
  end else begin
    `uvm_error(`gfn, $sformatf("The specified tl_type (%0s) doesn't exist!", tl_type))
  end
endfunction : compare_tl_item

task ac_range_check_scoreboard::process_tl_access(tl_seq_item item,
                                                  tl_channels_e channel,
                                                  string ral_name);
  uvm_reg        csr;
  string         csr_name;
  int            csr_idx       = -1;
  bit            do_read_check = 1'b1;
  bit            write         = item.is_write();
  uvm_reg_addr_t csr_addr      = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);
  tl_phase_e     tl_phase;

  // Note: AddrChannel and DataChannel don't exist in the TL spec. There is a confusion as TileLink
  //       defines 5 channels called A, B, C, D and E. But for TLUL version, only A and D are used.
  if (!write && channel == AddrChannel) tl_phase = AChanRead;
  if ( write && channel == AddrChannel) tl_phase = AChanWrite;
  if (!write && channel == DataChannel) tl_phase = DChanRead;
  if ( write && channel == DataChannel) tl_phase = DChanWrite;

  // If access was to a valid csr, get the csr handle
  if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
    csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
    `DV_CHECK_NE_FATAL(csr, null)
    // When the CSR is defined as an array, simplify the name to make it generic. This will be
    // useful if the template parameter "num_ranges" is changed.
    if (csr.get_type_name() == "ac_range_check_reg_range_regwen") begin
      csr_name = "range_regwen";
    end else if (csr.get_type_name() == "ac_range_check_reg_range_base") begin
      csr_name = "range_base";
    end else if (csr.get_type_name() == "ac_range_check_reg_range_limit") begin
      csr_name = "range_limit";
    end else if (csr.get_type_name() == "ac_range_check_reg_range_attr") begin
      csr_name = "range_attr";
    end else if (csr.get_type_name() == "ac_range_check_reg_range_racl_policy_shadowed") begin
      csr_name = "range_racl_policy_shadowed";
    end else begin
      csr_name = csr.get_name();
    end
  end else begin
    `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
  end

  csr_idx = get_csr_idx(csr.get_name(), csr_name);

  // If incoming access is a write to a valid csr, then make updates right away
  if (tl_phase == AChanWrite) begin
    void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
  end

  // Process the CSR req:
  //  - for write, update local variable and FIFO at AChanWrite phase
  //  - for read, update predication at AChanRead phase and compare at DChanRead phase
  case (csr_name)
    // Add individual case item for each csr
    "intr_state": begin
      // FIXME TODO MVy
    end
    "intr_enable": begin
      // FIXME TODO MVy
    end
    "intr_test": begin
      // FIXME TODO MVy
    end
    "alert_test": begin
      // FIXME TODO MVy
    end
    "alert_status": begin
      // FIXME TODO MVy
    end
    "log_config": begin
      // FIXME TODO MVy
    end
    "log_status": begin
      // FIXME TODO MVy
    end
    "log_address": begin
      // FIXME TODO MVy
    end
    "range_regwen": begin
      // FIXME TODO MVy
    end
    "range_base": begin
      if (tl_phase == AChanWrite) begin
        dut_cfg.range_base[csr_idx] = `gmv(ral.range_base[csr_idx]);
      end
    end
    "range_limit": begin
      if (tl_phase == AChanWrite) begin
        dut_cfg.range_limit[csr_idx] = `gmv(ral.range_limit[csr_idx]);
      end
    end
    "range_attr": begin
      if (tl_phase == AChanWrite) begin
        dut_cfg.range_attr[csr_idx].log_denied_access =
          mubi4_logic_test_true_strict(`gmv(ral.range_attr[csr_idx].log_denied_access));
        dut_cfg.range_attr[csr_idx].execute_access    =
          mubi4_logic_test_true_strict(`gmv(ral.range_attr[csr_idx].execute_access));
        dut_cfg.range_attr[csr_idx].write_access      =
          mubi4_logic_test_true_strict(`gmv(ral.range_attr[csr_idx].write_access));
        dut_cfg.range_attr[csr_idx].read_access       =
          mubi4_logic_test_true_strict(`gmv(ral.range_attr[csr_idx].read_access));
        dut_cfg.range_attr[csr_idx].enable            =
          mubi4_logic_test_true_strict(`gmv(ral.range_attr[csr_idx].enable));
      end
    end
    "range_racl_policy_shadowed": begin
      if (tl_phase == AChanWrite) begin
        dut_cfg.range_racl_policy[csr_idx].read_perm =
          `gmv(ral.range_racl_policy_shadowed[csr_idx].read_perm);
        dut_cfg.range_racl_policy[csr_idx].write_perm =
          `gmv(ral.range_racl_policy_shadowed[csr_idx].write_perm);
      end
    end
    default: begin
      `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
    end
  endcase

  // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
  if (tl_phase == DChanRead) begin
    if (do_read_check) begin
      `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                   $sformatf("reg name: %0s", csr.get_full_name()))
    end
    void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
  end
endtask : process_tl_access

function void ac_range_check_scoreboard::reset(string kind = "HARD");
  super.reset(kind);
  predict.reset(kind);
  tl_unfilt_d_chan_fifo.flush();
  tl_filt_a_chan_fifo.flush();
  act_unfilt_d_chan_cnt = 0;
  act_filt_a_chan_cnt   = 0;
  a_chan_matching_cnt   = 0;
  d_chan_matching_cnt   = 0;
endfunction : reset

function void ac_range_check_scoreboard::check_phase(uvm_phase phase);
  super.check_phase(phase);

  // This condition seems useless, but the way the environment builds the scoreboard, it doesn't
  // care about this configuration field for some reason. We don't need to check the following
  // things when the ran test is related to the CSR checks in particular.
  if (cfg.en_scb) begin
    if (a_chan_matching_cnt == 0) begin
      `uvm_error(`gfn, {"No matching transaction found, it can be because all the TL accesses have",
                        " been filtered. Please check your DUT configuration and your sequence."})
    end

    if (d_chan_matching_cnt != predict.all_unfilt_a_chan_cnt) begin
      `uvm_error(`gfn, $sformatf({"The number of matching transactions on the A and on the D ",
                 "channels must be equal: all_unfilt_a_chan_cnt=%0d vs d_chan_matching_cnt=%0d"},
                 predict.all_unfilt_a_chan_cnt, d_chan_matching_cnt))
    end

    if (tl_unfilt_d_chan_fifo.size() > 0) begin
      `uvm_error(`gfn, {"FIFO tl_unfilt_d_chan_fifo is not empty: not all the received TL",
                        " transactions have been compared."})
    end

    if (tl_filt_a_chan_fifo.size() > 0) begin
      `uvm_error(`gfn, {"FIFO tl_filt_a_chan_fifo is not empty: not all the received TL",
                        " transactions have been compared."})
    end
  end
endfunction : check_phase

function void ac_range_check_scoreboard::report_phase(uvm_phase phase);
  super.report_phase(phase);
  `uvm_info(`gfn,
            $sformatf("The number of transactions that matched the prediction on a_chan is %0d",
                      a_chan_matching_cnt),
            UVM_MEDIUM)
  `uvm_info(`gfn,
            $sformatf("The number of transactions that matched the prediction on d_chan is %0d",
                      d_chan_matching_cnt),
            UVM_MEDIUM)
endfunction : report_phase
