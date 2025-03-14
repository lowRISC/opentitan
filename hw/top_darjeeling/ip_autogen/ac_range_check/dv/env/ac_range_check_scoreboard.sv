// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ac_range_check_scoreboard extends cip_base_scoreboard #(
    .CFG_T(ac_range_check_env_cfg),
    .RAL_T(ac_range_check_reg_block),
    .COV_T(ac_range_check_env_cov)
  );
  `uvm_component_utils(ac_range_check_scoreboard)

  // Local variables
  ac_range_check_dut_cfg dut_cfg;
  tl_seq_item latest_filtered_item;
  int matching_cnt;                   // Number of transactions that matched the prediction
  int unfilt_tr_cnt;
  int act_filt_tr_cnt;
  int exp_filt_tr_cnt;

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(tl_seq_item) tl_unfilt_a_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item) tl_unfilt_d_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item) tl_filt_a_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item) tl_filt_d_chan_fifo;

  // Local queues to hold incoming packets pending comparison
  tl_filt_t exp_tl_filt_q[$];

  // Standard SV/UVM methods
  extern function new(string name="", uvm_component parent=null);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);
  extern function void check_phase(uvm_phase phase);
  extern function void report_phase(uvm_phase phase);

  // Class specific methods
  extern task process_tl_unfilt_a_chan_fifo();
  extern task process_tl_unfilt_d_chan_fifo();
  extern task process_tl_filt_a_chan_fifo();
  extern task process_tl_filt_d_chan_fifo();
  extern task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
  extern task compare_tl_a_chan(tl_filt_t act_tl_filt);
  extern function void reset(string kind = "HARD");
  extern function access_decision_e check_access(tl_seq_item item);
endclass : ac_range_check_scoreboard


function ac_range_check_scoreboard::new(string name="", uvm_component parent=null);
  super.new(name, parent);
  dut_cfg = ac_range_check_dut_cfg::type_id::create("dut_cfg");
endfunction : new

function void ac_range_check_scoreboard::build_phase(uvm_phase phase);
  super.build_phase(phase);
  tl_unfilt_a_chan_fifo = new("tl_unfilt_a_chan_fifo", this);
  tl_unfilt_d_chan_fifo = new("tl_unfilt_d_chan_fifo", this);
  tl_filt_a_chan_fifo   = new("tl_filt_a_chan_fifo", this);
  tl_filt_d_chan_fifo   = new("tl_filt_d_chan_fifo", this);
  // TODO: remove once support alert checking
  do_alert_check = 0;
endfunction : build_phase

function void ac_range_check_scoreboard::connect_phase(uvm_phase phase);
  super.connect_phase(phase);
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
            process_tl_unfilt_a_chan_fifo();
            process_tl_unfilt_d_chan_fifo();
            process_tl_filt_a_chan_fifo();
            process_tl_filt_d_chan_fifo();
          join
          wait fork;  // To ensure it will be killed only when the reset will occur
        end
        begin : reset_thread
          wait(cfg.under_reset);
        end
      join_any
      disable fork;   // Terminates all descendants and sub-descendants of isolation_fork
    end join
  end
endtask : run_phase

// Check whether the current TL access is granted.
// Note: if a request matches multiple ranges with conflicting permissions enabled, the priority is
//       given to the first enabled matching range based on the register configuration order (index
//       0 has priority over 1 for example). Thus, directly return when an enabled matching range is
//       granting or denying the access.
// TODO: check if RACL policies control is OK as done below
function access_decision_e ac_range_check_scoreboard::check_access(tl_seq_item item);
  `uvm_info(`gfn, $sformatf("Analyzing unfiltered item #%0d", unfilt_tr_cnt), UVM_MEDIUM)

  // Due to the note above, we should keep this loop starting from index 0
  for (int i=0; i<NUM_RANGES; i++) begin
    // Only consider the enabled ranges, continue when the range is not enabled
    if (!dut_cfg.range_perm[i].enable) begin
      continue;  // Jump to the next index of the for loop
    end else begin
      // Break and try further if the address is not matching this index range
      if (!(item.a_addr >= dut_cfg.range_base[i] && item.a_addr < dut_cfg.range_limit[i])) begin
        `uvm_info(`gfn, $sformatf("Address 0x%0h is not within the configured range for index #%0d",
                  item.a_addr, i), UVM_HIGH)
        continue;  // Jump to the next index of the for loop
      // Range is allowed
      end else begin
        if (!item.is_write()) begin
          // Access is an EXECUTE (a_user contains this information if a_opcode indicates a read)
          if (item.a_user[InstrTypeMsbPos:InstrTypeLsbPos] == MuBi4True) begin
            if (!dut_cfg.range_perm[i].execute_access) begin
              `uvm_info(`gfn, $sformatf({"EXECUTE access to address 0x%0h is DENIED as ",
                "configured in range_perm index #%0d"}, item.a_addr, i), UVM_MEDIUM)
              return AccessDenied;
            end else begin
              // RACL policy READ permission should also be set
              if (!dut_cfg.range_racl_policy[i].read_perm) begin
                `uvm_info(`gfn, $sformatf({"EXECUTE access to address 0x%0h is DENIED as ",
                  "configured in range_racl_policy index #%0d"}, item.a_addr, i), UVM_HIGH)
                continue;  // Jump to the next index of the for loop
              end else begin
                `uvm_info(`gfn, $sformatf({"EXECUTE access to address 0x%0h is GRANTED as ",
                  "configured in registers with index #%0d"}, item.a_addr, i), UVM_MEDIUM)
                return AccessGranted;
              end
            end
          // Access is a READ
          end else begin
            if (!dut_cfg.range_perm[i].read_access) begin
              `uvm_info(`gfn, $sformatf({"READ access to address 0x%0h is DENIED as ",
                "configured in range_perm index #%0d"}, item.a_addr, i), UVM_MEDIUM)
              return AccessDenied;
            end else begin
              // RACL policy READ permission should also be set
              if (!dut_cfg.range_racl_policy[i].read_perm) begin
                `uvm_info(`gfn, $sformatf({"READ access to address 0x%0h is DENIED as ",
                  "configured in range_racl_policy index #%0d"}, item.a_addr, i), UVM_HIGH)
                continue;  // Jump to the next index of the for loop
              end else begin
                `uvm_info(`gfn, $sformatf({"READ access to address 0x%0h is GRANTED as ",
                  "configured in registers with index #%0d"}, item.a_addr, i), UVM_MEDIUM)
                return AccessGranted;
              end
            end
          end
        // Access is a WRITE
        end else begin
          if (!dut_cfg.range_perm[i].write_access) begin
            `uvm_info(`gfn, $sformatf({"WRITE access to address 0x%0h is DENIED as ",
              "configured in range_perm index #%0d"}, item.a_addr, i), UVM_MEDIUM)
            return AccessDenied;
          end else begin
            // RACL policy WRITE permission should also be set
            if (!dut_cfg.range_racl_policy[i].write_perm) begin
              `uvm_info(`gfn, $sformatf({"WRITE access to address 0x%0h is DENIED as ",
                "configured in range_racl_policy index #%0d"}, item.a_addr, i), UVM_HIGH)
              continue;  // Jump to the next index of the for loop
            end else begin
              `uvm_info(`gfn, $sformatf({"WRITE access to address 0x%0h is GRANTED as ",
                "configured in registers with index #%0d"}, item.a_addr, i), UVM_MEDIUM)
              return AccessGranted;
            end
          end
        end
      end
    end
  end
  `uvm_info(`gfn, $sformatf("No matching range found for access #%0d to address 0x%0h",
            unfilt_tr_cnt, item.a_addr), UVM_MEDIUM)
  return AccessDenied;
endfunction : check_access

task ac_range_check_scoreboard::process_tl_unfilt_a_chan_fifo();
  tl_filt_t tl_filt;
  forever begin
    tl_unfilt_a_chan_fifo.get(tl_filt.item);
    unfilt_tr_cnt++;
    `uvm_info(`gfn, $sformatf("Received tl_unfilt_a_chan unfiltered item #%0d:\n%0s",
                              unfilt_tr_cnt, tl_filt.item.sprint()), UVM_HIGH)

    if (check_access(tl_filt.item) == AccessGranted) begin
      exp_filt_tr_cnt++;
      tl_filt.cnt = exp_filt_tr_cnt;
      exp_tl_filt_q.push_back(tl_filt);
      `uvm_info(`gfn, $sformatf({"EXPECTED filtered item #%0d/%0d on tl_unfilt_a_chan has been ",
                "pushed for comparison"}, exp_filt_tr_cnt, unfilt_tr_cnt), UVM_LOW)
    end else begin
      `uvm_info(`gfn, $sformatf("Item #%0d from tl_unfilt_a_chan has been filtered",
                unfilt_tr_cnt), UVM_LOW)
      latest_filtered_item = tl_filt.item;
    end
  end
endtask : process_tl_unfilt_a_chan_fifo

task ac_range_check_scoreboard::process_tl_unfilt_d_chan_fifo();
  tl_seq_item item;
  forever begin
    tl_unfilt_d_chan_fifo.get(item);
    `uvm_info(`gfn, $sformatf("Received tl_unfilt_d_chan unfiltered item:\n%0s",
              item.sprint()), UVM_HIGH)
    // TODO MVy
    // // At this point, the TL transaction should have completed and the response will be in seq.rsp.
    // // The fetch was successful if d_error is false.
    // `DV_CHECK(!seq.rsp.d_error, "Single TL unfiltered transaction failed")
  end
endtask : process_tl_unfilt_d_chan_fifo

task ac_range_check_scoreboard::process_tl_filt_a_chan_fifo();
  tl_filt_t tl_filt;
  forever begin
    tl_filt_a_chan_fifo.get(tl_filt.item);
    act_filt_tr_cnt++;
    tl_filt.cnt = act_filt_tr_cnt;
    `uvm_info(`gfn, $sformatf("Received tl_filt_a_chan ACTUAL filtered item #%0d:\n%0s",
                              act_filt_tr_cnt, tl_filt.item.sprint()), UVM_HIGH)
    `uvm_info(`gfn, $sformatf({"ACTUAL filtered item #%0d on tl_filt_a_chan has been ",
              "pushed for comparison"}, act_filt_tr_cnt), UVM_LOW)

    // Spawn a thread and directly wait for the next item
    fork
      compare_tl_a_chan(tl_filt);
    join_none
  end
endtask : process_tl_filt_a_chan_fifo

task ac_range_check_scoreboard::process_tl_filt_d_chan_fifo();
  tl_seq_item item;
  forever begin
    tl_filt_d_chan_fifo.get(item);
    `uvm_info(`gfn, $sformatf("Received tl_filt_d_chan item:\n%0s", item.sprint()), UVM_HIGH)
  end
endtask : process_tl_filt_d_chan_fifo

task ac_range_check_scoreboard::compare_tl_a_chan(tl_filt_t act_tl_filt);
  tl_filt_t exp_tl_filt;

  // Delay a bit if the espected queue is still empty as tl_unfilt port can be fed shortly after
  // tl_filt for some reason
  if (exp_tl_filt_q.size() == 0) begin
    `DV_WAIT(exp_tl_filt_q.size() > 0,
             $sformatf({"Unable to get any item from exp_tl_filt_q, it has probably been filtered.",
                       " The lastest filtered item was the #%0d: \n%0s"}, unfilt_tr_cnt,
                       latest_filtered_item.sprint()),
             1_000, `gfn, 0)
  end

  exp_tl_filt = exp_tl_filt_q.pop_front();
  `uvm_info(`gfn, $sformatf("EXPECTED tl_filt_a_chan item:\n%0s",
                            exp_tl_filt.item.sprint()), UVM_HIGH)

  // Compare DUT output on TL filtered A channel against the expected data
  if (act_tl_filt.item.compare(exp_tl_filt.item)) begin
    `uvm_info(`gfn, $sformatf("ACTUAL item matched the prediction for filtered item #%0d",
              act_tl_filt.cnt), UVM_LOW)
    matching_cnt++;
  end else begin
    `uvm_info(`gfn, $sformatf("Trying to compare ACTUAL item #%0d vs EXPECTED item #%0d",
              act_tl_filt.cnt, exp_tl_filt.cnt), UVM_LOW)
    `uvm_error(`gfn, $sformatf({"ACTUAL and EXPECTED tl_filt_a_chan items are not matching:",
                "\n\nACTUAL: \n%0s \nEXPECTED: \n%0s"},
                act_tl_filt.item.sprint(), exp_tl_filt.item.sprint()))
  end
endtask : compare_tl_a_chan

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
    end else if (csr.get_type_name() == "ac_range_check_reg_range_perm") begin
      csr_name = "range_perm";
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
    "range_perm": begin
      if (tl_phase == AChanWrite) begin
        dut_cfg.range_perm[csr_idx].log_denied_access =
          mubi4_logic_test_true_strict(`gmv(ral.range_perm[csr_idx].log_denied_access));
        dut_cfg.range_perm[csr_idx].execute_access    =
          mubi4_logic_test_true_strict(`gmv(ral.range_perm[csr_idx].execute_access));
        dut_cfg.range_perm[csr_idx].write_access      =
          mubi4_logic_test_true_strict(`gmv(ral.range_perm[csr_idx].write_access));
        dut_cfg.range_perm[csr_idx].read_access       =
          mubi4_logic_test_true_strict(`gmv(ral.range_perm[csr_idx].read_access));
        dut_cfg.range_perm[csr_idx].enable            =
          mubi4_logic_test_true_strict(`gmv(ral.range_perm[csr_idx].enable));
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
  exp_tl_filt_q.delete();
  matching_cnt    = 0;
  unfilt_tr_cnt   = 0;
  exp_filt_tr_cnt = 0;
  act_filt_tr_cnt = 0;
endfunction : reset

function void ac_range_check_scoreboard::check_phase(uvm_phase phase);
  super.check_phase(phase);

  // This condition seems useless, but the way the environment builds the scoreboard, it doesn't
  // care about this configuration field for some reason. We don't need to check the following
  // things when the ran test is related to the CSR checks in particular.
  if (cfg.en_scb) begin
    if (matching_cnt == 0) begin
      `uvm_error(`gfn, {"No matching transaction found, it can be because all the TL accesses have",
                        " been filtered. Please check your DUT configuration and your sequence."})
    end

    if (exp_tl_filt_q.size() > 0) begin
      `uvm_error(`gfn, {"Queue exp_tl_filt_q is not empty: not all the received TL transactions",
                        " have been compared."})
    end
  end
endfunction : check_phase

function void ac_range_check_scoreboard::report_phase(uvm_phase phase);
  super.report_phase(phase);
  if (cfg.en_scb) begin
    `uvm_info(`gfn, $sformatf("The number of transactions that matched the prediction is %0d",
              matching_cnt), UVM_MEDIUM)
  end
endfunction : report_phase
