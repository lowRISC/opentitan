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
  int matching_cnt = 0;             // Number of transactions that matched the prediction

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(tl_seq_item) tl_unfilt_a_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item) tl_unfilt_d_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item) tl_filt_a_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item) tl_filt_d_chan_fifo;

  // Local queues to hold incoming packets pending comparison
  tl_seq_item act_tl_filt_q[$];
  tl_seq_item exp_tl_filt_q[$];

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
  extern task compare_tl_a_chan();
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
// Note: if ranges are configured in a contradictory way, the priority is given to the first
//       matching range based on the register configuration order (index 0 has priority over 1 for
//       example). Thus, directly return when a matching range is allowing the access.
function access_decision_e ac_range_check_scoreboard::check_access(tl_seq_item item);
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
          if (item.a_user) begin
            if (!dut_cfg.range_perm[i].execute_access) begin
              `uvm_info(`gfn, $sformatf({"EXECUTE access to address 0x%0h is DENIED as ",
                        "configured in range_perm index #%0d"}, item.a_addr, i), UVM_HIGH)
              continue;  // Jump to the next index of the for loop
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
                        "configured in range_perm index #%0d"}, item.a_addr, i), UVM_HIGH)
              continue;  // Jump to the next index of the for loop
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
                      "configured in range index #%0d"}, item.a_addr, i), UVM_HIGH)
            continue;  // Jump to the next index of the for loop
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
  `uvm_info(`gfn, $sformatf("No matching access found for address 0x%0h",item.a_addr), UVM_MEDIUM)
  return AccessDenied;
endfunction : check_access

task ac_range_check_scoreboard::process_tl_unfilt_a_chan_fifo();
  tl_seq_item item;
  forever begin
    tl_unfilt_a_chan_fifo.get(item);
    `uvm_info(`gfn, $sformatf("Received tl_unfilt_a_chan item:\n%0s", item.sprint()), UVM_HIGH)

    if (check_access(item) == AccessGranted) begin
      exp_tl_filt_q.push_back(item);
    end else begin
      `uvm_info(`gfn, "Transaction on tl_unfilt_a_chan has been filtered", UVM_LOW)
    end
  end
endtask : process_tl_unfilt_a_chan_fifo

task ac_range_check_scoreboard::process_tl_unfilt_d_chan_fifo();
  tl_seq_item item;
  forever begin
    tl_unfilt_d_chan_fifo.get(item);
    `uvm_info(`gfn, $sformatf("Received tl_unfilt_d_chan item:\n%0s", item.sprint()), UVM_HIGH)
    // TODO MVy
    // // At this point, the TL transaction should have completed and the response will be in seq.rsp.
    // // The fetch was successful if d_error is false.
    // `DV_CHECK(!seq.rsp.d_error, "Single TL unfiltered transaction failed")
  end
endtask : process_tl_unfilt_d_chan_fifo

task ac_range_check_scoreboard::process_tl_filt_a_chan_fifo();
  tl_seq_item item;
  forever begin
    tl_unfilt_a_chan_fifo.get(item);
    `uvm_info(`gfn, $sformatf("Received tl_unfilt_a_chan item:\n%0s", item.sprint()), UVM_HIGH)

    if (check_access(item) == AccessGranted) begin
      exp_tl_filt_q.push_back(item);
    end else begin
      `uvm_info(`gfn, "Transaction on tl_unfilt_a_chan has been filtered", UVM_LOW)
    end
  end
endtask : process_tl_unfilt_a_chan_fifo

task ac_range_check_scoreboard::process_tl_unfilt_d_chan_fifo();
  tl_seq_item item;
  forever begin
    tl_unfilt_d_chan_fifo.get(item);
    `uvm_info(`gfn, $sformatf("Received tl_unfilt_d_chan item:\n%0s", item.sprint()), UVM_HIGH)
    // TODO MVy
    // // At this point, the TL transaction should have completed and the response will be in seq.rsp.
    // // The fetch was successful if d_error is false.
    // `DV_CHECK(!seq.rsp.d_error, "Single TL unfiltered transaction failed")
  end
endtask : process_tl_unfilt_d_chan_fifo

task ac_range_check_scoreboard::process_tl_filt_a_chan_fifo();
  tl_seq_item item;
  forever begin
    tl_filt_a_chan_fifo.get(item);
    // `uvm_info(`gfn, $sformatf("Received tl_filt_a_chan item:\n%0s", item.sprint()), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("Received tl_filt_a_chan item:\n%0s", item.sprint()), UVM_LOW)
    tl_filt_a_chan_fifo.get(item);
    `uvm_info(`gfn, $sformatf("\nACTUAL tl_filt_a_chan item:\n%0s", item.sprint()), UVM_HIGH)
    act_tl_filt_q.push_back(item);

    // Spawn a thread and directly wait for the next item
    fork
      compare_tl_a_chan();
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

task ac_range_check_scoreboard::compare_tl_a_chan();
  tl_seq_item act_item;
  tl_seq_item exp_item;

  act_item = act_tl_filt_q.pop_front();

  // Delay a bit if the espected queue is still empty as tl_unfilt port can be fed shortly after
  // tl_filt for some reason
  if (exp_tl_filt_q.size() == 0) begin
    `DV_SPINWAIT(wait(exp_tl_filt_q.size() > 0);, , 1_000, )
  end

  exp_item = exp_tl_filt_q.pop_front();
  `uvm_info(`gfn, $sformatf("EXPECTED tl_filt_a_chan item:\n%0s", exp_item.sprint()), UVM_HIGH)

  // Compare DUT output on TL filtered A channel against the expected data
  if (act_item.compare(exp_item)) begin
    `uvm_info(`gfn, "Transaction on tl_filt_a_chan matched the prediction", UVM_LOW)
    matching_cnt++;
  end else begin
    `uvm_error(`gfn, $sformatf({"Actual and expected tl_filt_a_chan items are not matching:",
                "ACTUAL: \n%0s \nEXPECTED: \n%0s"}, act_item.sprint(), exp_item.sprint()))
  end
endtask : compare_tl_a_chan

task ac_range_check_scoreboard::process_tl_access(tl_seq_item item,
                                                  tl_channels_e channel,
                                                  string ral_name);
  uvm_reg        csr;
  string         csr_name;
  int            csr_idx = -1;
  bit            do_read_check = 1'b1;
  bit            write         = item.is_write();
  uvm_reg_addr_t csr_addr      = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);
  tl_phase_e     tl_phase;

  if (!write && channel == AddrChannel) tl_phase = AddrRead;
  if ( write && channel == AddrChannel) tl_phase = AddrWrite;
  if (!write && channel == DataChannel) tl_phase = DataRead;
  if ( write && channel == DataChannel) tl_phase = DataWrite;

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
  if (tl_phase == AddrWrite) begin
    void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
  end

  // Process the csr req:
  //  - for write, update local variable and fifo at address phase
  //  - for read, update predication at address phase and compare at data phase
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
      if (tl_phase == AddrWrite) begin
        dut_cfg.range_base[csr_idx] = `gmv(ral.range_base[csr_idx]);
      end
    end
    "range_limit": begin
      if (tl_phase == AddrWrite) begin
        dut_cfg.range_limit[csr_idx] = `gmv(ral.range_limit[csr_idx]);
      end
    end
    "range_perm": begin
      if (tl_phase == AddrWrite) begin
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
      if (tl_phase == AddrWrite) begin
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
  if (tl_phase == DataRead) begin
    if (do_read_check) begin
      `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                   $sformatf("reg name: %0s", csr.get_full_name()))
    end
    void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
  end
endtask : process_tl_access

function void ac_range_check_scoreboard::reset(string kind = "HARD");
  super.reset(kind);
  // Reset local fifos queues and variables
endfunction : reset

function void ac_range_check_scoreboard::check_phase(uvm_phase phase);
  super.check_phase(phase);

  if (matching_cnt == 0) begin
    `uvm_error(`gfn, {"No matching transaction found, it can be because all TL accesses have been",
                      "filtered. Please check your DUT configuration and your sequence."})
  end

  if (act_tl_filt_q.size() > 0) begin
    `uvm_error(`gfn, {"Queue act_tl_filt_q is not empty: not all the received TL transactions have",
                      " been compared."})
  end

  if (exp_tl_filt_q.size() > 0) begin
    `uvm_error(`gfn, {"Queue exp_tl_filt_q is not empty: not all the received TL transactions have",
                      " been compared."})
  end
endfunction : check_phase

function void ac_range_check_scoreboard::report_phase(uvm_phase phase);
  super.report_phase(phase);
  if (cfg.en_scb) begin
    `uvm_info(`gfn, $sformatf("The number of transactions that matched the prediction is %0d",
              matching_cnt), UVM_MEDIUM)
  end
endfunction : report_phase
