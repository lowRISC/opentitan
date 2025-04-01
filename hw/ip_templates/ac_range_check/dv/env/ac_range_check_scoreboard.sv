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
  cip_tl_seq_item latest_filtered_item;
  int a_chan_matching_cnt;            // Number of matching transactions on A channel
  int d_chan_matching_cnt;            // Number of matching transactions on D channel
  int all_unfilt_a_chan_cnt;          // Total number of received transactions on unfilt A channel
  int exp_unfilt_d_chan_cnt;
  int act_unfilt_d_chan_cnt;
  int act_filt_a_chan_cnt;
  int exp_filt_a_chan_cnt;

  // Local queues
  access_decision_e tr_access_decision_q[$];  // Access decision for each incoming transaction

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(tl_seq_item) tl_unfilt_a_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item) tl_unfilt_d_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item) tl_filt_a_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item) tl_filt_d_chan_fifo;

  // Standard SV/UVM methods
  extern function new(string name="", uvm_component parent=null);
  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);
  extern function void check_phase(uvm_phase phase);
  extern function void report_phase(uvm_phase phase);

  // Class specific methods
  extern task process_tl_unfilt_a_chan_fifo(output tl_filt_t tl_unfilt);
  extern task get_tl_unfilt_d_chan_item(output tl_filt_t tl_unfilt);
  extern task get_tl_filt_a_chan_item(output tl_filt_t tl_filt);
  extern task get_tl_filt_d_chan_item(output tl_filt_t tl_filt);
  extern task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
  extern task manage_tl_fifos();
  extern function void reset(string kind = "HARD");
  extern function void compare_tl_item(string tl_type, tl_filt_t exp, tl_filt_t act);
  extern function access_decision_e check_access(tl_seq_item item);
  extern function cip_tl_seq_item predict_tl_unfilt_d_chan();
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
            manage_tl_fifos();
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
  `uvm_info(`gfn, $sformatf("Analyzing unfiltered item #%0d", all_unfilt_a_chan_cnt), UVM_MEDIUM)

  // Due to the note above, we should keep this loop starting from index 0
  for (int i=0; i<NUM_RANGES; i++) begin
    // Only consider the enabled ranges, continue when the range is not enabled
    if (!dut_cfg.range_attr[i].enable) begin
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
            if (!dut_cfg.range_attr[i].execute_access) begin
              `uvm_info(`gfn, $sformatf({"EXECUTE access to address 0x%0h is DENIED as ",
                "configured in range_attr index #%0d"}, item.a_addr, i), UVM_MEDIUM)
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
            if (!dut_cfg.range_attr[i].read_access) begin
              `uvm_info(`gfn, $sformatf({"READ access to address 0x%0h is DENIED as ",
                "configured in range_attr index #%0d"}, item.a_addr, i), UVM_MEDIUM)
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
          if (!dut_cfg.range_attr[i].write_access) begin
            `uvm_info(`gfn, $sformatf({"WRITE access to address 0x%0h is DENIED as ",
              "configured in range_attr index #%0d"}, item.a_addr, i), UVM_MEDIUM)
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
            all_unfilt_a_chan_cnt, item.a_addr), UVM_MEDIUM)
  return AccessDenied;
endfunction : check_access

function cip_tl_seq_item ac_range_check_scoreboard::predict_tl_unfilt_d_chan();
  cip_tl_seq_item tmp_exp;
  `DV_CHECK_FATAL(latest_filtered_item != null);
  // Predict the exp_tl_unfilt_d_chan item based on the latest_filtered_item item.
  // First copy over all the fields and make some adjustments afterward
  `DV_CHECK_FATAL($cast(tmp_exp, latest_filtered_item.clone()));
  tmp_exp.d_source = latest_filtered_item.a_source;
  // Set TL error flag
  tmp_exp.d_error  = 1;
  // When READ/EXECUTE forward data to zero
  // This check below is required as we can also get erroneous a_user type.
  if (!latest_filtered_item.is_write() &&
      (latest_filtered_item.a_user[InstrTypeMsbPos:InstrTypeLsbPos] == MuBi4True ||
       latest_filtered_item.a_user[InstrTypeMsbPos:InstrTypeLsbPos] == MuBi4False)) begin
      tmp_exp.d_data = 0;
  end
  // Deduce the d_opcode
  if (latest_filtered_item.a_opcode == tlul_pkg::Get) begin
    tmp_exp.d_opcode = tlul_pkg::AccessAckData;
  end else if (latest_filtered_item.a_opcode == tlul_pkg::PutFullData ||
               latest_filtered_item.a_opcode == tlul_pkg::PutPartialData) begin
    tmp_exp.d_opcode = tlul_pkg::AccessAck;
  end
  // Set the d_size to fixed value 32 bits
  tmp_exp.d_size = 2;
  // Compute the d_user field
  tmp_exp.d_user = tmp_exp.compute_d_user();
  return tmp_exp;
endfunction : predict_tl_unfilt_d_chan

// For A channels:
//   - Denied TL transactions are filtered.
//   - Granted TL transactions are forwarded without any change.
// This task predicts the EXPECTED item only when the check_access called from
// process_tl_unfilt_a_chan_fifo returns AccessGranted. Gets the ACTUAL item from its dedicated
// queue. When both items are available, calls the comparison function.
//
// For D channels, when the check_access called from process_tl_unfilt_a_chan_fifo returns:
//   - AccessDenied: the D fields of the item are fed with the info from the latest_filtered_item
//     of the A channel. Additionally, d_error is set to high and d_data is set to 0 in case of a
//     read/execute access.
//   - AccessGranted: the responses provided by the TL device agent (tl_filt_agt) and received
//     on the tl_filt_d_chan_fifo are forwarded without any change, except for d_data when the
//     access is a write. In that case the d_data will be zeroed, but it has been decided to ignore
//     this field in that condition. Note: the reason is mentionned in the PR #1236 ("to avoid
//     unknown assertion failure on prim_fifo_sync").
// This task predicts the EXPECTED item based on what has been assessed by the
// process_tl_unfilt_a_chan_fifo task (by calling the check_access function). Gets the ACTUAL item
//  from its dedicated queue. When both items are available, calls the comparison function.
task ac_range_check_scoreboard::manage_tl_fifos();
  tl_filt_t exp_tl_filt_a_chan;
  tl_filt_t act_tl_filt_a_chan;
  tl_filt_t exp_tl_unfilt_d_chan;
  tl_filt_t act_tl_unfilt_d_chan;

  forever begin
    // Wait until a transaction is available on the tl_unfilt_a_chan port and process it
    process_tl_unfilt_a_chan_fifo(exp_tl_filt_a_chan);

    // When the predicted access is AccessGranted
    if (tr_access_decision_q[all_unfilt_a_chan_cnt-1] == AccessGranted) begin
      // Get item from the tl_filt_a_chan_fifo
      get_tl_filt_a_chan_item(act_tl_filt_a_chan);
      // And do the comparison of the filtered A channel items
      compare_tl_item("tl_filt_a_chan", exp_tl_filt_a_chan, act_tl_filt_a_chan);
      // Get item from the tl_filt_d_chan_fifo (no process is required as it should just go through
      // except for WRITE operations.
      get_tl_filt_d_chan_item(exp_tl_unfilt_d_chan);
      // In presence of a WRITE, the d_data should be zeroed (see PR #1236)
      if (exp_tl_unfilt_d_chan.item.is_write()) begin
        exp_tl_unfilt_d_chan.item.d_data = 0;
      end
    // When the predicted access is AccessDenied
    end else begin
      `uvm_create_obj(tl_seq_item, exp_tl_unfilt_d_chan.item)
      // Predict what the DUT will build based on the latest_filtered_item on A channel
      exp_tl_unfilt_d_chan.item = predict_tl_unfilt_d_chan();
      // Update the expected counter as this should match the actual
      exp_unfilt_d_chan_cnt++;
      exp_tl_unfilt_d_chan.cnt = exp_unfilt_d_chan_cnt;
    end
    // Get item from the tl_unfilt_d_chan_fifo
    get_tl_unfilt_d_chan_item(act_tl_unfilt_d_chan);
    // Finally do the comparison of the unfiltered D channel items
    compare_tl_item("tl_unfilt_d_chan", exp_tl_unfilt_d_chan, act_tl_unfilt_d_chan);
  end
endtask : manage_tl_fifos

// Get an item from the tl_unfilt_a_chan_fifo and call the check_access function to assess whether
// the current transaction should be granted or denied.
task ac_range_check_scoreboard::process_tl_unfilt_a_chan_fifo(output tl_filt_t tl_unfilt);
  tl_unfilt_a_chan_fifo.get(tl_unfilt.item);
  all_unfilt_a_chan_cnt++;
  `uvm_info(`gfn, $sformatf("Received tl_unfilt_a_chan unfiltered item #%0d:\n%0s",
                            all_unfilt_a_chan_cnt, tl_unfilt.item.sprint()), UVM_HIGH)

  // Store whether the access is granted or not, this info could be then retrieved by using the
  // the queue index based on the all_unfilt_a_chan_cnt
  tr_access_decision_q.push_back(check_access(tl_unfilt.item));

  if (tr_access_decision_q[all_unfilt_a_chan_cnt-1] == AccessGranted) begin
    exp_filt_a_chan_cnt++;
    tl_unfilt.cnt = exp_filt_a_chan_cnt;
    `uvm_info(`gfn, $sformatf({"EXPECTED filtered item #%0d/%0d on tl_unfilt_a_chan has been ",
              "forwarded for comparison"}, exp_filt_a_chan_cnt, all_unfilt_a_chan_cnt), UVM_LOW)
  end else begin
    `uvm_info(`gfn, $sformatf("Item #%0d from tl_unfilt_a_chan has been filtered",
              all_unfilt_a_chan_cnt), UVM_LOW)
    `DV_CHECK_FATAL($cast(latest_filtered_item, tl_unfilt.item));
  end
endtask : process_tl_unfilt_a_chan_fifo

task ac_range_check_scoreboard::get_tl_unfilt_d_chan_item(output tl_filt_t tl_unfilt);
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

task ac_range_check_scoreboard::get_tl_filt_a_chan_item(output tl_filt_t tl_filt);
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

// Get the item generated from the TB and sent to the tl_filt D channel.
task ac_range_check_scoreboard::get_tl_filt_d_chan_item(output tl_filt_t tl_filt);
  // Timeout with an error if the FIFO remains empty
  fork
    `DV_WAIT_TIMEOUT(10_000_000, `gfn, "Unable to get any item from tl_filt_d_chan_fifo.", 0)
    tl_filt_d_chan_fifo.get(tl_filt.item);
  join_any
  exp_unfilt_d_chan_cnt++;
  tl_filt.cnt = exp_unfilt_d_chan_cnt;
  `uvm_info(`gfn, $sformatf("Received tl_filt_d_chan item #%0d:\n%0s",
                            exp_unfilt_d_chan_cnt, tl_filt.item.sprint()), UVM_HIGH)
endtask : get_tl_filt_d_chan_item

function void ac_range_check_scoreboard::compare_tl_item(string tl_type,
                                                         tl_filt_t exp, tl_filt_t act);
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
  tl_unfilt_a_chan_fifo.flush();
  tl_unfilt_d_chan_fifo.flush();
  tl_filt_a_chan_fifo.flush();
  tl_filt_d_chan_fifo.flush();
  a_chan_matching_cnt   = 0;
  d_chan_matching_cnt   = 0;
  all_unfilt_a_chan_cnt = 0;
  exp_unfilt_d_chan_cnt = 0;
  act_unfilt_d_chan_cnt = 0;
  exp_filt_a_chan_cnt   = 0;
  act_filt_a_chan_cnt   = 0;
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

    if (d_chan_matching_cnt != all_unfilt_a_chan_cnt) begin
      `uvm_error(`gfn, $sformatf({"The number of matching transactions on the A and on the D ",
                 "channels must be equal: all_unfilt_a_chan_cnt=%0d vs d_chan_matching_cnt=%0d"},
                 all_unfilt_a_chan_cnt, d_chan_matching_cnt))
    end

    if (tl_unfilt_a_chan_fifo.size() > 0) begin
      `uvm_error(`gfn, {"FIFO tl_unfilt_a_chan_fifo is not empty: not all the received TL",
                        " transactions have been compared."})
    end

    if (tl_unfilt_d_chan_fifo.size() > 0) begin
      `uvm_error(`gfn, {"FIFO tl_unfilt_d_chan_fifo is not empty: not all the received TL",
                        " transactions have been compared."})
    end

    if (tl_filt_a_chan_fifo.size() > 0) begin
      `uvm_error(`gfn, {"FIFO tl_filt_a_chan_fifo is not empty: not all the received TL",
                        " transactions have been compared."})
    end

    if (tl_filt_d_chan_fifo.size() > 0) begin
      `uvm_error(`gfn, {"FIFO tl_filt_d_chan_fifo is not empty: not all the received TL",
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
