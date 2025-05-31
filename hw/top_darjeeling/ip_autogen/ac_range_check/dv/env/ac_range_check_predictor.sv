// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ac_range_check_predictor extends uvm_component;
  `uvm_component_utils(ac_range_check_predictor)

  // Local objects
  ac_range_check_dut_cfg dut_cfg;
  ac_range_check_env_cfg env_cfg;

  // TODO: Add check to the coverage object such that it is not null when
  // coverage is enabled
  ac_range_check_env_cov cov;

  cip_tl_seq_item latest_filtered_item;
  ac_range_check_scb_item exp_tl_filt_a_chan;
  ac_range_check_scb_item exp_tl_unfilt_d_chan;

  // Local variables
  int all_unfilt_a_chan_cnt;          // Total number of received transactions on unfilt A channel
  int exp_unfilt_d_chan_cnt;
  int exp_filt_a_chan_cnt;

  // Local queues
  access_decision_e tr_access_decision_q[$];  // Access decision for each incoming transaction

  // TLM FIFOs for incoming transactions from the monitors
  uvm_tlm_analysis_fifo #(tl_seq_item) tl_unfilt_a_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item) tl_filt_d_chan_fifo;

  // Outgoing transactions which will be used in the scoreboard for comparison
  uvm_blocking_put_port #(ac_range_check_scb_item) tl_filt_put;
  uvm_blocking_put_port #(ac_range_check_scb_item) tl_unfilt_put;

  // Standard SV/UVM methods
  extern function new(string name="", uvm_component parent=null);
  extern function void build_phase(uvm_phase phase);
  extern function void check_phase(uvm_phase phase);

  // Class specific methods
  extern task process_tl_unfilt_a_chan_fifo(output ac_range_check_scb_item tl_unfilt);
  extern task get_tl_filt_d_chan_item(output ac_range_check_scb_item tl_filt);
  extern task manage_tl_fifos();
  extern function void reset(string kind = "HARD");
  extern function access_decision_e check_access(tl_seq_item item);
  extern function cip_tl_seq_item predict_tl_unfilt_d_chan();
endclass : ac_range_check_predictor


function ac_range_check_predictor::new(string name="", uvm_component parent=null);
  super.new(name, parent);
  dut_cfg = ac_range_check_dut_cfg::type_id::create("dut_cfg");

endfunction : new

function void ac_range_check_predictor::build_phase (uvm_phase phase);
  super.build_phase(phase);
  // For incoming transactions
  tl_unfilt_a_chan_fifo = new("tl_unfilt_a_chan_fifo", this);
  tl_filt_d_chan_fifo   = new("tl_filt_d_chan_fifo", this);
  // For outgoing transactions
  tl_filt_put           = new("tl_filt_put", this);
  tl_unfilt_put         = new("tl_unfilt_put", this);
endfunction : build_phase

// For A channels:
//   - Denied TL transactions are filtered out.
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
//     access is a write. In that case the d_data will be zeroed (REF_001), but it has been decided
//     to ignore this field in that condition. Note: this is because we cannot stick an "x" into a
//     FIFO, as mentioned in the PR #1236 ("to avoid unknown assertion failure on prim_fifo_sync").
// This task predicts the EXPECTED item based on what has been assessed by the
// process_tl_unfilt_a_chan_fifo task (by calling the check_access function). Gets the ACTUAL item
// from its dedicated queue. When both items are available, calls the comparison function.
task ac_range_check_predictor::manage_tl_fifos();
  ac_range_check_scb_item exp_tl_filt_a_chan;
  ac_range_check_scb_item exp_tl_unfilt_d_chan;

  exp_tl_filt_a_chan   = ac_range_check_scb_item::type_id::create("exp_tl_filt_a_chan");
  exp_tl_unfilt_d_chan = ac_range_check_scb_item::type_id::create("exp_tl_unfilt_d_chan");

  forever begin
    // Wait until a transaction is available on the tl_unfilt_a_chan port and process it
    process_tl_unfilt_a_chan_fifo(exp_tl_filt_a_chan);

    // When the predicted access is AccessGranted
    if (tr_access_decision_q[all_unfilt_a_chan_cnt-1] == AccessGranted) begin
      // Send the expected item to the scoreboard for checking
      tl_filt_put.put(exp_tl_filt_a_chan);
      // Get item from the tl_filt_d_chan_fifo (no process is required as it should just go through
      // except for WRITE operations.
      get_tl_filt_d_chan_item(exp_tl_unfilt_d_chan);
      // In presence of a WRITE, see comment REF_001
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
    // Send the expected item to the scoreboard for checking
    tl_unfilt_put.put(exp_tl_unfilt_d_chan);
  end
endtask : manage_tl_fifos

// Get an item from the tl_unfilt_a_chan_fifo and call the check_access function to assess whether
// the current transaction should be granted or denied.
task ac_range_check_predictor::process_tl_unfilt_a_chan_fifo(
  output ac_range_check_scb_item tl_unfilt);
  tl_unfilt = ac_range_check_scb_item::type_id::create("tl_unfilt");
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

// Get the item generated from the TB and sent to the tl_filt D channel.
task ac_range_check_predictor::get_tl_filt_d_chan_item(output ac_range_check_scb_item tl_filt);
  tl_filt = ac_range_check_scb_item::type_id::create("tl_filt");
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

// Check whether the current TL access is granted.
// Note: if a request matches multiple ranges with conflicting permissions enabled, the priority is
//       given to the first enabled matching range based on the register configuration order (index
//       0 has priority over 1 for example). Thus, directly return when an enabled matching range is
//       granting or denying the access.
// TODO: check if RACL policies control is OK as done below
function access_decision_e ac_range_check_predictor::check_access(tl_seq_item item);
  bit        attr_ok;
  bit        racl_ok;
  int        racl_role;
  bit [15:0] racl_perm;

  tlul_pkg::tl_a_user_t a_user;

  ac_range_check_env_pkg::access_type_e access_type; // Type of transaction access (R/W/X)

  `uvm_info(`gfn, $sformatf("Analyzing unfiltered item #%0d", all_unfilt_a_chan_cnt), UVM_MEDIUM)

  // Due to the note above, we should keep this loop starting from index 0
  for (int i = 0; i < NUM_RANGES; i++) begin
    // Start building coverage model right from the begining
    if (env_cfg.en_cov) begin
      cov.sample_range_cg(.idx(i), .range_en(dut_cfg.range_attr[i].enable));
    end

    // Skip disabled ranges
    if (!dut_cfg.range_attr[i].enable) begin
      continue;
    end

    // At this point the range is enabled. We now check if the transaction
    // address in within the address range specified. If the address is not
    // in the range, move forward to the next range index
    if (item.a_addr < dut_cfg.range_base[i] || item.a_addr >= dut_cfg.range_limit[i]) begin
      `uvm_info(`gfn, $sformatf("Address 0x%0h not in range #%0d", item.a_addr, i), UVM_HIGH)
      if (env_cfg.en_cov) begin
        cov.sample_addr_match_cg(.idx(i), .addr_hit(0));
      end
      continue;
    end

    if (env_cfg.en_cov) begin
      cov.sample_addr_match_cg(.idx(i), .addr_hit(1));
    end

    // At this point we know the address of the transaction address is within
    // the values specified by the range index. Now check what kind of
    // transaction we are observing and fetch the necessary permissions for
    // the access type
    if (item.is_write()) begin
      attr_ok   = dut_cfg.range_attr[i].write_access;
      racl_perm = dut_cfg.range_racl_policy[i].write_perm;
      access_type = ac_range_check_env_pkg::Write;
    end else if (item.a_user[InstrTypeMsbPos:InstrTypeLsbPos] == MuBi4True) begin
      attr_ok   = dut_cfg.range_attr[i].execute_access;
      racl_perm = dut_cfg.range_racl_policy[i].read_perm; // EXECUTE reuses READ in RACL
      access_type = ac_range_check_env_pkg::Execute;
    end else begin
      attr_ok   = dut_cfg.range_attr[i].read_access;
      racl_perm = dut_cfg.range_racl_policy[i].read_perm;
      access_type = ac_range_check_env_pkg::Read;
    end
    `uvm_info(`gfn, $sformatf("RACL Permissions: 0x%0h", racl_perm), UVM_MEDIUM)

    // Extract the role bits that are part of the a_user.rsvd field.
    a_user    = item.a_user;
    racl_role = top_racl_pkg::tlul_extract_racl_role_bits(a_user.rsvd);
    `uvm_info(`gfn, $sformatf("a_user: 0x%0h", a_user), UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("racl_role: %0d", racl_role), UVM_MEDIUM)

    // Extract the RACL configuration bit for racl_role from the extracted
    // shadow index register
    racl_ok = racl_perm[racl_role];
    `uvm_info(`gfn, $sformatf("racl_ok: %0b", racl_ok), UVM_MEDIUM)

    // ---------------------------------------------------------
    // Apply policy
    // ---------------------------------------------------------
    if (!attr_ok) begin
      `uvm_info(`gfn, $sformatf("%s access to 0x%0h is *DENIED* by range_attr[%0d]",
                access_type.name(), item.a_addr, i), UVM_MEDIUM)
      // Sample coverage data
      if (env_cfg.en_cov) begin
        cov.sample_attr_cg(.idx(i), .access_type(access_type),
                           .read_perm   (dut_cfg.range_attr[i].read_access   ),
                           .write_perm  (dut_cfg.range_attr[i].write_access  ),
                           .execute_perm(dut_cfg.range_attr[i].execute_access),
                           .acc_permit(0));
      end

      return AccessDenied;
    end

    if (!racl_ok) begin
      `uvm_info(`gfn, $sformatf("%s access to 0x%0h is *DENIED* by range_racl_policy[%0d]",
                access_type.name(), item.a_addr, i), UVM_MEDIUM)
      if (env_cfg.en_cov) cov.sample_racl_cg(.idx(i), .access_type(access_type),
                                             .role(racl_role), .racl_check(0));
      return AccessDenied;
    end

    // At this point all checks have passed including RACL. So transaction is GRANTED access
    if (env_cfg.en_cov) begin
      cov.sample_attr_cg(.idx(i), .access_type(access_type),
                           .read_perm   (dut_cfg.range_attr[i].read_access   ),
                           .write_perm  (dut_cfg.range_attr[i].write_access  ),
                           .execute_perm(dut_cfg.range_attr[i].execute_access),
                           .acc_permit(1));
      cov.sample_racl_cg(.idx(i), .access_type(access_type), .role(racl_role), .racl_check(1));
    end

    `uvm_info(`gfn, $sformatf("%s access to 0x%0h is *GRANTED* by range[%0d]",
              access_type.name(), item.a_addr, i), UVM_MEDIUM)
    return AccessGranted;
  end // end for i<NUM_RANGES

  // If we have reached this point. The transaction address is out of range on
  // all indexes and hence access is denied
  `uvm_info(`gfn, $sformatf("No matching range found for access #%0d to address 0x%0h",
            all_unfilt_a_chan_cnt, item.a_addr), UVM_MEDIUM)

  if (env_cfg.en_cov) begin
    cov.sample_all_index_miss_cg();
  end
  return AccessDenied;
endfunction : check_access

function cip_tl_seq_item ac_range_check_predictor::predict_tl_unfilt_d_chan();
  cip_tl_seq_item tmp_exp;
  mubi4_t instr_type = mubi4_t'(latest_filtered_item.a_user[InstrTypeMsbPos:InstrTypeLsbPos]);
  `DV_CHECK_FATAL(latest_filtered_item != null);
  // Predict the exp_tl_unfilt_d_chan item based on the latest_filtered_item item.
  // First copy over all the fields and make some adjustments afterward
  `DV_CHECK_FATAL($cast(tmp_exp, latest_filtered_item.clone()));
  tmp_exp.d_source = latest_filtered_item.a_source;
  // Set TL error flag
  tmp_exp.d_error  = 1;
  // When READ/EXECUTE forward data to zero
  // This check below is required as we can also get erroneous a_user type.
  if (!latest_filtered_item.is_write() && instr_type inside {MuBi4True, MuBi4False}) begin
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

function void ac_range_check_predictor::reset(string kind = "HARD");
  tl_unfilt_a_chan_fifo.flush();
  tl_filt_d_chan_fifo.flush();
  all_unfilt_a_chan_cnt = 0;
  exp_unfilt_d_chan_cnt = 0;
  exp_filt_a_chan_cnt   = 0;
  latest_filtered_item  = null;
endfunction : reset

function void ac_range_check_predictor::check_phase(uvm_phase phase);
  super.check_phase(phase);

  if (tl_unfilt_a_chan_fifo.size() > 0) begin
    `uvm_error(`gfn, {"FIFO tl_unfilt_a_chan_fifo is not empty: not all the received TL",
                      " transactions have been compared."})
  end

  if (tl_filt_d_chan_fifo.size() > 0) begin
    `uvm_error(`gfn, {"FIFO tl_filt_d_chan_fifo not empty: not all the received TL",
                      " transactions have been compared."})
  end
endfunction : check_phase
