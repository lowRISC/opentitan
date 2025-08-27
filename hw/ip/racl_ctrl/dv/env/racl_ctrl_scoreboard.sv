// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class racl_ctrl_scoreboard extends cip_base_scoreboard #(.CFG_T(racl_ctrl_env_cfg),
                                                         .RAL_T(racl_ctrl_reg_block),
                                                         .COV_T(racl_ctrl_env_cov));
  `uvm_component_utils(racl_ctrl_scoreboard)

  uvm_analysis_export #(racl_error_log_vec_item) internal_errors_export;
  uvm_analysis_export #(racl_error_log_vec_item) external_errors_export;

  extern function new (string name="", uvm_component parent=null);

  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);
  extern task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);

  extern local task process_tl_a_channel(tl_seq_item item, string ral_name);
  extern local task process_tl_d_channel(tl_seq_item item, string ral_name);

  // A function that looks at cfg.policies_vif and checks that its values match those requested in
  // the policy registers.
  extern local function void check_policies();

  // A task that watches cfg.policies_vif continuously, checking that the values always match the
  // ones requested by the policy registers.
  //
  // This performs a check just after each change to the output. To make sure everything stays in
  // sync, the process_tl_access task does an analogous check after each write to one of those
  // policies.
  extern local task watch_policies();

  // Watch the output of arb_predictor. When an item comes out, update the ERROR_LOG and
  // ERROR_LOG_ADDRESS registers. Also assert the racl_error interrupt.
  extern local task watch_arbitrated_errors();

  // Keep the predicted value of the ERROR_LOG register up to date with error_log_pred, waiting for
  // the register not to be in use.
  extern local task mirror_error_log();

  // Keep the predicted value of the ERROR_LOG_ADDRESS register up to date with
  // error_log_address_pred, waiting for the register not to be in use.
  extern local task mirror_error_log_address();

  // A model that arbitrates between errors that have been detected by the error log agents in the
  // environment and fed through to *_errors_export above. Its output is not connected to any
  // export, but it is consumed by the watch_arbitrated_errors task.
  local racl_ctrl_error_arb_predictor arb_predictor;

  // A prediction of the current value of the ERROR_LOG register. This doesn't necessarily use the
  // RAL because hardware changes might happen at the same time as an access to the register, which
  // would cause a race condition.
  local uvm_reg_data_t error_log_pred;

  // An event that gets triggered on a change to error_log_pred, telling mirror_error_log to update
  // the RAL prediction of the ERROR_LOG register.
  local uvm_event error_log_pred_changed_ev;

  // A prediction of the current value of the ERROR_LOG_ADDRESS register and an event for when it
  // gets written (see the documentation for error_log_pred and error_log_pred_changed_ev).
  local uvm_reg_data_t error_log_address_pred;

  // An event that gets triggered on a change to error_log_pred, telling mirror_error_log to update
  // the RAL prediction of the ERROR_LOG register.
  local uvm_event error_log_address_pred_changed_ev;
endclass

function racl_ctrl_scoreboard::new (string name="", uvm_component parent=null);
  super.new(name, parent);
  error_log_pred_changed_ev = new();
  error_log_address_pred_changed_ev = new();
endfunction

function void racl_ctrl_scoreboard::build_phase(uvm_phase phase);
  super.build_phase(phase);
  // TODO: remove once support alert checking
  do_alert_check = 0;

  internal_errors_export = new("internal_errors_export", this);
  external_errors_export = new("external_errors_export", this);

  arb_predictor = racl_ctrl_error_arb_predictor::type_id::create("arb_predictor", this);
  arb_predictor.cfg = cfg;
endfunction

function void racl_ctrl_scoreboard::connect_phase(uvm_phase phase);
  internal_errors_export.connect(arb_predictor.internal_errors_fifo.analysis_export);
  external_errors_export.connect(arb_predictor.external_errors_fifo.analysis_export);
endfunction

task racl_ctrl_scoreboard::run_phase(uvm_phase phase);
  // At the start of time, wait until rst_n is either 0 or 1 (skipping over any period where it's 'x
  // at the start)
  wait(!$isunknown(cfg.clk_rst_vif.rst_n));
  fork
    super.run_phase(phase);
    if (cfg.en_scb)
      fork
        watch_policies();
        watch_arbitrated_errors();
        mirror_error_log();
        mirror_error_log_address();
      join
  join
endtask

task racl_ctrl_scoreboard::process_tl_access(tl_seq_item item,
                                             tl_channels_e channel,
                                             string ral_name);
  case (channel)
    AddrChannel: process_tl_a_channel(item, ral_name);
    DataChannel: process_tl_d_channel(item, ral_name);
    default: `uvm_fatal(`gfn, $sformatf("Invalid channel: %0h", channel))
  endcase
endtask

task racl_ctrl_scoreboard::process_tl_a_channel(tl_seq_item item, string ral_name);
  // We don't do anything with transactions on the A channel at the moment.
endtask

task racl_ctrl_scoreboard::process_tl_d_channel(tl_seq_item item, string ral_name);
  dv_base_reg_block blk = cfg.ral_models[ral_name];

  bit            write    = item.is_write();
  uvm_reg_addr_t csr_addr = blk.get_word_aligned_addr(item.a_addr);
  uvm_reg        csr      = blk.default_map.get_reg_by_offset(csr_addr);

  if (csr == null) `uvm_fatal(`gfn, $sformatf("Could not find CSR for address 0x%0h", csr_addr))

  // If this is the D channel response for a write to one of the policy registers, check that it has
  // been applied to racl_policies_o.
  if (write && cfg.regs.is_policy_reg(csr)) check_policies();

  // If this is the D channel response to a register read, work out the value we think it should
  // have (probably the mirrored value of the register) and check that item.d_data matches.
  if (!write) begin
    string csr_name = csr.get_name();
    uvm_reg_data_t pred_value = csr.get_mirrored_value();

    if (csr_name == "error_log") pred_value = error_log_pred;
    else if (csr_name == "error_log_address") pred_value = error_log_address_pred;

    // Check the read data matches what we expected.
    if (item.d_data != pred_value)
      `uvm_error(`gfn,
                 $sformatf("Unexpected value when reading from %0s. Seen=0x%0h; Predicted=0x%0h",
                           csr_name, item.d_data, pred_value))
  end
endtask

function void racl_ctrl_scoreboard::check_policies();
  dv_base_reg  regs[$];
  cfg.regs.get_policy_registers(regs);

  for (int unsigned i = 0; i < regs.size(); i++) begin
    logic [31:0] seen     = cfg.policies_vif.get_policy(i);
    logic [31:0] expected = regs[i].get_mirrored_value();

    // If the register is currently marked as busy, that means something is currently reading or
    // writing it. If it's a write, we may not yet have updated the prediction to match the value
    // that is being written. Skip the check in this case. Note that we won't miss a mismatch: the
    // watch_policies task will call us again on the next clock edge.
    if (regs[i].is_busy()) continue;

    if (seen !== expected) begin
      `uvm_error(`gfn, $sformatf("Policy output mismatch for index %0d: seen %0x; expected %0x",
                                 i, seen, expected))
    end
  end
endfunction

task racl_ctrl_scoreboard::watch_policies();
  forever begin
    wait(!cfg.under_reset);

    check_policies();

    fork begin : isolation_fork
      fork
        wait(cfg.under_reset);
        begin
          @(cfg.policies_vif.policies);
          @(negedge cfg.clk_rst_vif.clk);
        end
      join_any
      disable fork;
    end join
  end
endtask

task racl_ctrl_scoreboard::watch_arbitrated_errors();
  dv_base_reg error_log_reg         = cfg.regs.get_error_log_reg();
  dv_base_reg error_log_address_reg = cfg.regs.get_error_log_address_reg();

  // Extract fields from error_log_reg
  uvm_reg_field valid_fld       = error_log_reg.get_field_by_name("valid");
  uvm_reg_field overflow_fld    = error_log_reg.get_field_by_name("overflow");
  uvm_reg_field read_access_fld = error_log_reg.get_field_by_name("read_access");
  uvm_reg_field role_fld        = error_log_reg.get_field_by_name("role");
  uvm_reg_field ctn_uid_fld     = error_log_reg.get_field_by_name("ctn_uid");

  // Extract the (only) field from error_log_address_reg
  uvm_reg_field address_fld = error_log_address_reg.get_field_by_name("address");

  // All the fields that we just searched for should have existed (which means that none of the
  // objects should be null)
  if (! (valid_fld && overflow_fld && read_access_fld && role_fld && ctn_uid_fld))
    `uvm_fatal(`gfn, "Failed to extract one or more fields from ERROR_LOG register.")

  forever begin
    racl_error_log_item item;
    arb_predictor.merged_errors_fifo.get(item);

    // TODO: Interrupt

    // Predict a new value for the ERROR_LOG register. We can predict the relevant fields (extracted
    // above) separately. Note that the register is read-only to software, so these predictions use
    // UVM_PREDICT_DIRECT.
    //
    // Before calling predict() on each field, make sure that the integers in the item's role and
    // ctn_uid are small enough to be representable in the register. This should always work: if
    // not, generate an error that shows the testbench is broken.
    if (item.role >> role_fld.get_n_bits())
      `uvm_error(`gfn, $sformatf("Item has a role of %0h, but the field only has %0d bits",
                                 item.role,
                                 role_fld.get_n_bits()))
    if (item.ctn_uid >> ctn_uid_fld.get_n_bits())
      `uvm_error(`gfn, $sformatf("Item has a ctn_uid of %0h, but the field only has %0d bits",
                                 item.ctn_uid,
                                 ctn_uid_fld.get_n_bits()))

    error_log_pred  = 1                   << valid_fld.get_lsb_pos();
    error_log_pred |= item.overflow       << overflow_fld.get_lsb_pos();
    error_log_pred |= item.read_not_write << read_access_fld.get_lsb_pos();
    error_log_pred |= item.role           << role_fld.get_lsb_pos();
    error_log_pred |= item.ctn_uid        << ctn_uid_fld.get_lsb_pos();

    // Tell mirror_error_log that we've updated error_log_pred. If the task is currently idle, it
    // will start trying to update the register prediction.
    error_log_pred_changed_ev.trigger();

    // Predict a new value for the ERROR_LOG_ADDRESS register, using the same framework as the code
    // above that predicts ERROR_LOG.
    if (item.request_address >> address_fld.get_n_bits())
      `uvm_error(`gfn, $sformatf({"Item has a request_address of %0h, ",
                                  "but the one field of error_log_address only has %0d bits"},
                                 item.request_address, address_fld.get_n_bits()))

    error_log_address_pred = item.request_address << address_fld.get_lsb_pos();

    error_log_address_pred_changed_ev.trigger();
  end
endtask

task racl_ctrl_scoreboard::mirror_error_log();
  dv_base_reg error_log_reg = cfg.regs.get_error_log_reg();
  forever begin
    // Wait until we are told that the event has been triggered
    error_log_pred_changed_ev.wait_on();

    // Now wait until we can safely update the predicted value of the register, using the register's
    // access_lock.
    error_log_reg.take_lock();

    // Give a UVM_PREDICT_DIRECT prediction of the register value using the current value of
    // error_log_pred (which may have changed since we started waiting for the lock). This shouldn't
    // fail (the only way that it can fail is if a field's prediction sees a collision, but the lock
    // we hold should prevent that).
    if(!error_log_reg.predict(error_log_pred)) begin
      `uvm_error(`gfn, "Failed to predict ERROR_LOG: presumably because of a race.")
    end

    error_log_reg.release_lock();

    // Clear the event again (because nothing has run since we last took a copy of error_log_pred),
    // so that the next iteration will only run when the prediction is updated again.
    error_log_pred_changed_ev.reset();
  end
endtask

task racl_ctrl_scoreboard::mirror_error_log_address();
  dv_base_reg error_log_address_reg = cfg.regs.get_error_log_address_reg();
  forever begin
    // Wait until we are told that the event has been triggered
    error_log_address_pred_changed_ev.wait_on();

    // Now wait until we can safely update the predicted value of the register, using the register's
    // access_lock.
    error_log_address_reg.take_lock();

    // Give a UVM_PREDICT_DIRECT prediction of the register value using the current value of
    // error_log_pred (which may have changed since we started waiting for the lock). This shouldn't
    // fail (the only way that it can fail is if a field's prediction sees a collision, but the lock
    // we hold should prevent that).
    if(!error_log_address_reg.predict(error_log_address_pred)) begin
      `uvm_error(`gfn, "Failed to predict ERROR_LOG_ADDRESS: presumably because of a race.")
    end

    error_log_address_reg.release_lock();

    // Clear the event again (because nothing has run since we last took a copy of error_log_pred),
    // so that the next iteration will only run when the prediction is updated again.
    error_log_address_pred_changed_ev.reset();
  end
endtask
