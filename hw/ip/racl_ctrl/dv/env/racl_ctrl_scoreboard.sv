// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class racl_ctrl_scoreboard extends cip_base_scoreboard #(.CFG_T(racl_ctrl_env_cfg),
                                                         .RAL_T(racl_ctrl_reg_block),
                                                         .COV_T(racl_ctrl_env_cov));
  `uvm_component_utils(racl_ctrl_scoreboard)

  uvm_analysis_export #(racl_error_log_vec_item) internal_errors_export;
  uvm_analysis_export #(racl_error_log_vec_item) external_errors_export;

  extern function new (string name, uvm_component parent);

  extern function void build_phase(uvm_phase phase);
  extern function void connect_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);
  extern task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);

  // An event that triggers a process inside the watch_interrupt task to tell it that the expected
  // value of the interrupt might have changed. This should be connected to a callback for
  // post_predict on the IE field of the INTR_ENABLE register and similarly for the RACL_ERROR field
  // of INTR_TEST.
  uvm_event check_interrupt_ev;

  // A function called when process_tl_accesses is notified of a bus access on the A channel. We use
  // this to update predictions of the input to the prim_intr_hw that drives the racl_error
  // interrupt (we can't use standard register predictions because the full write transaction needs
  // to wait for a D-channel response, which only arrives too late).
  extern local function void process_tl_a_channel(tl_seq_item item, string ral_name);

  // A function called when process_tl_accesses is notified of a bus access on the D channel.
  extern local function void process_tl_d_channel(tl_seq_item item, string ral_name);

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

  // Consume a write to the ERROR_LOG register, setting error_log_d_pred and thus error_log_q_pred.
  // This is called from watch_arbitrated_errors but also called after an A-channel write request
  // for the register.
  extern local function void take_error_log_write(uvm_reg_data_t data, bit [3:0] byte_mask);

  // Get the prediction of whether the racl_error interrupt should currently be asserted. If
  // require_enable is false, this doesn't require the interrupt to be enabled (so can be used to
  // predict the INTR_STATE register)
  extern local function bit get_intr_pred(bit require_enable);

  // Watch the value of the interrupt and check it stays in sync with ERROR_LOG.VALID.
  extern local task watch_interrupt();

  // Keep the predicted value of the ERROR_LOG register up to date with error_log_q_pred, waiting
  // for the register not to be in use.
  extern local task mirror_error_log();

  // Keep the predicted value of the ERROR_LOG_ADDRESS register up to date with
  // error_log_address_q_pred, waiting for the register not to be in use.
  extern local task mirror_error_log_address();

  // Keep the predicted value of the INTR_STATE.RACL_ERROR field up to date with intr_valid_q_pred
  extern local task mirror_racl_error_field();

  // Watch the under_reset flag. When a reset is seen, reset all modelled state.
  extern local task track_resets();

  // Watch the clock, copying "d" values to "q" values on each edge.
  extern local task model_registers();

  // Check the pending_csr_write variable and apply any CSR write on the negedge of the clock. The
  // variable gets set by process_tl_a_channel on a posedge, and delaying until the negedge ensures
  // that the TL write is predicted to win over a HW update.
  extern local task process_csr_writes();

  // A handle pointing at the block's RAL (to avoid lots of tasks having to look it up).
  local dv_base_reg_block reg_block;

  // A prediction of the current values of the inputs and values for the INTR_ENABLE and INTR_TEST
  // registers. Note that we also can't use get_mirrored_value for the "q predictions" because the
  // D-channel response that causes the register prediction might only be accepted several cycles
  // after the A-channel request.
  local bit intr_enable_d_pred, intr_enable_q_pred;
  local bit intr_test_d_pred, intr_test_q_pred;

  // A model that arbitrates between errors that have been detected by the error log agents in the
  // environment and fed through to *_errors_export above. Its output is not connected to any
  // export, but it is consumed by the watch_arbitrated_errors task.
  local racl_ctrl_error_arb_predictor arb_predictor;

  // A prediction of the current value of the ERROR_LOG register. This doesn't use the RAL because
  // hardware changes might happen at the same time as an access to the register, which would cause
  // a race condition. Because we predict the "d side" of the register, this needs separate d/q
  // predictions.
  local uvm_reg_data_t error_log_d_pred, error_log_q_pred;

  // An event that gets triggered on a change to error_log_pred, telling mirror_error_log to update
  // the RAL prediction of the ERROR_LOG register.
  local uvm_event error_log_pred_changed_ev;

  // A prediction of the current value of the ERROR_LOG_ADDRESS register and an event for when it
  // gets written (see the documentation for error_log_pred and error_log_pred_changed_ev).
  local uvm_reg_data_t error_log_address_d_pred, error_log_address_q_pred;

  // An event that gets triggered on a change to error_log_pred, telling mirror_error_log to update
  // the RAL prediction of the ERROR_LOG register.
  local uvm_event error_log_address_pred_changed_ev;

  // An event that gets changed on a change to intr_valid_q_pred, telling mirror_racl_error_field to
  // update the RAL prediction of INTR_STATE.ERROR_LOG.
  local uvm_event racl_error_fld_changed_ev;

  // A prediction for the current value of the "valid" field of error_log. We copy this out of
  // error_log_pred to two separate variables because this means that consumers don't need to unpack
  // the ERROR_LOG register value.
  local bit intr_valid_d_pred, intr_valid_q_pred;

  // The most recently seen TL write as a tl_seq_item. This gets populated by process_tl_a_channel
  // if it sees a write to a CSR, and is then consumed (and set to null again) on the following
  // negedge by the process_csr_writes task.
  local tl_seq_item pending_csr_write;
endclass

function racl_ctrl_scoreboard::new (string name, uvm_component parent);
  super.new(name, parent);
  check_interrupt_ev = new();
  error_log_pred_changed_ev = new();
  error_log_address_pred_changed_ev = new();
  racl_error_fld_changed_ev = new();
endfunction

function void racl_ctrl_scoreboard::build_phase(uvm_phase phase);
  string ral_name;

  super.build_phase(phase);
  // TODO: remove once support alert checking
  do_alert_check = 0;

  internal_errors_export = new("internal_errors_export", this);
  external_errors_export = new("external_errors_export", this);

  arb_predictor = racl_ctrl_error_arb_predictor::type_id::create("arb_predictor", this);
  arb_predictor.cfg = cfg;

  // We expect there to be a RAL model for exactly one register block. Grab a reference to it.
  if (cfg.ral_models.size() != 1) begin
    `uvm_fatal(`gfn, $sformatf("Number of register blocks = %0d, not 1.", cfg.ral_models.size()))
  end
  if (!cfg.ral_models.first(ral_name)) `uvm_fatal(`gfn, "first failed on a nonempty array")
  reg_block = cfg.ral_models[ral_name];
  if (reg_block == null) `uvm_fatal(`gfn, "Couldn't find reg block")
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
        watch_interrupt();
        mirror_error_log();
        mirror_error_log_address();
        mirror_racl_error_field();
        track_resets();
        model_registers();
        process_csr_writes();
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

function void racl_ctrl_scoreboard::process_tl_a_channel(tl_seq_item item, string ral_name);
  uvm_reg_addr_t    csr_addr;

  uvm_reg           intr_enable_reg, intr_test_reg;
  bit               intr_enable_d, intr_test_d, intr_value_d;

  // A-channel monitoring is only used to catch write requests, so we needn't track read requests.
  if (!item.is_write) return;

  // Figure out what register is being accessed
  csr_addr = reg_block.get_word_aligned_addr(item.a_addr);

  // If this is a request to a non-existent register, we don't expect it to have any effect. Ignore
  // it.
  if (reg_block.default_map.get_reg_by_offset(csr_addr) == null) return;

  // We only care about writes that might touch the bottom bit, so ignore writes where the bottom
  // bit of the byte mask is false.
  if (!(item.a_mask & 1)) return;

  // If we get here, we know that an A-side channel transaction has just finished that tries to
  // write to a known csr. Set the pending_csr_write variable to point at this write. It will then
  // be applied on the negedge of the clock (so that it "wins" for the prediction if HW requests a
  // register update on the same cycle)
  pending_csr_write = item;
endfunction

function void racl_ctrl_scoreboard::process_tl_d_channel(tl_seq_item item, string ral_name);
  bit            write    = item.is_write();
  uvm_reg_addr_t csr_addr = reg_block.get_word_aligned_addr(item.a_addr);
  uvm_reg        csr      = reg_block.default_map.get_reg_by_offset(csr_addr);

  if (csr == null) `uvm_fatal(`gfn, $sformatf("Could not find CSR for address 0x%0h", csr_addr))

  // If this is the D channel response for a write to one of the policy registers, check that it has
  // been applied to racl_policies_o.
  if (write && cfg.regs.is_policy_reg(csr)) check_policies();

  // If this is the D channel response to a register read, work out the value we think it should
  // have (probably the mirrored value of the register) and check that item.d_data matches.
  if (!write) begin
    string csr_name = csr.get_name();
    uvm_reg_data_t allowed_values[$] = {csr.get_mirrored_value()};
    bit matched_value;

    if (csr_name == "error_log") allowed_values = {error_log_q_pred};
    else if (csr_name == "error_log_address") allowed_values = {error_log_address_q_pred};
    else if (csr_name == "intr_state") begin
      // Because the bus access might happen at the same time as an error log being raised (which
      // gets processed by watch_arbitrated_errors), the INTR_STATE.RACL_ERROR field might have
      // changed value. The RAL prediction will be updated by the mirror_error_log task, but this
      // bus access might have kept it waiting. Add any new value to the list of allowed values.
      uvm_reg_data_t fld_mask = 1 << 0;
      allowed_values.push_back((allowed_values[0] & ~fld_mask) | (error_log_q_pred & fld_mask));
    end

    // Work through the list of allowed values and check whether the read transaction we've just
    // seen matches any of them.
    foreach (allowed_values[i]) begin
      if (item.d_data == allowed_values[i]) begin
        matched_value = 1'b1;
        break;
      end
    end

    if (!matched_value) begin
      `uvm_error(`gfn,
                 $sformatf("Unexpected value when reading from %0s. Seen=0x%0h; Allowed: %0p",
                           csr_name, item.d_data, allowed_values))
    end
  end
endfunction

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

    error_log_d_pred  = 1                   << valid_fld.get_lsb_pos();
    error_log_d_pred |= item.overflow       << overflow_fld.get_lsb_pos();
    error_log_d_pred |= item.read_not_write << read_access_fld.get_lsb_pos();
    error_log_d_pred |= item.role           << role_fld.get_lsb_pos();
    error_log_d_pred |= item.ctn_uid        << ctn_uid_fld.get_lsb_pos();

    // Predict a new value for the ERROR_LOG_ADDRESS register, using the same framework as the code
    // above that predicts ERROR_LOG.
    if (item.request_address >> address_fld.get_n_bits())
      `uvm_error(`gfn, $sformatf({"Item has a request_address of %0h, ",
                                  "but the one field of error_log_address only has %0d bits"},
                                 item.request_address, address_fld.get_n_bits()))

    error_log_address_d_pred = item.request_address << address_fld.get_lsb_pos();

    // Finally, predict the behaviour of the racl_error interrupt (which must have just been set)
    intr_valid_d_pred = 1'b1;
  end
endtask

function void racl_ctrl_scoreboard::take_error_log_write(uvm_reg_data_t data, bit [3:0] byte_mask);
  // The only field of ERROR_LOG that is not read-only is the VALID field, which is stored at bit
  // zero. This is rw1c, so we need to clear its predicted bottom bit if the bottom bit of data is 1
  // and the bottom byte is enabled.
  if (data[0] & byte_mask[0]) begin
    error_log_d_pred[0] = 1'b0;
    intr_valid_d_pred = 0;
  end
endfunction

function bit racl_ctrl_scoreboard::get_intr_pred(bit require_enable);
  bit enabled = require_enable ? intr_enable_d_pred : 1'b1;
  return (intr_valid_q_pred | intr_test_q_pred) & enabled;
endfunction

task racl_ctrl_scoreboard::watch_interrupt();
  dv_base_reg_field intr_state_fld = cfg.regs.get_intr_state_racl_error_fld();

  forever begin
    // The interrupt signal is of Status type and is controlled by a prim_intr_hw called
    // u_intr_racl_error. A genuine interrupt would be signalled through its event_intr_i port,
    // which gets the ERROR_LOG.VALID field.
    //
    // That genuine interrupt may not be enabled, so the prediction also requires the INTR_ENABLE
    // register to be true.
    //
    // Another way that the interrupt can be set is through the INTR_TEST register. Since it's a
    // hwext register (whose state actually lives in prim_intr_hw), we it isn't modelled in the ral,
    // but we model it in an intr_test_q_pred register, which is essentially the test_q signal in
    // prim_intr_hw.
    bit intr_pred = get_intr_pred(1'b1);

    // Check that the interrupt line matches the prediction in intr_pred
    if (intr_pred != cfg.intr_vif.sample() & 1) begin
      `uvm_error(`gfn,
                 $sformatf("racl_error interrupt doesn't match prediction. exp=%0d; seen=%0d",
                           intr_pred, cfg.intr_vif.sample() & 1))
    end

    if (intr_pred != intr_state_fld.get_mirrored_value()) racl_error_fld_changed_ev.trigger();

    // Wait until either the interrupt line changes or our prediction of its value might change
    // (either because of a change to intr_valid_q_pred or a change to INTR_ENABLE)
    fork begin : isolation_fork
      fork
        @(cfg.intr_vif.pins_o[0]);
        @intr_valid_q_pred;
        check_interrupt_ev.wait_on();
      join_any
      disable fork;
    end join

    // Unconditionally reset the timer correctly handle a situation where several different items
    // fired in the fork above.
    check_interrupt_ev.reset();

    // At this point, we don't actually know what point of the cycle we are at. It's possible that
    // the event that just triggered us

    // To avoid spurious failures when the prediction and the interrupt change at the same time,
    // delay for 1ps (to allow things to settle down).
    #1ps;
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
    if(!error_log_reg.predict(error_log_q_pred)) begin
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
    if(!error_log_address_reg.predict(error_log_address_q_pred)) begin
      `uvm_error(`gfn, "Failed to predict ERROR_LOG_ADDRESS: presumably because of a race.")
    end

    error_log_address_reg.release_lock();

    // Clear the event again (because nothing has run since we last took a copy of error_log_pred),
    // so that the next iteration will only run when the prediction is updated again.
    error_log_address_pred_changed_ev.reset();
  end
endtask

task racl_ctrl_scoreboard::mirror_racl_error_field();
  dv_base_reg_field racl_error_fld = cfg.regs.get_intr_state_racl_error_fld();
  uvm_reg           intr_state_uvm_reg = racl_error_fld.get_parent();
  dv_base_reg       intr_state_reg;

  `downcast(intr_state_reg, intr_state_uvm_reg)

  forever begin
    // Wait until we are told that the event has been triggered
    racl_error_fld_changed_ev.wait_on();

    // Now wait until we can safely update the predicted value of the register, using the register's
    // access_lock.
    intr_state_reg.take_lock();

    // Give a UVM_PREDICT_DIRECT prediction of the field value using the result of get_intr_pred(0)
    // (which may have changed since we started waiting for the lock). This shouldn't fail (the only
    // way that it can fail is if a field's prediction sees a collision, but the lock we hold should
    // prevent that).
    if(!racl_error_fld.predict(get_intr_pred(1'b0))) begin
      `uvm_error(`gfn, "Failed to predict ERROR_LOG_ADDRESS: presumably because of a race.")
    end

    intr_state_reg.release_lock();

    // Clear the event again (because nothing has run since we last took a copy of error_log_pred),
    // so that the next iteration will only run when the prediction is updated again.
    racl_error_fld_changed_ev.reset();
  end
endtask

task racl_ctrl_scoreboard::track_resets();
  dv_base_reg error_log_reg         = cfg.regs.get_error_log_reg();
  dv_base_reg error_log_address_reg = cfg.regs.get_error_log_address_reg();

  forever begin
    wait(cfg.under_reset);

    arb_predictor.on_reset();
    error_log_d_pred = error_log_reg.get_reset();
    error_log_q_pred = error_log_reg.get_reset();
    error_log_address_d_pred = error_log_address_reg.get_reset();
    error_log_address_q_pred = error_log_address_reg.get_reset();
    intr_valid_d_pred = 1'b0;
    intr_valid_q_pred = 1'b0;
    intr_test_d_pred = 1'b0;
    intr_test_q_pred = 1'b0;
    intr_enable_d_pred = 1'b0;
    intr_enable_q_pred = 1'b0;

    wait(!cfg.under_reset);
  end
endtask

task racl_ctrl_scoreboard::model_registers();
  bit changes_error_log, changes_error_address_log, may_change_intr;

  forever begin
    cfg.clk_rst_vif.wait_clks(1);
    if (cfg.under_reset) begin
      wait(!cfg.under_reset);
      continue;
    end

    changes_error_log = |(error_log_q_pred ^ error_log_d_pred);
    changes_error_address_log = |(error_log_address_q_pred ^ error_log_address_d_pred);
    may_change_intr = ((intr_valid_q_pred ^ intr_valid_d_pred) |
                       (intr_test_q_pred ^ intr_test_d_pred) |
                       (intr_enable_q_pred ^ intr_enable_d_pred));

    intr_test_q_pred         = intr_test_d_pred;
    intr_enable_q_pred       = intr_enable_d_pred;
    error_log_q_pred         = error_log_d_pred;
    error_log_address_q_pred = error_log_address_d_pred;
    intr_valid_q_pred        = intr_valid_d_pred;

    if (changes_error_log) error_log_pred_changed_ev.trigger();
    if (changes_error_address_log) error_log_address_pred_changed_ev.trigger();
    if (may_change_intr) check_interrupt_ev.trigger();
  end
endtask

task racl_ctrl_scoreboard::process_csr_writes();
  uvm_reg_addr_t csr_addr;
  uvm_reg        csr;
  string         csr_name;

  forever begin
    cfg.clk_rst_vif.wait_n_clks(1);
    if (cfg.under_reset) begin
      wait(!cfg.under_reset);
      continue;
    end

    if (pending_csr_write == null) continue;

    csr_addr = reg_block.get_word_aligned_addr(pending_csr_write.a_addr);
    csr = reg_block.default_map.get_reg_by_offset(csr_addr);

    // We expect to find a CSR here (because process_tl_a_channel only sets pending_csr_write if it
    // corresponds to a genuine CSR)
    if (csr == null) `uvm_fatal(`gfn, "Bogus pending_csr_write with no CSR.")

    // There are only a few CSRs where we need precisely timed predictions (the ones that affect the
    // racl_error interrupt). If we are looking at one of them, update our prediction of its bottom
    // bit.
    csr_name = csr.get_name();
    if (csr_name == "intr_enable") intr_enable_d_pred = pending_csr_write.a_data & 1;
    else if (csr_name == "intr_test") intr_test_d_pred = pending_csr_write.a_data & 1;
    else if (csr_name == "error_log") begin
      take_error_log_write(pending_csr_write.a_data, pending_csr_write.a_mask);
    end

    // Now that we have consumed pending_csr_write, set it back to null.
    pending_csr_write = null;
  end
endtask
