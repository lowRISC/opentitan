// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A set of callbacks attached to some registers in the rram_ctrl environment.
//
// To use it:
//
//   - In the scoreboard's run_phase, start the clean_write_queue() task.
//   - Call uvm_reg_field_cb::add() to connect each monitored field to this cbs class.
//   - To have an rdata check for a field, call enable_field_rdata_check() with it.
//   - Call on_reset() from the scoreboard on resets.

class rram_ctrl_reg_cbs extends uvm_reg_cbs;
  `uvm_object_utils(rram_ctrl_reg_cbs)

  // A layer of "direct predictions". These are used for fields in registers that can be updated by
  // hardware, meaning that we might need to update our estimate of the field's value when there is
  // a register operation in progress. Doing that in the register model itself isn't possible. This
  // associative array gives an extra layer.
  //
  // We normally expect fields of registers that are not busy to be tracked by the register model
  // (with values from this array popped and incorporated into that model as part of post_predict).
  // There are some small race windows, where a HW update happens on the same time step as a
  // register access completes (which is at least a cycle after any write happened). In this
  // situation, the new prediction will be in m_direct_predictions and that's fine! It is a more
  // precise prediction of what is going on, so the only disadvantage is that the register model
  // won't know about it.
  //
  // To compare reads of a field against the predictions in this class, call set_compare() on the
  // field with UVM_NO_CHECK, which will stop uvm_reg_predictor from checking against its register
  // model (which might be out of date). Then use enable_field_rdata_check() to cause reads of the
  // field to be checked in this class.
  local uvm_reg_data_t m_direct_predictions[uvm_reg_field];

  // A queue of register items that are being written to a specific field.
  typedef uvm_reg_item pred_queue_t[$];

  // Queues of WRITE items that are being written to fields through the register layer. A value is
  // appended to the queue when the write starts in pre_write(). The head of the queue is used as
  // part of prediction update at the end of post_predict. That head is finally popped from the
  // queue in post_write().
  //
  // It's possible for an item to be dropped (if a write returns a status other than UVM_IS_OK). To
  // support this case, the pop that happens in post_write will discard items that have a different
  // uvm_reg_item.
  local pred_queue_t m_pending_writes[uvm_reg_field];

  // The set of fields that are modelled and whose values should be checked when they are seen in
  // bus transactions. The modelling is built from a combination of the register model and
  // m_direct_predictions. Add a field with enable_field_rdata_check()
  local bit m_fields_to_check[uvm_reg_field];

  // A queue of fields with an item that should be popped from m_pending_writes when m_pop_write_ev
  // is next triggered.
  local uvm_reg_field m_pop_write_queue[$];

  // When this event is triggered (by post_write), any running instance of clean_write_queue() will
  // consume values from m_pop_write_queue and pop the corresponding write from m_pending_writes.
  local uvm_event m_pop_write_ev;

  extern function new (string name="");

  // Enable a check for this field's value when it is read in a bus transaction.
  //
  // The check runs in post_predict when kind is UVM_PREDICT_READ, which means "We have just seen
  // the following value in a bus transaction. Please update the register prediction accordingly."
  extern function void enable_field_rdata_check(uvm_reg_field fld);

  // A task that runs forever to clean the queue of pending writes after register transactions
  //
  // The precise flow is quite complicated, and works as follows:
  //
  //   - A call to some_reg.write(123) causes fields in the register to call pre_write. Fields that
  //     are tracked by this class instance will have "pending write" items written to
  //     m_pending_writes.
  //
  //   - When the register write completes (with monitor in tl_agent seeing the transaction), this
  //     is reported to a uvm_reg_predictor, which calls do_predict() on the field.
  //
  //   - At the end of do_predict, the post_predict function in this class is run, and might use the
  //     wdata from the pending write to inform the register prediction it makes.
  //
  //   - In parallel with the monitor-driven steps above, there is a stimulus-driven step that calls
  //     post_write(). That task pushes the field in question into m_pop_write_queue and triggers
  //     m_pop_write_ev.
  //
  //   - At that point, a running instance of this task will unblock, then wait a small positive
  //     amount of time before popping the value from m_pending_writes.
  //
  // All of this complication is to work around a difficulty caused by the fact that OpenTitan's
  // bus2reg ignores the value of d_error when producing a uvm_reg_item.
  //
  //  - That means that the status of the resulting uvm_reg_item is UVM_IS_OK, so we can't pass the
  //    bus item to uvm_reg_predictor. If we did, it would view the error-response register access
  //    as implying a register prediction.
  //
  //  - To avoid this, the scoreboard filters out those bus transactions.
  //
  //  - This means that post_predict() won't run (so can't be used to pop the pending write)
  //
  //  - post_write *will* run, so can be used to pop the prediction again. Unfortunately, it will be
  //    scheduled in the same time slot as post_predict (if that function runs), so we can't
  //    guarantee that post_write won't delete the value that post_predict needs.
  extern task clean_write_queue();

  // A reset has just happened. Clear any entries from m_direct_predictions, m_pending_writes and
  // m_pop_write_queue.
  extern function void on_reset();

  // Make a direct prediction for a register field
  //
  // If the field isn't currently busy, the prediction will be written to the register model. If the
  // field is busy, the prediction will be stored in m_direct_predictions, where it can be seen with
  // get_fld_prediction().
  extern function void make_direct_prediction(uvm_reg_field fld, uvm_reg_data_t value);

  // Get the testbench's best possible prediction of the field's current value, taking direct
  // predictions into account.
  extern function uvm_reg_data_t get_fld_prediction(uvm_reg_field fld);

  // Get the testbench's best possible prediction of the register's current value. This is built
  // from calls to get_fld_prediction() for the fields in the register.
  extern function uvm_reg_data_t get_reg_prediction(uvm_reg register);

  // Standard function from uvm_reg_cbs that is called as part of do_predict.
  //
  // The implementation in this class merges any direct prediction with values that are seen from
  // bus transactions, allowing it to improve predictions for the value of the register.
  //
  // There is a race condition with this mechanism:
  //
  //    Cycle 0: A-channel transaction to write 123 to the register causes the register value to be
  //             written.
  //
  //    Cycle 1: Hardware update to the field sets it to 456.
  //
  //    Cycle 2: D-channel transaction is sent by the HW, reporting that the write of 123 happened.
  //
  // With this sequence of events, the field will have value 456. Unfortunately, this class can't
  // distinguish between that sequence of events and the version with items 0 and 1 swapped.
  //
  // We don't *want* to model the timing precisely enough to be able to distinguish the options for
  // these races (because we'd end up modelling the internals of the reg_top implementation). As
  // such, we pick the version where the value from the bus access wins. This will behave reasonably
  // if the environment forgets to model some HW update.
  //
  // The same race is visible for reads (because the register value gets sampled with the A-channel
  // transaction and only reported later in the D-channel transaction). There, the results are
  // worse: there will be an error from the apparent rdata mismatch.
  extern function void post_predict(input uvm_reg_field fld,
                                    input uvm_reg_data_t previous,
                                    inout uvm_reg_data_t value,
                                    input uvm_predict_e kind,
                                    input uvm_path_e path,
                                    input uvm_reg_map map);

  // Standard task from uvm_reg_cbs
  extern task pre_write(uvm_reg_item rw);

  // Standard task from uvm_reg_cbs
  extern task post_write(uvm_reg_item rw);
endclass

function rram_ctrl_reg_cbs::new(string name="");
  super.new(name);
  m_pop_write_ev = new();
endfunction

function void rram_ctrl_reg_cbs::enable_field_rdata_check(uvm_reg_field fld);
  m_fields_to_check[fld] = 1;
endfunction

task rram_ctrl_reg_cbs::clean_write_queue();
  forever begin
    while (m_pop_write_queue.size()) begin
      uvm_reg_field fld = m_pop_write_queue.pop_front();

      if (!m_pending_writes.exists(fld)) begin
        `uvm_fatal("pop_nonexistent_field",
                   $sformatf({"Cannot pop pending write for field %0s: ",
                              "it has no queue in m_pending_writes."},
                             fld.get_full_name()))
      end
      if (!m_pending_writes[fld].size()) begin
        `uvm_fatal("none_pending_for_field",
                   $sformatf({"Cannot pop pending write for field %0s: ",
                              "its m_pending_writes queue is empty."},
                             fld.get_full_name()))
      end

      void'(m_pending_writes[fld].pop_front());
    end

    m_pop_write_ev.wait_ptrigger();

    // The event has just been triggered by post_write. We need to wait until a later time slot to
    // avoid races where post_write and do_predict are both running at the same time.
    #1;
  end
endtask

function void rram_ctrl_reg_cbs::on_reset();
  m_direct_predictions.delete();
  m_pending_writes.delete();
  m_pop_write_queue.delete();
endfunction

function void rram_ctrl_reg_cbs::make_direct_prediction(uvm_reg_field fld, uvm_reg_data_t value);
  // Mask the predicted value with the number of bits in the field. Doing this (rather than throwing
  // an error) might make it slightly more convenient to call this function to make predictions.
  value &= (uvm_reg_data_t'(1) << fld.get_n_bits()) - 1;

  if (!fld.get_parent().is_busy()) begin
    // If the field's parent register isn't busy, we can make a direct prediction of the field's
    // value. This shouldn't fail (the only reason it can fail is if the register is busy), so we
    // generate a fatal error if it does.
    if (!fld.predict(value)) begin
      `uvm_fatal("failed_predict",
                 $sformatf("Failed to predict value of %0s.", fld.get_full_name()))
    end

    // There *might* have been a value for the field in m_direct_predictions (there's a race that
    // makes this possible if a direct prediction happens as an access is finishing). If that has
    // happened, there's no problem: we can just use this new prediction. But we should get rid of
    // the stale one.
    m_direct_predictions.delete(fld);
  end else begin
    // The register is busy. Set a direct prediction for the field's value (overwriting any value
    // that was already there).
    m_direct_predictions[fld] = value;
  end
endfunction

function uvm_reg_data_t rram_ctrl_reg_cbs::get_fld_prediction(uvm_reg_field fld);
  return (m_direct_predictions.exists(fld) ?
          m_direct_predictions[fld] :
          fld.get_mirrored_value());
endfunction

function uvm_reg_data_t rram_ctrl_reg_cbs::get_reg_prediction(uvm_reg register);
  // This is basically a clone of uvm_reg::get_mirrored_value, but using get_fld_prediction()
  // instead of getting the fields' mirrored values.
  uvm_reg_field  fields[$];
  uvm_reg_data_t prediction = 0;

  register.get_fields(fields);
  foreach (fields[i]) begin
    prediction |= get_fld_prediction(fields[i]) << fields[i].get_lsb_pos();
  end

  return prediction;
endfunction

function void rram_ctrl_reg_cbs::post_predict(input uvm_reg_field  fld,
                                              input uvm_reg_data_t previous,
                                              inout uvm_reg_data_t value,
                                              input uvm_predict_e  kind,
                                              input uvm_path_e     path,
                                              input uvm_reg_map    map);
  bit            has_pending_write;
  uvm_reg_data_t reg_wdata, fld_wdata;
  string         reg_fld_name = $sformatf("%0s.%0s", fld.get_parent().get_name(), fld.get_name());

  bit            has_direct_pred;
  uvm_reg_data_t direct_pred;
  uvm_reg_data_t best_old_pred;

  // The code below is designed for predictions caused by bus items. Manual predictions, from
  // dubious virtual sequences that falsely claim UVM_PREDICT_READ, are different. We don't want to
  // cause spurious rdata mismatches for these, but can spot them (and ignore them) because map will
  // be null.
  if (map == null) begin
    return;
  end

  // If this is a write access that came from some_reg.write(), the value being written should be at
  // the front of a corresponding nonempty queue in m_pending_writes.
  //
  // There might not be any such data if the write access was driven more directly (by calling
  // tl_access) or if we are just observing the block in passive mode.
  if (kind == UVM_PREDICT_WRITE) begin
    if (m_pending_writes.exists(fld) && (m_pending_writes[fld].size() > 0)) begin
      has_pending_write = 1;

      // Grab the write data from the earliest item in m_pending_writes. In theory, we might get
      // wdata from an earlier write that responded with an error (so that post_write didn't run).
      // In this case, the risk is that the prediction might be incorrect if the field is W1S or W0C
      // and we've had a hardware prediction in the meantime.
      //
      // This cannot be a problem while tl_agent::tl_reg_adapter::bus2reg only responds with error
      // on reset. If that changes, we'll have to restructure this class.
      reg_wdata = m_pending_writes[fld][0].value[0];

      fld_wdata = (reg_wdata >> fld.get_lsb_pos()) & ((1 << fld.get_n_bits()) - 1);
    end
  end

  // Override the register model's prediction for fld by popping any entry in m_direct_predictions.
  if (m_direct_predictions.exists(fld)) begin
    has_direct_pred = 1;
    direct_pred = m_direct_predictions[fld];
    m_direct_predictions.delete(fld);

    best_old_pred = direct_pred;
  end else begin
    best_old_pred = fld.get_mirrored_value();
  end

  case (kind)
    UVM_PREDICT_READ: begin
      // The field has just been read. If it has been passed to enable_field_rdata_check() then we
      // should check rdata against our best prediction. The value argument holds the new prediction
      // that uvm_reg_predictor thinks we should make (which is the value we have just read). Check
      // that it matches our prediction
      if (m_fields_to_check.exists(fld)) begin
        if (value != best_old_pred) begin
          `uvm_error("rdata_mismatch",
                     $sformatf("The best prediction of %0s was 0x%0h but rdata was 0x%0h.",
                               fld.get_full_name(), best_old_pred, value))
        end
      end

      // Note: We've now popped any direct prediction. Leave the inout value argument unchanged: the
      // rdata is definitely the best prediction of the register value now.
    end

    UVM_PREDICT_WRITE: begin
      // This is a prediction based on writing the register. The correct new prediction depends on
      // the access rules for the field and also the value being written (which we took note of in
      // pre_write and is now in the fld_wdata variable).

      case (fld.get_access())
        "RO": begin
          // Writing an RO field won't do anything. Take the prediction from direct_pred if there is
          // one.
          if (has_direct_pred) begin
            value = direct_pred;
          end
        end

        "RW": begin
          // Writing an RW field will overwrite any prediction we had before. Leave the value
          // inferred from the fld_wdata.
        end

        "W1C": begin
          // The correct prediction might be different if we have written zero (which doesn't clear
          // any bits) and best_old_pred has fewer bits set than the register model prediction.
          //
          // Of course, this only works if we know what value was written, which depends on this
          // having been an access through uvm_reg::do_write(). If not, we're kind of stuck. We
          // don't expect this to happen though, because this would need the write to overlap with
          // accesses through the register layer that cause the register to be busy. If it happens,
          // raise an error and ignore the direct prediction.
          if (has_pending_write) begin
            value = best_old_pred & ~fld_wdata;
          end else if (has_direct_pred) begin
            `uvm_error("no_fld_wdata",
                       $sformatf({"Access to %0s that didn't come through uvm_reg::do_write has ",
                                  "just finished. It overlapped with something that did."},
                                 fld.get_full_name()))
          end
        end

        "W0C": begin
          // The correct prediction might be different if we have written '1 (which doesn't clear
          // any bits) and best_old_pred has fewer bits set than the register model prediction.
          //
          // As with the W1C case, fail with an error if there is no pending fld_wdata.
          if (has_pending_write) begin
            value = best_old_pred & fld_wdata;
          end else if (has_direct_pred) begin
            `uvm_error("no_fld_wdata",
                       $sformatf({"Access to %0s that didn't come through uvm_reg::do_write has ",
                                  "just finished. It overlapped with something that did."},
                                 fld.get_full_name()))
          end
        end

        default: begin
          // It's possible to support more access values than are currently in this case statement,
          // but the chosen values are the ones that were needed for the initial scoreboard bringup.
          // If adding a field with a different access rule, add that rule to this case statement.
          `uvm_fatal("unsupported_access",
                     $sformatf("The field %0s has access rule '%0s', which we don't support.",
                               fld.get_full_name(), fld.get_access()))
        end
      endcase
    end

    default: begin
      `uvm_fatal("unsupported_kind",
                 $sformatf("post_predict with kind=%0s (%0d).", kind.name(), kind))
    end
  endcase
endfunction

task rram_ctrl_reg_cbs::pre_write(uvm_reg_item rw);
  uvm_reg_field fld;

  super.pre_write(rw);

  if (!$cast(fld, rw.element)) begin
    `uvm_fatal("not_field",
               $sformatf({"pre_write called for item %0s, which isn't a field. ",
                          "These cbs should only be attached to fields."},
                         rw.element.get_name()))
  end

  if (m_pending_writes.exists(fld)) begin
    m_pending_writes[fld].push_back(rw);
  end else begin
    m_pending_writes[fld] = '{rw};
  end
endtask

task rram_ctrl_reg_cbs::post_write(uvm_reg_item rw);
  uvm_reg_field fld;
  int unsigned  num_mismatches;
  bit           found_match;

  super.post_write(rw);

  if (!$cast(fld, rw.element)) begin
    `uvm_fatal("not_field",
               $sformatf({"post_write called for item %0s, which isn't a field. ",
                          "These cbs should only be attached to fields."},
                         rw.element.get_name()))
  end

  if (!m_pending_writes.exists(fld)) begin
    `uvm_fatal("no_pending_write_queue",
               $sformatf({"post_write called for field %0s, but that field has ",
                          "no queue in m_pending_writes."},
                         fld.get_full_name()))
  end

  // Walk from the front of the queue of pending writes and count how many items don't match before
  // we find a match.
  foreach (m_pending_writes[fld][i]) begin
    if (m_pending_writes[fld][i] == rw) begin
      found_match = 1;
      break;
    end
    num_mismatches++;
  end

  if (!found_match) begin
    `uvm_fatal("no_match_in_pending_writes",
               $sformatf({"post_write called for field %0s but there was no pending ",
                          "write with the same uvm_reg_item (after discarding %0d mismatches)"},
                         fld.get_full_name(), num_mismatches))
  end

  // At this point, push 1 + num_mismatches copies of fld into m_pop_write_queue and trigger
  // m_pop_write_ev so that clean_write_queue discards the mismatches and the match.
  repeat (num_mismatches + 1) m_pop_write_queue.push_back(fld);
  m_pop_write_ev.trigger();
endtask
