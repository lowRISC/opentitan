// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

//-----------------------------------------------------------------------------
// Description of a predicted change of a register field.
//-----------------------------------------------------------------------------
typedef struct {
  // Unique ID of predicted change; diagnostically useful in log messages.
  int unsigned    id;
  // Previous value of this field.
  uvm_reg_data_t  val_prev;
  // New value of this field.
  uvm_reg_data_t  val_new;
  // Latest time of predicted change.
  int             latest_time;
} timed_field_pred_t;

//-----------------------------------------------------------------------------
// Description of a register field for which timed predictions are to be made.
//-----------------------------------------------------------------------------
class timed_reg_field extends uvm_object;
  `uvm_object_utils(timed_reg_field)

  `uvm_object_new

  // Register field within DV/RAL.
  dv_base_reg_field  field;

  // Maximum expected delay for a predicted change to be met.
  int unsigned       max_delay;

  // Latest matched value of this field; used in predicting CSR read data.
  uvm_reg_data_t     read_latest;

  // Latest prediction for this register field; used for predicting CSR read data.
  bit                pred_valid;
  timed_field_pred_t pred_latest;

  // Latest value of this field observed by the `timed_checker` process.
  uvm_reg_data_t     obs_latest;

  // Queue of predictions for this register field; used by the `timed_checker` process.
  timed_field_pred_t pred_q[$];

  // Prediction ID; diagnostic purposes only.
  static int unsigned pred_id = 0;

  // A change has been predicted for the containing register; form a prediction of this register
  // field is predicted to change.
  function void predict(int unsigned time_now, uvm_reg_data_t new_data, uvm_reg_data_t prev_data);
    uvm_reg_data_t changed_mask = new_data ^ prev_data;
    // Properties of this register field.
    uvm_reg_data_t mask = (1 << field.get_n_bits()) - 1;
    int unsigned lsb = field.get_lsb_pos();

    if ((changed_mask >> lsb) & mask) begin
      // This field is expected to change; form a prediction.
      timed_field_pred_t pred;
      pred.id          = pred_id++;
      pred.val_prev    = (prev_data >> lsb) & mask;
      pred.val_new     = (new_data  >> lsb) & mask;
      pred.latest_time = time_now + int'(max_delay);
      `uvm_info(`gfn, $sformatf(" - field '%s'(ID 0x%0x) <= 0x%0x from 0x%0x by time 0x%0x",
                                field.get_name(), pred.id, pred.val_new, pred.val_prev,
                                pred.latest_time), UVM_MEDIUM)
      // Present this expectation for validating CSR reads from the DUT.
      pred_latest = pred;
      pred_valid  = 1'b1;
      // Present it to the checker also.
      pred_q.push_back(pred);
    end
  endfunction

  // Return the contribution of this register field to a prediction of the read data from the DUT
  // at the specified time.
  function uvm_reg_data_t read(int unsigned time_now, uvm_reg_data_t act_data);
    // Properties of this register field.
    uvm_reg_data_t f_mask = (1 << field.get_n_bits()) - 1;
    int unsigned lsb = field.get_lsb_pos();
    // Predicted value of this register field.
    uvm_reg_data_t pred_val;
    `uvm_info(`gfn, $sformatf(" - field %s : pred valid %d prev 0x%0x new 0x%0x",
                              field.get_name(), pred_valid, pred_latest.val_prev,
                              pred_latest.val_new), UVM_HIGH)
    if (pred_valid) begin
      uvm_reg_data_t act_val = (act_data >> lsb) & f_mask;
      `uvm_info(`gfn, $sformatf("   (time_now 0x%0x latest_time 0x%0x)", pred_latest.latest_time,
                                time_now), UVM_HIGH)
      if (act_val == pred_latest.val_new) begin
        `uvm_info(`gfn, "   Prediction met", UVM_HIGH)
        pred_val = pred_latest.val_new;
        // Prediction met; no longer required.
        pred_valid = 1'b0;
      end else begin
        `uvm_info(`gfn, $sformatf("   Prediction not met; act 0x%0x", act_val), UVM_MEDIUM)
        `DV_CHECK_EQ(act_val, pred_latest.val_prev)
        `DV_CHECK_GT(pred_latest.latest_time - time_now, 0)
        pred_val = pred_latest.val_prev;
      end
      // Retain the latest prediction.
      read_latest = pred_val;
    end else begin
      // We have no new prediction, use the most recent prediction.
      pred_val = read_latest;
    end
    `uvm_info(`gfn, $sformatf("   (predicted as 0x%0x)", pred_val), UVM_HIGH)
    // Return the predicted value pre-shifted to be merged into the register-level prediction.
    return pred_val << lsb;
  endfunction

  // Are there any pending predictions for this register field?
  function bit preds_pending();
    return (pred_q.size() > 0);
  endfunction

  // Check whether the given field of the specified register yet matches the predicted change;
  // object to expired predictions that have not been matched, and any observed value that is
  // neither the previous nor the expected new value of that field.
  function void check_pred(int unsigned time_now, string reg_name, input uvm_reg_data_t act_data);
    // Properties of this register field.
    uvm_reg_data_t mask = (1 << field.get_n_bits()) - 1;
    int unsigned lsb = field.get_lsb_pos();
    // Collect as many expired expectations as possible.
    uvm_reg_data_t act_val = (act_data >> lsb) & mask;
    bit act_changed = (act_val != obs_latest);
    if (act_changed) begin
      `uvm_info(`gfn, $sformatf("Checker observed reg %p field %p change 0x%0x -> 0x%0x",
                                reg_name, field.get_name(), obs_latest, act_val), UVM_MEDIUM)
    end
    do begin
      // Check whether the actual state of the DUT register matches the expectation.
      timed_field_pred_t pred = pred_q[0];
      if (act_val == pred.val_new) begin
        // This expectation has been met and may be discarded.
        `uvm_info(`gfn, $sformatf("Reg %s field %s (ID 0x%0x) met expectation 0x%0x", reg_name,
                                  field.get_name(), pred.id, pred.val_new), UVM_HIGH)
        void'(pred_q.pop_front());
        obs_latest = act_val;
      end else begin
        // Check that the latest time on this prediction has not yet passed; the expression of the
        // comparison copes with timer wraparound too.
        if (!(pred.latest_time - time_now > 0)) begin
          `uvm_info(`gfn, $sformatf("Reg %p field %s (ID 0x%0x) did NOT meet expectation 0x%0x",
                                    reg_name, field.get_name(), pred.id, pred.val_new), UVM_MEDIUM)
          `uvm_info(`gfn, $sformatf(" (time_now 0x%0x)", time_now), UVM_MEDIUM)
          // Report the mismatched value.
          `DV_CHECK_EQ(act_val, pred.val_new);
        end else begin
          // Check that it still matches the previous value.
          `DV_CHECK_EQ(act_val, pred.val_prev);
          break;
        end
      end
    end while (pred_q.size() > 0);
  endfunction
endclass : timed_reg_field

//-----------------------------------------------------------------------------
// Description of a register for which timed-limited predictions are to be made.
//-----------------------------------------------------------------------------
class timed_reg extends uvm_object;
  `uvm_object_utils(timed_reg)

  `uvm_object_new

  // Register bits that we cannot predict; this may be ascertained by consulting the bitmaps
  // of the individual register fields, but we keep a copy for convenience and fast access.
  uvm_reg_data_t unpred_mask = {`UVM_REG_DATA_WIDTH{1'b1}};

  // Predicted fields within this register.
  timed_reg_field fields[$];

  // Add a field to the description of this register.
  //
  // `init_val` specifies the expected initial value of the field (ie. post-DUT reset).
  // `max_delay` gives the maximum expected delay before a prediction is met (in DUT clock cycles).
  function void add_field(input dv_base_reg_field field, input uvm_reg_data_t init_val,
                          int unsigned max_delay);
    timed_reg_field trf = timed_reg_field::type_id::create("trf");
    uvm_reg_data_t mask;
    trf.field = field;
    // Remember the maximum prediction delay.
    trf.max_delay = max_delay;
    // Update the 'unpredictable bits' mask.
    mask = (1 << field.get_n_bits()) - 1;
    unpred_mask &= ~(mask << field.get_lsb_pos());
    // State for CSR reading.
    trf.read_latest = init_val;
    trf.pred_valid = 1'b0;
    // State for `timed_checker` process.
    trf.obs_latest = init_val;
    fields.push_back(trf);
  endfunction

  // A change is expected from `prev_val` to `new_val` is expected for this register; update the
  /// predictions for each of the affected register fields.
  function void predict(int unsigned time_now, uvm_reg_data_t new_data, uvm_reg_data_t prev_data);
    // Post predictions for any affected register fields.
    for (int unsigned f = 0; f < fields.size(); f++) begin
      fields[f].predict(time_now, new_data, prev_data);
    end
  endfunction

  // Form a prediction of the read data expected from the DUT at the given time, propagating
  // the parts of `act_data` (actual read data from the DUT) that cannot be predicted.
  function uvm_reg_data_t read(int unsigned time_now, uvm_reg_data_t act_data);
    // Propagate the bits of the observed DUT register that we are presently unable to predict.
    uvm_reg_data_t pred_data = act_data & unpred_mask;

    // Collect predictions for all of the register fields that we can predict.
    for (int unsigned f = 0; f < fields.size(); f++) begin
      // Collect prediction contribution from this register field.
      pred_data |= fields[f].read(time_now, act_data);
    end
    return pred_data;
  endfunction

  // Are there any pending predictions for this register?
  function bit preds_pending();
    int unsigned f = 0;
    while (f < fields.size()) begin
      if (fields[f].preds_pending()) return 1'b1;
      f++;
    end
    return 1'b0;
  endfunction

  // Check the actual state of the DUT register matches predictions for the current time.
  function void check_pred(int unsigned time_now, string reg_name, uvm_reg_data_t act_data);
    for (int unsigned f = 0; f < fields.size(); f++) begin
      if (fields[f].preds_pending()) fields[f].check_pred(time_now, reg_name, act_data);
    end
  endfunction
endclass : timed_reg
