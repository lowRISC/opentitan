// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A callback attached to some registers in the rram_ctrl environment. This should be given a handle
// to the scoreboard, which it uses to inform the scoreboard about some register events.

class rram_ctrl_reg_cbs extends uvm_reg_cbs;
  `uvm_object_utils(rram_ctrl_reg_cbs)

  // A handle to the scoreboard. This must be set before the start of the simulation (because some
  // of the hooks need to pass information to the scoreboard).
  local rram_ctrl_scoreboard m_scb;

  // A layer of "direct predictions". These are used for fields in registers that can be updated by
  // hardware, meaning that we might need to update our estimate of the field's value when there is
  // a register operation in progress. Doing that in the register model itself isn't possible. This
  // associative array gives an extra step.
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
  // model. Then use enable_field_rdata_check() to cause reads of the field to be checked in this
  // class.
  local uvm_reg_data_t m_direct_predictions[uvm_reg_field];

  // Values being written to fields, reported by pre_write(). These are used as part of a combined
  // prediction update at the end of post_predict.
  local uvm_reg_data_t m_pending_wdata[uvm_reg_field];

  // The set of fields whose rdata should be checked agaisnt a combination of the register model and
  // m_direct_predictions. Add a field with enable_field_rdata_check()
  local bit m_fields_to_check[uvm_reg_field];

  extern function new (string name="");

  // Pass a handle to the scoreboard. This must be called before the start of the simulation
  // (because some of the hooks need to pass information to the scoreboard).
  extern function void set_scb(rram_ctrl_scoreboard scb);

  // Set that the given field should have its rdata checked in post_predict for reads
  extern function void enable_field_rdata_check(uvm_reg_field fld);

  // A reset has just happened. Clear any entries from m_direct_predictions and m_pending_wdata.
  extern function void on_reset();

  // Make a direct prediction for a register field
  //
  // If the field isn't currently busy, the prediction will be written to the register model. If the
  // field is busy, the prediction will be stored in m_direct_predictions, where it can be seen with
  // get_fld_prediction().
  extern function void make_direct_prediction(uvm_reg_field fld, uvm_reg_data_t value);

  // Get the best prediction of the field's current value, taking direct predictions into account.
  extern function uvm_reg_data_t get_fld_prediction(uvm_reg_field fld);

  // Get the best prediction of the register's current value (building this from calls to
  // get_fld_prediction for the fields in the register)
  extern function uvm_reg_data_t get_reg_prediction(uvm_reg register);

  // Standard function from uvm_reg_cbs
  extern function void post_predict(input uvm_reg_field  fld,
                                    input uvm_reg_data_t previous,
                                    inout uvm_reg_data_t value,
                                    input uvm_predict_e  kind,
                                    input uvm_path_e     path,
                                    input uvm_reg_map    map);

  // Standard task from uvm_reg_cbs
  extern task pre_write(uvm_reg_item rw);
endclass

function rram_ctrl_reg_cbs::new(string name="");
  super.new(name);
endfunction

function void rram_ctrl_reg_cbs::set_scb(rram_ctrl_scoreboard scb);
  m_scb = scb;
endfunction

function void rram_ctrl_reg_cbs::enable_field_rdata_check(uvm_reg_field fld);
  m_fields_to_check[fld] = 1;
endfunction

function void rram_ctrl_reg_cbs::on_reset();
  m_direct_predictions.delete();
  m_pending_wdata.delete();
endfunction

function void rram_ctrl_reg_cbs::make_direct_prediction(uvm_reg_field fld, uvm_reg_data_t value);
  if (!fld.get_parent().is_busy()) begin
    // If the field's parent register isn't busy, we can make a direct prediction of the field's
    // value.
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
  // This is basically a clone of uvm_reg::get_mirrored_value, but using get_fld_prediction instead
  // of getting the fields' mirrored values.
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
  import prim_mubi_pkg::MuBi4False;

  bit            has_pending_wdata;
  uvm_reg_data_t wdata;

  bit            has_direct_pred;
  uvm_reg_data_t direct_pred;
  uvm_reg_data_t best_old_pred;

  if (m_scb == null) begin
    `uvm_fatal("no_scb", "No handle to a scoreboard.")
  end

  // If this is a write access that came from some_reg.write(), there should be a corresponding
  // value in m_pending_wdata. Pop that value into a wdata variable and set has_pending_wdata.
  //
  // There might not be any such data if the write access was driven more directly (by calling
  // tl_access) or if we are just observing the block in passive mode.
  if (kind == UVM_PREDICT_WRITE) begin
    if (m_pending_wdata.exists(fld)) begin
      has_pending_wdata = 1;
      wdata = m_pending_wdata[fld];
      m_pending_wdata.delete(fld);
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

  // Track writes to DIS.SW_DIS.
  //
  // If a write causes RRAM to be disabled (because the previous version of the field was MuBi4False
  // and the new value is not) then tell the scoreboard about it. This allows the scoreboard to
  // start a short window where the disable status of RRAM isn't known.
  if (kind == UVM_PREDICT_WRITE && fld.get_full_name() == "dis.sw_dis") begin
    // This is a write to DIS.SW_DIS. Is it disabling RRAM? If so, tell the scoreboard about it.
    if (previous == MuBi4False && value != MuBi4False) begin
      m_scb.on_dis_sw_write_true();
    end
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
      // pre_write and is now in the wdata variable).

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
          // inferred from the wdata.
        end

        "W1C": begin
          // The correct prediction might be different if we have written zero (which doesn't clear
          // any bits) and best_old_pred has fewer bits set than the register model prediction.
          //
          // Of course, this only works if we know what value was written, which depends on this
          // having been an access through uvm_reg::do_write(). If not, we're kind of stuck. We
          // don't expect this to happen though, because this would need the write to overlap with
          // accesses through the register frontdoor to cause the register to be busy. If it
          // happens, raise an error and ignore the direct prediction.
          if (has_pending_wdata) begin
            value = best_old_pred & ~wdata;
          end else if (has_direct_pred) begin
            `uvm_error("no_wdata",
                       $sformatf({"Access to %0s that didn't come through uvm_reg::do_write has ",
                                  "just finished. It overlapped with something that did."},
                                 fld.get_full_name()))
          end
        end

        "W0C": begin
          // The correct prediction might be different if we have written '1 (which doesn't clear
          // any bits) and best_old_pred has fewer bits set than the register model prediction.
          //
          // As with the W1C case, fail with an error if there is no pending wdata.
          if (has_pending_wdata) begin
            value = best_old_pred & wdata;
          end else if (has_direct_pred) begin
            `uvm_error("no_wdata",
                       $sformatf({"Access to %0s that didn't come through uvm_reg::do_write has ",
                                  "just finished. It overlapped with something that did."},
                                 fld.get_full_name()))
          end
        end

        default: begin
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

  if (!$cast(fld, rw.element)) begin
    `uvm_fatal("not_field",
               $sformatf({"pre_write called for item %0s, which isn't a field. ",
                          "These cbs should only be attached to fields."},
                         rw.element.get_name()))
  end

  m_pending_wdata[fld] = rw.value[0];
endtask
