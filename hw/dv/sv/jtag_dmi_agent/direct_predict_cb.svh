// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class direct_predict_cb extends uvm_reg_cbs;

  // An associative array of direct predictions, keyed by register fields
  //
  // These predictions are generated when something happens that allows us to predict the value of
  // some field when there is a register operation already trying to access the field's register.
  // For an extreme example, many register operations might have been queued up.
  //
  // When an operation completes on the register, there is a call-back associated with the
  // read/write prediction that ensues and we can update the predictions for the register's fields
  // as a result.
  local uvm_reg_data_t m_direct_predictions[uvm_reg_field];

  // An associative array of write data, keyed by register fields.
  //
  // This is updated by the pre-write callback when the field is about to be written. This is useful
  // because it will happen before the post_predict callback gets called after there is a follow-up
  // UVM_PREDICT_WRITE prediction when the write is finished. Here, we have stored the value that is
  // being written to the field.
  local uvm_reg_data_t m_wdata[uvm_reg_field];

  extern function new(string name = "");

  // Called when the block resets, so any state in this class should be cleared.
  extern function void on_reset();

  // Make a direct prediction for a field. If that field is not currently busy, this immediately
  // uses the field's predict() function. If the field *is* busy, this writes the prediction to
  // m_direct_predictions.
  extern function void make_direct_prediction(uvm_reg_field fld, uvm_reg_data_t value);

  // Get the best prediction for a field's current value, returning the most recent direct
  // prediction if there is one, or the mirrored value otherwise.
  extern function uvm_reg_data_t get_prediction(uvm_reg_field fld);

  // A function from uvm_reg_cbs, called before a field, register or memory is about to be written.
  extern task pre_write(uvm_reg_item rw);

  // A function from uvm_reg_cbs, called as part of predicting a field after a read or write.
  extern function void post_predict(input uvm_reg_field  fld,
                                    input uvm_reg_data_t previous,
                                    inout uvm_reg_data_t value,
                                    input uvm_predict_e  kind,
                                    input uvm_path_e     path,
                                    input uvm_reg_map    map);

  // Get the wdata for the most recent write that has been seen for this field.
  //
  // If there is no such write, generate a uvm_error and then return zero.
  extern local function uvm_reg_data_t get_last_wdata(uvm_reg_field fld);
endclass

function direct_predict_cb::new(string name = "");
  super.new(name);
endfunction

function void direct_predict_cb::on_reset();
  m_direct_predictions.delete();
  m_wdata.delete();
endfunction

function void direct_predict_cb::make_direct_prediction(uvm_reg_field  fld,
                                                        uvm_reg_data_t value);
  if (fld.get_parent().is_busy()) begin
    `uvm_info("direct_predict",
              $sformatf("Making direct prediction for busy field %0s with value 0x%0h",
                        fld.get_full_name(), value),
              UVM_HIGH)

    m_direct_predictions[fld] = value;
  end else begin
    if (!fld.predict(value)) begin
      `uvm_fatal("no_direct_predict",
                 $sformatf("Failed to predict value of %0s.", fld.get_name()))
    end
  end
endfunction

function uvm_reg_data_t direct_predict_cb::get_prediction(uvm_reg_field fld);
  if (m_direct_predictions.exists(fld)) begin
    `uvm_info("direct_predict",
              $sformatf("Retrieving direct prediction for busy field %0s as value 0x%0h",
                        fld.get_full_name(), m_direct_predictions[fld]),
              UVM_HIGH)

    return m_direct_predictions[fld];
  end else begin
    return fld.get_mirrored_value();
  end
endfunction

task direct_predict_cb::pre_write(uvm_reg_item rw);
  uvm_reg_field fld;

  // The pre-write callback gets called for both fields and registers. Ignore the register-wide
  // version: we just want to grab fields.
  if (!$cast(fld, rw.element)) return;

  // Otherwise, grab the value that is being written by updating the "value" array to point at it
  // and then storing the first element of wdata.
  m_wdata[fld] = rw.value[0];

  `uvm_info("direct_predict_cb::pre_write",
            $sformatf("Storing wdata of 0x%0h for write to field %0s.",
                      m_wdata[fld], fld.get_full_name()),
            UVM_HIGH)
endtask

function void direct_predict_cb::post_predict(input uvm_reg_field  fld,
                                              input uvm_reg_data_t previous,
                                              inout uvm_reg_data_t value,
                                              input uvm_predict_e  kind,
                                              input uvm_path_e     path,
                                              input uvm_reg_map    map);
  uvm_reg_data_t prediction;

  // If we don't have any direct predictions for the field, there's nothing to do
  if (!m_direct_predictions.exists(fld)) return;

  prediction = m_direct_predictions[fld];
  m_direct_predictions.delete(fld);

  `uvm_info("direct_predict_cb::post_predict",
            $sformatf({"Applying direct prediction made for field %0s, ",
                       "which had value 0x%0h when the existing prediction updated a value of ",
                       "0x%0h to 0x%0h."},
                      fld.get_full_name(), prediction, previous, value),
            UVM_HIGH)

  case (kind)
    UVM_PREDICT_READ: begin
      // If we have just read the field, that trumps any value that we might have thought we were
      // predicting: we've just read the value!
    end

    UVM_PREDICT_WRITE: begin
      // If we have just written to the field, the correct new prediction depends on the field's
      // m_access.
      case (fld.get_access())
        "RO", "RC", "RS": begin
          // The field ignores writes, so it doesn't really matter what value was being written. We
          // know the value the field should really have.
          value = prediction;
        end

        "RW", "WC", "WS", "WRC", "WRS", "WSRC", "WCRS", "WO", "WOC", "WOS": begin
          // The field is writable, so our prediction doesn't really matter. The write that has just
          // completed will win.
        end

        "W1C", "W1CRS": begin
          // We can get the value that was just written by calling get_last_wdata and should update
          // value to be prediction after clearing the bits that were set in wdata.
          value = prediction & ~get_last_wdata(fld);
        end

        "W1S", "W1SRC": begin
          // We can get the value that was just written by calling get_last_wdata and should update
          // value to be prediction after setting the bits that were set in wdata.
          value = prediction | get_last_wdata(fld);
        end

        "W1T": begin
          // We can get the value that was just written by calling get_last_wdata and should update
          // value to be prediction after flipping the bits that were set in wdata.
          value = prediction ^ get_last_wdata(fld);
        end

        "W0C", "W0CRS": begin
          // We can get the value that was just written by calling get_last_wdata and should update
          // value to be prediction after clearing the bits that were clear in wdata.
          value = prediction & get_last_wdata(fld);
        end

        "W0S", "W0SRC": begin
          // We can get the value that was just written by calling get_last_wdata and should update
          // value to be prediction after setting the bits that were clear in wdata.
          value = prediction | ~get_last_wdata(fld);
        end

        "W0T": begin
          // We can get the value that was just written by calling get_last_wdata and should update
          // value to be prediction after flipping the bits that were clear in wdata.
          value = prediction ^ ~get_last_wdata(fld);
        end

        default: begin
          `uvm_error("unknown_access_type",
                     $sformatf({"Cannot override a prediction for the field %0s, ",
                                "which has access %0s"},
                               fld.get_full_name(), fld.get_access()))
        end
      endcase
    end
    default: begin
      `uvm_error("unknown_predict_type",
                 $sformatf("post_predict doesn't expect kind='%0s' (%0d).",
                           kind.name(), kind))
    end
  endcase
endfunction

function uvm_reg_data_t direct_predict_cb::get_last_wdata(uvm_reg_field fld);
  if (!m_wdata.exists(fld)) begin
    `uvm_error("no_wdata",
               $sformatf("Cannot find the most recent write to field %0s. Returning wdata=0.",
                         fld.get_full_name()))
    return 0;
  end

  return m_wdata[fld];
endfunction
