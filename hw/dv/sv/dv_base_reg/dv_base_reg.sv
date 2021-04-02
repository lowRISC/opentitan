// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// base register class which will be used to generate the reg
class dv_base_reg extends uvm_reg;
  // external reg doesn't have storage in reg module, which may connect to some combinational logic
  // hence, backdoor write isn't available
  local bit is_ext_reg;

  local uvm_reg_data_t staged_shadow_val, committed_val, shadowed_val;
  local bit            is_shadowed;
  local bit            shadow_wr_staged; // stage the first shadow reg write
  local bit            shadow_update_err;
  local bit            en_shadow_wr = 1;
  // In certain shadow reg (e.g. in AES), fatal error can lock write access
  local bit            shadow_fatal_lock;
  local string         update_err_alert_name;
  local string         storage_err_alert_name;

  // atomic_shadow_wr: semaphore to guarantee atomicity of the two writes for shadowed registers.
  // In case a parallel thread writing a different value to the same reg causing an update_err
  semaphore            atomic_shadow_wr;

  // atomic_en_shadow_wr: semaphore to guarantee setting or resetting en_shadow_wr is unchanged
  // through the 1st/2nd (or both) writes
  semaphore            atomic_en_shadow_wr;

  function new(string       name = "",
               int unsigned n_bits,
               int          has_coverage);
    super.new(name, n_bits, has_coverage);
    atomic_en_shadow_wr = new(1);
    atomic_shadow_wr    = new(1);
  endfunction : new

  function void get_dv_base_reg_fields(ref dv_base_reg_field dv_fields[$]);
    foreach (m_fields[i]) `downcast(dv_fields[i], m_fields[i])
  endfunction

  // get_n_bits will return number of all the bits in the csr
  // while this function will return actual number of bits used in reg field
  function uint get_n_used_bits();
    foreach (m_fields[i]) get_n_used_bits += m_fields[i].get_n_bits();
  endfunction

  // loop all the fields to find the msb position of this reg
  function uint get_msb_pos();
    foreach (m_fields[i]) begin
      uint field_msb_pos = m_fields[i].get_lsb_pos() + m_fields[i].get_n_bits() - 1;
      if (field_msb_pos > get_msb_pos) get_msb_pos = field_msb_pos;
    end
  endfunction

  virtual function dv_base_reg_field get_dv_base_reg_field_by_name(string fld_name,
                                                                   bit check_fld_exist = 1'b1);
    uvm_reg_field fld = get_field_by_name(fld_name);
    dv_base_reg_field dv_fld;

    `downcast(dv_fld, fld)
    if (check_fld_exist) begin
      `DV_CHECK_NE_FATAL(dv_fld, null,
                         $sformatf("%0s does not exist in reg %0s", fld_name, get_full_name()))
    end
    return dv_fld;
  endfunction

  // this function can only be called when this reg is intr_state reg
  // Example: ral.intr_state.get_intr_pins_exp_value(). And it returns value of
  // intr_state & intr_enable, which represents value of interrupt pins
  virtual function uvm_reg_data_t get_intr_pins_exp_value();
    uvm_reg_block blk = get_parent();
    uvm_reg       intr_enable_csr;
    string        intr_enable_csr_name;
    bit           is_intr_state_csr = !(uvm_re_match("intr_state*", get_name()));

    `DV_CHECK_EQ_FATAL(is_intr_state_csr, 1)

    // intr_enable and intr_state have the same suffix
    intr_enable_csr_name = str_utils_pkg::str_replace(get_name(), "state", "enable");

    intr_enable_csr = blk.get_reg_by_name(intr_enable_csr_name);

    // some interrupts may not have intr_enable
    if (intr_enable_csr != null) begin
      return get_mirrored_value() & intr_enable_csr.get_mirrored_value();
    end else begin
      return get_mirrored_value();
    end
  endfunction

  // Wen reg/fld can lock specific groups of fields' write acces. The lockable fields are called
  // lockable flds.
  function void add_lockable_reg_or_fld(uvm_object lockable_obj);
    dv_base_reg_field wen_fld;
    `DV_CHECK_FATAL(m_fields.size(), 1, "This register has more than one field.\
                    Please use register field's add_lockable_reg_or_fld() method instead.")
    `downcast(wen_fld, m_fields[0])
    wen_fld.add_lockable_reg_or_fld(lockable_obj);
  endfunction

  // Returns true if this register/field can lock the specified register/field, else return false.
  function bit locks_reg_or_fld(uvm_object obj);
    dv_base_reg_field wen_fld;
    `DV_CHECK_FATAL(m_fields.size(), 1, "This register has more than one field.\
                    Please use register field's locks_reg_or_fld() method instead.")
    `downcast(wen_fld, m_fields[0])
    return wen_fld.locks_reg_or_fld(obj);
  endfunction

  // Even though user can add lockable register or field via `add_lockable_reg_or_fld` method, the
  // get_lockable_flds function will always return a queue of lockable fields.
  function void get_lockable_flds(ref dv_base_reg_field lockable_flds_q[$]);
    dv_base_reg_field wen_fld;
    `DV_CHECK_FATAL(m_fields.size(), 1, "This register has more than one field.\
                    Please use register field's get_lockable_flds() method instead.")
    `downcast(wen_fld, m_fields[0])
    wen_fld.get_lockable_flds(lockable_flds_q);
  endfunction

  // The register is a write enable register (wen_reg) if its fields are wen_flds.
  function bit is_wen_reg();
    foreach (m_fields[i]) begin
      dv_base_reg_field fld;
      `downcast(fld, m_fields[i])
      if (fld.is_wen_fld()) return 1;
    end
    return 0;
  endfunction

  function bit is_staged();
     return shadow_wr_staged;
  endfunction

  // is_shadowed bit is only one-time programmable
  // once this function is called in RAL auto-generated class, it cannot be changed
  function void set_is_shadowed();
    is_shadowed = 1;
  endfunction

  function uvm_reg_data_t get_staged_shadow_val();
    return staged_shadow_val;
  endfunction

  function void set_en_shadow_wr(bit val);
    // do not update en_shadow_wr if shadow register write is in process
    if ((en_shadow_wr ^ val) && shadow_wr_staged) begin
      `uvm_info(`gfn,
          $sformatf("unable to %0s en_shadow_wr because register already completed first write",
          val ? "set" : "clear"), UVM_HIGH)
      return;
    end
    en_shadow_wr = val;
  endfunction

  function bit get_is_shadowed();
    return is_shadowed;
  endfunction

  function bit get_shadow_update_err();
    return shadow_update_err;
  endfunction

  function bit get_shadow_storage_err();
    uvm_reg_data_t mask = (1'b1 << (get_msb_pos() + 1)) - 1;
    uvm_reg_data_t shadowed_val_temp = (~shadowed_val) & mask;
    uvm_reg_data_t committed_val_temp = committed_val & mask;
    `uvm_info(`gfn, $sformatf("shadow_val %0h, commmit_val %0h", shadowed_val_temp,
                              committed_val_temp), UVM_DEBUG)
    return shadowed_val_temp != committed_val_temp;
  endfunction

  virtual function void clear_shadow_update_err();
    shadow_update_err = 0;
  endfunction

  // post_write callback to handle special regs:
  // - shadow register: shadow reg won't be updated until the second write has no error
  // - lock register: if wen_fld is set to 0, change access policy to all the lockable_flds
  // TODO: create an `enable_field_access_policy` variable and set the template code during
  // automation.
  virtual task post_write(uvm_reg_item rw);
    dv_base_reg_field fields[$];

    // no need to update shadow value or access type if access is not OK, as access is aborted
    if (rw.status != UVM_IS_OK) return;

    if (is_shadowed && !shadow_fatal_lock) begin
      // first write
      if (!shadow_wr_staged) begin
        shadow_wr_staged = 1;
        // rw.value is a dynamic array
        staged_shadow_val = rw.value[0];
        return;
      end begin
        // second write
        shadow_wr_staged = 0;
        if (staged_shadow_val != rw.value[0]) begin
          shadow_update_err = 1;
          return;
        end
        committed_val = staged_shadow_val;
        shadowed_val  = ~committed_val;
      end
    end
    lock_lockable_flds(rw.value[0]);
  endtask

  // shadow register read will clear its phase tracker
  virtual task post_read(uvm_reg_item rw);
    if (is_shadowed) shadow_wr_staged = 0;
  endtask

  virtual function void set_is_ext_reg(bit is_ext);
    is_ext_reg = is_ext;
  endfunction

  virtual function bit get_is_ext_reg();
    return is_ext_reg;
  endfunction

  // if it is a shadowed register, and is enabled to write it twice, this task will write the
  // register twice with the same value and address.
  virtual task write(output uvm_status_e     status,
                     input uvm_reg_data_t    value,
                     input uvm_path_e        path = UVM_DEFAULT_PATH,
                     input uvm_reg_map       map = null,
                     input uvm_sequence_base parent=null,
                     input int               prior = -1,
                     input uvm_object        extension = null,
                     input string            fname = "",
                     input int               lineno = 0);
    if (is_shadowed) atomic_shadow_wr.get(1);
    super.write(status, value, path, map, parent, prior, extension, fname, lineno);
    if (is_shadowed && en_shadow_wr) begin
      super.write(status, value, path, map, parent, prior, extension, fname, lineno);
    end
    if (is_shadowed) atomic_shadow_wr.put(1);
  endtask

  // Override do_predict function to support shadow_reg.
  // Skip predict in one of the following conditions:
  // 1). It is shadow_reg's first write.
  // 2). It is shadow_reg's second write with an update_err.
  // 2). The shadow_reg is locked due to fatal storage error and it is not a backdoor write.

  virtual function void do_predict(uvm_reg_item      rw,
                                   uvm_predict_e     kind = UVM_PREDICT_DIRECT,
                                   uvm_reg_byte_en_t be = -1);
    if (is_shadowed && kind != UVM_PREDICT_READ && (shadow_wr_staged || shadow_update_err ||
        (shadow_fatal_lock && rw.path != UVM_BACKDOOR))) begin
      `uvm_info(`gfn, $sformatf(
          "skip predict %s: due to shadow_reg_first_wr=%0b, update_err=%0b, shadow_fatal_lock=%0b",
          get_name(), shadow_wr_staged, shadow_update_err, shadow_fatal_lock), UVM_HIGH)
      return;
    end
    super.do_predict(rw, kind, be);
  endfunction

  // This function is used for wen_reg to lock its lockable flds by changing the lockable flds'
  // access policy. For register write via csr_wr(), this function is included in post_write().
  // For register write via tl_access(), user will need to call this function manually.
  virtual function void lock_lockable_flds(uvm_reg_data_t val);
    if (is_wen_reg()) begin
      foreach (m_fields[i]) begin
        dv_base_reg_field fld;
        `downcast(fld, m_fields[i])
        if (fld.is_wen_fld()) begin
          uvm_reg_data_t field_val = val & fld.get_field_mask();
          string field_access = fld.get_access();
          case (field_access)
            // discussed in issue #1922: enable register is standarized to W0C or RO (if HW has
            // write access).
            "W0C": if (field_val == 1'b0) fld.set_lockable_flds_access(1);
            "RO": ; // if RO, it's updated by design, need to predict in scb
            default:`uvm_fatal(`gfn, $sformatf("lock register invalid access %s", field_access))
          endcase
        end
      end
    end
  endfunction

  virtual task poke(output uvm_status_e     status,
                    input  uvm_reg_data_t   value,
                    input string            kind = "BkdrRegPathRtl",
                    input uvm_sequence_base parent = null,
                    input uvm_object        extension = null,
                    input string            fname = "",
                    input int               lineno = 0);
    if (kind == "BkdrRegPathRtlShadow") shadowed_val = value;
    else if (kind == "BkdrRegPathRtlCommitted") committed_val = value;

    super.poke(status, value, kind, parent, extension, fname, lineno);
  endtask

  // Callback function to update shadowed values according to specific design.
  // Should only be called after post-write.
  // If a shadow reg is locked due to fatal error, this function will return without updates
  virtual function void update_shadowed_val(uvm_reg_data_t val, bit do_predict = 1);
    if (shadow_fatal_lock) return;
    if (shadow_wr_staged) begin
      // update value after first write
      staged_shadow_val = val;
    end else begin
      // update value after second write
      if (staged_shadow_val != val) begin
        shadow_update_err = 1;
      end else begin
        shadow_update_err = 0;
        committed_val     = staged_shadow_val;
        shadowed_val      = ~committed_val;
      end
    end
    if (do_predict) void'(predict(val));
  endfunction

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    if (is_shadowed) begin
      shadow_update_err = 0;
      shadow_wr_staged  = 0;
      shadow_fatal_lock = 0;
      committed_val     = get_mirrored_value();
      shadowed_val      = ~committed_val;
      // in case reset is issued during shadowed writes
      void'(atomic_shadow_wr.try_get(1));
      void'(atomic_en_shadow_wr.try_get(1));
      atomic_shadow_wr.put(1);
      atomic_en_shadow_wr.put(1);
    end
  endfunction

  function void add_update_err_alert(string name);
    if (update_err_alert_name == "") update_err_alert_name = name;
  endfunction

  function void add_storage_err_alert(string name);
    if (storage_err_alert_name == "") storage_err_alert_name = name;
  endfunction

  function string get_update_err_alert_name();
    string parent_name = this.get_parent().get_name();

    // block level alert name is input alert name from hjson
    if (get_parent().get_parent() == null) return update_err_alert_name;

    // top-level alert name is ${block_name} + alert name from hjson
    return ($sformatf("%0s_%0s", parent_name, update_err_alert_name));
  endfunction

  function void lock_shadow_reg();
    shadow_fatal_lock = 1;
  endfunction

  function bit shadow_reg_is_locked();
    return shadow_fatal_lock;
  endfunction

  function string get_storage_err_alert_name();
    string parent_name = this.get_parent().get_name();

    // block level alert name is input alert name from hjson
    if (get_parent().get_parent() == null) return storage_err_alert_name;

    // top-level alert name is ${block_name} + alert name from hjson
    return ($sformatf("%0s_%0s", parent_name, storage_err_alert_name));
  endfunction

endclass
