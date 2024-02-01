// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// base register class which will be used to generate the reg
class dv_base_reg extends uvm_reg;
  // external reg doesn't have storage in reg module, which may connect to some combinational logic
  // hence, backdoor write isn't available
  local bit is_ext_reg;

  local bit            is_shadowed;
  local bit            shadow_wr_staged; // stage the first shadow reg write
  local bit            shadow_update_err;
  local bit            backdoor_write_shadow_val; // flag to avoid predict `shadow_wr_staged`
  // Update internal shadow committed and shadowed values when register access is not `RW`.
  local bit            do_update_shadow_vals;
  // In certain shadow reg (e.g. in AES), fatal error can lock write access.
  local bit            shadow_fatal_lock;
  local string         update_err_alert_name;
  local string         storage_err_alert_name;

  // This is used for get_alias_name
  string alias_name = "";
  // Lookup table for alias fields (used for get_field_by_name)
  string field_alias_lookup[string];

  // atomic_en_shadow_wr: semaphore to guarantee setting or resetting en_shadow_wr is unchanged
  // through the 1st/2nd (or both) writes
  semaphore            atomic_en_shadow_wr;

  function new(string       name = "",
               int unsigned n_bits,
               int          has_coverage);
    super.new(name, n_bits, has_coverage);
    atomic_en_shadow_wr = new(1);
  endfunction : new

  // Create this register and its fields' IP-specific functional coverage.
  function void create_cov();
    dv_base_reg_field fields[$];
    get_dv_base_reg_fields(fields);
    foreach(fields[i]) fields[i].create_cov();
    // Create register-specific covergroups here.
  endfunction

  // this is similar to get_name, but it gets the
  // simple name of the aliased register instead.
  function string get_alias_name ();
    return this.alias_name;
  endfunction: get_alias_name

  // this is similar to set_name, but it sets the
  // simple name of the aliased register instead.
  function void set_alias_name (string alias_name);
    dv_base_reg_block reg_block;
    `downcast(reg_block, get_parent())
    reg_block.register_alias_lookup[alias_name] = this.get_name();
    this.alias_name = alias_name;
  endfunction: set_alias_name

  function void get_dv_base_reg_fields(ref dv_base_reg_field dv_fields[$]);
    foreach (m_fields[i]) `downcast(dv_fields[i], m_fields[i])
  endfunction

  function dv_base_reg_block get_dv_base_reg_block();
    `downcast(get_dv_base_reg_block, get_parent())
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

  // Return a mask of valid bits in the register.
  virtual function uvm_reg_data_t get_reg_mask();
    dv_base_reg_field flds[$];
    this.get_dv_base_reg_fields(flds);
    foreach (flds[i]) begin
      get_reg_mask |= flds[i].get_field_mask();
    end
  endfunction

  // Return a mask of read-only bits in the register.
  virtual function uvm_reg_data_t get_ro_mask();
    dv_base_reg_field flds[$];
    this.get_dv_base_reg_fields(flds);
    foreach (flds[i]) begin
      get_ro_mask |= flds[i].get_ro_mask();
    end
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

  // A helper function for shadow register or field read to clear the `shadow_wr_staged` flag.
  virtual function void clear_shadow_wr_staged();
    if (is_shadowed) begin
      if (shadow_wr_staged) `uvm_info(`gfn, "clear shadow_wr_staged", UVM_HIGH)
      shadow_wr_staged = 0;
      clear_shadow_update_err();
    end
  endfunction

  function bit get_is_shadowed();
    return is_shadowed;
  endfunction

  function bit get_shadow_update_err();
    return shadow_update_err;
  endfunction

  function bit get_shadow_storage_err();
    dv_base_reg_field flds[$];
    this.get_dv_base_reg_fields(flds);
    foreach (flds[i]) begin
      get_shadow_storage_err |= flds[i].get_shadow_storage_err();
    end
  endfunction

  virtual function void clear_shadow_update_err();
    shadow_update_err = 0;
  endfunction

  // do_predict callback to handle special regs. This function doesn't update mirror values, but
  // update local variables used for the special regs.
  // - shadow register: shadow reg won't be updated until the second write has no error
  // - lock register: if wen_fld is set to 0, change access policy to all the lockable_flds
  virtual function void pre_do_predict(uvm_reg_item rw, uvm_predict_e kind);

    // Skip updating shadow value or access type if:
    // 1). Access is not OK, as access is aborted.
    // 2). The operation is not write.
    // 3). The update is triggered by backdoor poke.
    if (rw.status != UVM_IS_OK || kind != UVM_PREDICT_WRITE || backdoor_write_shadow_val) return;

    if (is_shadowed && !shadow_fatal_lock) begin
      dv_base_reg_field flds[$];
      this.get_dv_base_reg_fields(flds);

      foreach (flds[i]) begin
        // `rw.value` is a dynamic array.
        uvm_reg_data_t wr_data = get_field_val(flds[i], rw.value[0]);

        // Skip updating shadow value or access type for this field if:
        // 1). A storage error is triggered, which means the field is locked to error status.
        // 2). The register is "RO". This condition is used to cover enable register locks shadowed
        // register's write access.
        if (flds[i].get_shadow_storage_err() || flds[i].get_access() == "RO") continue;

        // first write
        if (!shadow_wr_staged) begin
          flds[i].update_staged_val(wr_data);
          continue;
        end begin
          // second write
          if (flds[i].get_staged_val() == wr_data) begin
             flds[i].update_committed_val(wr_data);
             flds[i].update_shadowed_val(~wr_data);
          end else begin
            shadow_update_err = 1;
            flds[i].sample_shadow_field_cov(.update_err(1));
          end
        end
      end
      if (!shadow_wr_staged) shadow_wr_staged = 1;
      else shadow_wr_staged = 0;

      // Update committed and shadowed values if the field access is not "RW".
      // Used for register with special access policy such as `RW1S`.
      if (!shadow_wr_staged && flds[0].get_access() != "RW") do_update_shadow_vals = 1;
    end
  endfunction

  // shadow register read will clear its phase tracker
  virtual task post_read(uvm_reg_item rw);
    if (rw.status == UVM_IS_OK) clear_shadow_wr_staged();
  endtask

  virtual function void set_is_ext_reg(bit is_ext);
    is_ext_reg = is_ext;
  endfunction

  virtual function bit get_is_ext_reg();
    return is_ext_reg;
  endfunction

  // Override do_predict function to support shadow_reg.
  // Skip predict in one of the following conditions:
  // 1). It is shadow_reg's first write.
  // 2). The shadow_reg is locked due to fatal storage error and it is not a backdoor write.
  // Note that if shadow_register write has update error, we only update the value with correct
  // fields.
  virtual function void do_predict(uvm_reg_item      rw,
                                   uvm_predict_e     kind = UVM_PREDICT_DIRECT,
                                   uvm_reg_byte_en_t be = -1);
    pre_do_predict(rw, kind);
    if (is_shadowed && kind != UVM_PREDICT_READ) begin
      if (shadow_wr_staged || (shadow_fatal_lock && rw.path != UVM_BACKDOOR)) begin
        `uvm_info(`gfn, $sformatf(
            "skip predict %s: due to shadow_reg_first_wr=%0b, shadow_fatal_lock=%0b",
            get_name(), shadow_wr_staged, shadow_fatal_lock), UVM_HIGH)
        return;
      end else begin
        `uvm_info(`gfn, $sformatf(
            "Update shadow reg %0s rw.value from %0h to %0h",
            get_name(), rw.value[0], get_committed_val()), UVM_HIGH)
        rw.value[0] = get_committed_val();
      end
    end
    super.do_predict(rw, kind, be);

    // For register with special access policies, update committed and shadowed value again with
    // the actual predicted value.
    if (do_update_shadow_vals) begin
      dv_base_reg_field flds[$];
      this.get_dv_base_reg_fields(flds);
      foreach (flds[i]) begin
        if (!flds[i].get_shadow_storage_err()) begin
          flds[i].update_committed_val(`gmv(flds[i]));
          flds[i].update_shadowed_val(~`gmv(flds[i]));
        end
      end
      do_update_shadow_vals = 0;
    end
    lock_lockable_flds(rw.value[0], kind);
  endfunction

  // This function is used for wen_reg to lock its lockable flds by changing the lockable flds'
  // access policy. For register write via csr_wr(), this function is included in post_write().
  // For register write via tl_access(), user will need to call this function manually.
  virtual function void lock_lockable_flds(uvm_reg_data_t val, uvm_predict_e kind);
    if (is_wen_reg()) begin
      `uvm_info(`gfn, $sformatf("lock_lockable_flds %d val", val), UVM_LOW);
      foreach (m_fields[i]) begin
        dv_base_reg_field fld;
        `downcast(fld, m_fields[i])
        if (fld.is_wen_fld()) begin
          uvm_reg_data_t field_val = val & fld.get_field_mask();
          string field_access = fld.get_access();
          case (field_access)
            // discussed in issue #1922: enable register is standarized to W0C or RO (if HW has
            // write access).
            "W0C": begin
              // This is the regular behavior with W0C access policy enabled (i.e., only
              // clearing is possible).
              if (kind == UVM_PREDICT_WRITE && field_val == 1'b0) begin
                fld.set_lockable_flds_access(1);
              // In this case we are using direct prediction where the access policy is not
              // applied. I.e., a regwen bit that has been set to 0 can be set to 1 again.
              end else if (kind == UVM_PREDICT_DIRECT) begin
                fld.set_lockable_flds_access((~field_val) & fld.get_field_mask());
              end
            end
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

    dv_base_reg_field flds[$];
    this.get_dv_base_reg_fields(flds);
    foreach (flds[i]) begin
      if (kind == "BkdrRegPathRtlShadow") begin
        flds[i].update_shadowed_val(get_field_val(flds[i], value));
        backdoor_write_shadow_val = 1;
      end else if (kind == "BkdrRegPathRtl") begin
        flds[i].update_committed_val(get_field_val(flds[i], value));
        backdoor_write_shadow_val = 1;
      end
    end
    super.poke(status, value, kind, parent, extension, fname, lineno);
    backdoor_write_shadow_val = 0;
  endtask

  virtual function uvm_reg_data_t get_committed_val();
    dv_base_reg_field flds[$];
    this.get_dv_base_reg_fields(flds);
    foreach (flds[i]) begin
      get_committed_val |= flds[i].get_committed_val() << flds[i].get_lsb_pos();
    end
  endfunction

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    if (is_shadowed) begin
      shadow_update_err = 0;
      shadow_wr_staged  = 0;
      shadow_fatal_lock = 0;
      // in case reset is issued during shadowed writes
      void'(atomic_en_shadow_wr.try_get(1));
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
    // block level alert name is input alert name from hjson
    if (get_parent().get_parent() == null) return update_err_alert_name;

    // top-level alert name is ${ip_name} + alert name from hjson
    return ($sformatf("%0s_%0s", get_dv_base_reg_block().get_ip_name(), update_err_alert_name));
  endfunction

  function void lock_shadow_reg();
    shadow_fatal_lock = 1;
  endfunction

  function bit shadow_reg_is_locked();
    return shadow_fatal_lock;
  endfunction

  function string get_storage_err_alert_name();
    string ip_name;

    // block level alert name is input alert name from hjson
    if (get_parent().get_parent() == null) return storage_err_alert_name;

    // top-level alert name is ${ip_name} + alert name from hjson
    return ($sformatf("%0s_%0s", get_dv_base_reg_block().get_ip_name(), storage_err_alert_name));
  endfunction

  // this overrides the get_field_by_name function
  function dv_base_reg_field get_field_by_name(string name);
    dv_base_reg_field retval;
    if (field_alias_lookup.exists(name)) begin
      `downcast(retval, super.get_field_by_name(field_alias_lookup[name]))
    end else begin
      `downcast(retval, super.get_field_by_name(name))
    end
    return retval;
  endfunction

endclass
