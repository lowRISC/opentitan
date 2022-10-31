// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// base register reg class which will be used to generate the reg field
class dv_base_reg_field extends uvm_reg_field;
  local string m_original_access;
  local dv_base_reg_field lockable_flds[$];
  local bit is_intr_test_fld;
  local uvm_reg_data_t staged_val, committed_val, shadowed_val;

  // if this is lockable field, here is its corresponding regwen object
  // if not, below 2 object will be null
  local dv_base_reg_field regwen_fld;
  local dv_base_lockable_field_cov lockable_field_cov;

  // This is used for get_field_by_name
  string alias_name = "";

  // Default mubi_width = 0 indicates this register field is not a mubi type.
  protected int mubi_width;

  // variable for mubi coverage, which is only created when this is a mubi reg
  dv_base_mubi_cov mubi_cov;

  // variable for shadowed coverage, which is only created when this is a shadowed reg
  local dv_base_shadowed_field_cov shadowed_cov;

  `uvm_object_utils(dv_base_reg_field)
  `uvm_object_new

  // this is similar to get_name, but it gets the
  // simple name of the aliased field instead.
  function string get_alias_name ();
     return this.alias_name;
  endfunction: get_alias_name

  // this is similar to set_name, but it sets the
  // simple name of the aliased field instead.
  function void set_alias_name (string alias_name);
    dv_base_reg register;
    dv_base_reg_block reg_block;
    `downcast(register, this.get_parent())
    register.field_alias_lookup[alias_name] = this.get_name();
    // We also add the name to the lookup table inside the reg_block to enable get_field_by_name at
    // that level. Note: in order for the get_field_by_name function of dv_base_reg_block to
    // produce meaningful results, all field names within the reg block have to be unique - which
    // cannot always guaranteed. If the fields are not unique at that level, the get_field_by_name
    // of dv_base_reg should be used instead.
    `downcast(reg_block, register.get_parent())
    reg_block.field_alias_lookup[alias_name] = this.get_name();
    this.alias_name = alias_name;
  endfunction: set_alias_name

  // Issue #5105: UVM forces the value member to be non-randomizable for certain access policies.
  // We restore it in this extended class.
  virtual function void configure(uvm_reg        parent,
                                  int unsigned   size,
                                  int unsigned   lsb_pos,
                                  string         access,
                                  bit            volatile,
                                  uvm_reg_data_t reset,
                                  bit            has_reset,
                                  bit            is_rand,
                                  bit            individually_accessible);
      super.configure(.parent   (parent),
                      .size     (size),
                      .lsb_pos  (lsb_pos),
                      .access   (access),
                      .volatile (volatile),
                      .reset    (reset),
                      .has_reset(has_reset),
                      .is_rand  (is_rand),
                      .individually_accessible(individually_accessible));
      value.rand_mode(is_rand);

      is_intr_test_fld = !(uvm_re_match("intr_test*", get_parent().get_name()));
      shadowed_val = ~committed_val;
    endfunction

  virtual function dv_base_reg get_dv_base_reg_parent();
    uvm_reg csr = get_parent();
    `downcast(get_dv_base_reg_parent, csr)
  endfunction

  virtual function void do_predict (uvm_reg_item      rw,
                                    uvm_predict_e     kind = UVM_PREDICT_DIRECT,
                                    uvm_reg_byte_en_t be = -1);
    uvm_reg_data_t field_val = rw.value[0] & ((1 << get_n_bits())-1);

    // update intr_state mirrored value if this is an intr_test reg
    // if kind is UVM_PREDICT_DIRECT or UVM_PREDICT_READ, super.do_predict can handle
    if (kind == UVM_PREDICT_WRITE && is_intr_test_fld) begin
      uvm_reg_field intr_state_fld = get_intr_state_field();
      bit predict_val;
      if (intr_state_fld.get_access == "RO") begin // status interrupt
        predict_val = field_val;
      end else begin // regular W1C interrupt
        `DV_CHECK_STREQ(intr_state_fld.get_access, "W1C")
        predict_val = field_val | `gmv(intr_state_fld);
      end
      // use UVM_PREDICT_READ to avoid uvm_warning due to UVM_PREDICT_DIRECT
      void'(intr_state_fld.predict(predict_val, .kind(UVM_PREDICT_READ)));
    end

    super.do_predict(rw, kind, be);
  endfunction

  // when use UVM_PREDICT_WRITE and the CSR access is WO, this function will return the default
  // val of the register, rather than the written value
  virtual function uvm_reg_data_t XpredictX(uvm_reg_data_t cur_val,
                                            uvm_reg_data_t wr_val,
                                            uvm_reg_map map);

    if (get_access(map) == "WO") return get_reset();
    else return super.XpredictX(cur_val, wr_val, map);
  endfunction

  virtual function string get_original_access();
    return m_original_access;
  endfunction

  virtual function uvm_reg_data_t get_field_mask();
    get_field_mask = (1'b1 << this.get_n_bits()) - 1;
    get_field_mask = get_field_mask << this.get_lsb_pos();
  endfunction

  virtual function void set_original_access(string access);
    if (m_original_access == "") begin
      m_original_access = access;
    end else begin
      `uvm_fatal(`gfn, "register original access can only be written once")
    end
  endfunction

  // Lock the write access to this field.
  // This only pertains to a lockable field. It is invoked in the `set_lockable_flds_access()`
  // method of its corresponding lock (wen) field.
  local function void set_fld_access(bit lock);
    if (lock) void'(this.set_access("RO"));
    else      void'(this.set_access(m_original_access));
  endfunction

  // If input is a reg, add all fields under the reg; if input is a field, add the specific field.
  function void add_lockable_reg_or_fld(uvm_object lockable_obj);
    dv_base_reg_field flds[$];
    uvm_reg_block     ral = this.get_parent().get_parent();
    `DV_CHECK_EQ_FATAL(ral.is_locked(), 0, "RAL is locked, cannot add lockable reg or fld!")
    get_flds_from_uvm_object(lockable_obj, `gfn, flds);
    foreach (flds[i]) begin
      lockable_flds.push_back(flds[i]);
      flds[i].regwen_fld = this;
    end
  endfunction

  function void create_lockable_fld_cov();
    lockable_field_cov = dv_base_lockable_field_cov::type_id::create(`gfn);
  endfunction

  function void create_mubi_cov(int width);
    mubi_cov = dv_base_mubi_cov::type_id::create(`gfn);
    mubi_cov.create_cov(width);
  endfunction

  function void create_shadowed_fld_cov();
    shadowed_cov = dv_base_shadowed_field_cov::type_id::create(`gfn);
  endfunction

  function void create_cov();
    string csr_name = this.get_parent().get_name();
    if (mubi_width > 0)     create_mubi_cov(mubi_width);
    if (regwen_fld != null) create_lockable_fld_cov();
    if (!uvm_re_match("*_shadowed", csr_name)) create_shadowed_fld_cov();
  endfunction

  // Returns true if this field can lock the specified register/field, else return false.
  // If lockable register is partially lockable (only certain field is lockable), this method will
  // still return true.
  function bit locks_reg_or_fld(uvm_object obj);
    dv_base_reg_field flds[$];
    get_flds_from_uvm_object(obj, `gfn, flds);
    foreach (flds[i]) begin
      if (flds[i] inside {lockable_flds}) return 1;
    end
    return 0;
  endfunction

  function bit is_wen_fld();
    return (lockable_flds.size() > 0);
  endfunction

  // If lock is set to 1, lockable fields access policy will be set to RO access.
  // If lock resets to 0, lockable fields will be set back to their original accesses.
  function void set_lockable_flds_access(bit lock);
    foreach (lockable_flds[i]) lockable_flds[i].set_fld_access(lock);
  endfunction

  function void get_lockable_flds(ref dv_base_reg_field lockable_flds_q[$]);
    lockable_flds_q = lockable_flds;
  endfunction

  // Return if the RAL block is locked or not.
  function bit is_locked();
    uvm_reg_block blk = this.get_parent().get_parent();
    return blk.is_locked();
  endfunction

  // If the register field is a mubi type, set the mubi width before the RAL is locked.
  function void set_mubi_width(int width);
    if (is_locked()) `uvm_fatal(`gfn, "Cannot set mubi width when the block is locked")
    mubi_width = width;
  endfunction

  function int get_mubi_width();
    return mubi_width;
  endfunction

  // shadow register field read will clear its phase tracker
  virtual task post_read(uvm_reg_item rw);
    if (rw.status == UVM_IS_OK) begin
      dv_base_reg parent_csr = get_dv_base_reg_parent();
      parent_csr.clear_shadow_wr_staged();

      if (lockable_field_cov != null) lockable_field_cov.post_read();
    end
  endtask

  virtual task post_write(uvm_reg_item rw);
    if (rw.status == UVM_IS_OK) begin
      uvm_reg_data_t field_val = rw.value[0] & ((1 << get_n_bits()) - 1);

      if (lockable_field_cov != null) lockable_field_cov.post_write(field_val, `gmv(regwen_fld));

      if (mubi_cov != null) mubi_cov.sample(field_val);
    end
  endtask

  function bit get_shadow_storage_err();
    uvm_reg_data_t mask = (1 << get_n_bits()) - 1;
    uvm_reg_data_t shadowed_val_temp = (~shadowed_val) & mask;
    uvm_reg_data_t committed_val_temp = committed_val & mask;
    `uvm_info(`gfn, $sformatf("shadow_val %0h, commmit_val %0h", shadowed_val_temp,
                              committed_val_temp), UVM_HIGH)
    sample_shadow_field_cov(.storage_err(1));
    return shadowed_val_temp != committed_val_temp;
  endfunction

  function void sample_shadow_field_cov(bit update_err = 0, bit storage_err = 0);
    if (shadowed_cov != null) shadowed_cov.shadow_field_errs_cg.sample(update_err, storage_err);
  endfunction

  function void update_staged_val(uvm_reg_data_t val);
    staged_val = val;
  endfunction

  function uvm_reg_data_t get_staged_val();
    return staged_val;
  endfunction

  function void update_shadowed_val(uvm_reg_data_t val);
    shadowed_val = val;
  endfunction

  function void update_committed_val(uvm_reg_data_t val);
    committed_val = val;
  endfunction

  function uvm_reg_data_t get_committed_val();
    return committed_val;
  endfunction

  // override RAL's reset function to support enable registers
  // when reset issued - the lockable field's access will be reset to original access
  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    set_fld_access(0);
    committed_val = get_mirrored_value();
    shadowed_val  = ~committed_val;
    if (lockable_field_cov != null) lockable_field_cov.reset(get_reset());
  endfunction

  // this function can only be called when this reg is intr_test reg
  // Example: ral.intr_test.get_intr_state_field()
  local function uvm_reg_field get_intr_state_field();
    uvm_reg_block blk = get_parent().get_parent();
    uvm_reg       intr_state_csr;
    uvm_reg_field fields[$];
    string        intr_state_csr_name;
    string        intr_test_csr_name = get_parent().get_name();
    bit           is_intr_state_csr = !(uvm_re_match("intr_test*", intr_test_csr_name));

    `DV_CHECK_EQ_FATAL(is_intr_state_csr, 1)

    // intr_enable and intr_state have the same suffix
    intr_state_csr_name = str_utils_pkg::str_replace(intr_test_csr_name, "test", "state");

    intr_state_csr = blk.get_reg_by_name(intr_state_csr_name);
    intr_state_csr.get_fields(fields);

    // the field location for intr_state and intr_test should be the same
    return fields[get_lsb_pos()];
  endfunction

endclass
