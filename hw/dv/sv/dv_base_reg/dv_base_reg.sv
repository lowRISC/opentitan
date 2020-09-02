// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// base register class which will be used to generate the reg
class dv_base_reg extends uvm_reg;
  // external reg doesn't have storage in reg module, which may connect to some combinational logic
  // hence, backdoor write isn't available
  local bit is_ext_reg;

  local dv_base_reg    locked_regs[$];
  local uvm_reg_data_t staged_shadow_val, committed_val, shadowed_val;
  local bit            is_shadowed;
  local bit            shadow_wr_staged; // stage the first shadow reg write
  local bit            shadow_update_err;
  local bit            en_shadow_wr = 1;

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
    uvm_reg_field ral_fields[$];
    get_fields(ral_fields);
    foreach (ral_fields[i]) `downcast(dv_fields[i], ral_fields[i])
  endfunction

  // get_n_bits will return number of all the bits in the csr
  // while this function will return actual number of bits used in reg field
  function uint get_n_used_bits();
    uvm_reg_field fields[$];
    get_fields(fields);
    foreach (fields[i]) get_n_used_bits += fields[i].get_n_bits();
  endfunction

  // loop all the fields to find the msb position of this reg
  function uint get_msb_pos();
    uvm_reg_field fields[$];
    get_fields(fields);
    foreach (fields[i]) begin
      uint field_msb_pos = fields[i].get_lsb_pos() + fields[i].get_n_bits() - 1;
      if (field_msb_pos > get_msb_pos) get_msb_pos = field_msb_pos;
    end
  endfunction

  // if the register is an enable reg, it will add controlled registers in the queue
  function void add_locked_reg(dv_base_reg locked_reg);
    locked_regs.push_back(locked_reg);
  endfunction

  function bit is_enable_reg();
    return (locked_regs.size() > 0);
  endfunction

  function bit is_staged();
     return shadow_wr_staged;
  endfunction

  // if enable register is set to 1, the locked registers will be set to RO access
  // once enable register is reset to 0, the locked registers will be set back to original access
  function void set_locked_regs_access(string access = "original_access");
    foreach (locked_regs[i]) begin
      dv_base_reg_field locked_fields[$];
      locked_regs[i].get_dv_base_reg_fields(locked_fields);
      foreach (locked_fields[i]) locked_fields[i].set_locked_fields_access(access);
    end
  endfunction

  function void get_locked_regs(ref dv_base_reg locked_regs_q[$]);
    locked_regs_q = locked_regs;
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
  // - shadow register, enable reg won't be updated until the second write has no error
  // - enable register, if enable_reg is disabled, change access policy to all the locked_regs
  // TODO: create an `enable_field_access_policy` variable and set the template code during
  // automation.
  virtual task post_write(uvm_reg_item rw);
    dv_base_reg_field fields[$];
    string field_access;

    // no need to update shadow value or access type if access is not OK, as access is aborted
    if (rw.status != UVM_IS_OK) return;

    if (is_shadowed) begin
      // first write
      if (!shadow_wr_staged) begin
        shadow_wr_staged = 1;
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
    if (is_enable_reg()) begin
      get_dv_base_reg_fields(fields);
      field_access = fields[0].get_access();
      case (field_access)
        // rw.value is a dynamic array
        "W1C": if (rw.value[0][0] == 1'b1) set_locked_regs_access("RO");
        "W0C": if (rw.value[0][0] == 1'b0) set_locked_regs_access("RO");
        "RO": ; // if RO, it's updated by design, need to predict in scb
        default:`uvm_fatal(`gfn, $sformatf("enable register invalid access %s", field_access))
      endcase
    end
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

  // override do_predict function to support shadow_reg:
  // skip predict if it is shadow_reg's first write, or second write with an update_err
  virtual function void do_predict (uvm_reg_item      rw,
                                    uvm_predict_e     kind = UVM_PREDICT_DIRECT,
                                    uvm_reg_byte_en_t be = -1);
    if (is_shadowed && (shadow_wr_staged || shadow_update_err) && kind != UVM_PREDICT_READ) begin
      `uvm_info(`gfn,
                $sformatf("skip predict csr %s: due to shadow_reg_first_wr=%0b or update_err=%0b",
                          get_name(), shadow_wr_staged, shadow_update_err), UVM_HIGH)
      return;
    end
    super.do_predict(rw, kind, be);
  endfunction

  virtual task poke (output uvm_status_e     status,
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

  // callback function to update shadowed values according to specific design
  // should only be called after post-write
  virtual function void update_shadowed_val(uvm_reg_data_t val, bit do_predict = 1);
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
      committed_val     = get_mirrored_value();
      shadowed_val      = ~committed_val;
      // in case reset is issued during shadowed writes
      void'(atomic_shadow_wr.try_get(1));
      void'(atomic_en_shadow_wr.try_get(1));
      atomic_shadow_wr.put(1);
      atomic_en_shadow_wr.put(1);
    end
  endfunction
endclass
