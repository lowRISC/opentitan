// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// base register reg class which will be used to generate the reg mem
class dv_base_mem extends uvm_mem;

  // uvm_mem::m_access is local variable. Create it again in order to use "access" in current class
  local string m_access;

  // if mem doesn't support partial write, doing that will result d_error = 1
  local bit mem_partial_write_support;

  // Modifies the expectation of writes / reads to RO / WO mem. By default it should be an error
  // response, but some implementations may choose to just ignore it.
  local bit write_to_ro_mem_ok;
  local bit read_to_wo_mem_ok;

  // if data integrity is passthru, mem stores integrity along with data but it won't check the
  // data integrity
  local bit data_intg_passthru;

  function new(string           name,
               longint unsigned size,
               int unsigned     n_bits,
               string           access = "RW",
               int              has_coverage = UVM_NO_COVERAGE);
    super.new(name, size, n_bits, access, has_coverage);
    m_access = access;
  endfunction : new

  function void set_mem_partial_write_support(bit enable);
    mem_partial_write_support = enable;
  endfunction : set_mem_partial_write_support

  function bit get_mem_partial_write_support();
    return mem_partial_write_support;
  endfunction : get_mem_partial_write_support

  function void set_data_intg_passthru(bit enable);
    data_intg_passthru = enable;
  endfunction : set_data_intg_passthru

  function bit get_data_intg_passthru();
    return data_intg_passthru;
  endfunction : get_data_intg_passthru

  function void set_write_to_ro_mem_ok(bit ok);
    write_to_ro_mem_ok = ok;
  endfunction

  function bit get_write_to_ro_mem_ok();
    return write_to_ro_mem_ok;
  endfunction

  function void set_read_to_wo_mem_ok(bit ok);
    read_to_wo_mem_ok = ok;
  endfunction

  function bit get_read_to_wo_mem_ok();
    return read_to_wo_mem_ok;
  endfunction

  // rewrite this function to support "WO" access type for mem
  function void configure(uvm_reg_block  parent,
                          string         hdl_path="");
     if (parent == null)
       `uvm_fatal("REG/NULL_PARENT","configure: parent argument is null")

     set_parent(parent);

     if (!(m_access inside {"RW", "RO", "WO"})) begin
        `uvm_error("RegModel", {"Memory '",get_full_name(),"' can only be RW, RO or WO"})
     end

     begin
        uvm_mem_mam_cfg cfg = new;

        cfg.n_bytes      = ((get_n_bits() - 1) / 8) + 1;
        cfg.start_offset = 0;
        cfg.end_offset   = get_size() - 1;

        cfg.mode     = uvm_mem_mam::GREEDY;
        cfg.locality = uvm_mem_mam::BROAD;

        mam = new(get_full_name(), cfg, this);
     end

     parent.add_mem(this);

     if (hdl_path != "") add_hdl_path_slice(hdl_path, -1, -1);
  endfunction: configure

endclass
