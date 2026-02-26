// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Specialised version of uvm_mem for OpenTitan
//
// The specialised version adds the possibilities that a memory:
//
//  - might not support partial writes (even if the bus would otherwise support them).
//
//  - might store integrity data but not check it (merely passing it through to the next read).

class dv_base_mem extends uvm_mem;
  // If true, the memory supports partial writes. If not, any partial write will get an error
  // response (d_error=1 in TileLink).
  local bit mem_partial_write_support;

  // If true, mem stores integrity along with data but it won't check the data integrity
  local bit data_intg_passthru;

  // Create a new instance of the memory abstraction class.
  //
  // The only access types supported are RW, RO and WO.
  extern function new(string           name,
                      longint unsigned size,
                      int unsigned     n_bits,
                      string           access = "RW",
                      int              has_coverage = UVM_NO_COVERAGE);

  extern function void set_mem_partial_write_support(bit enable);
  extern function bit get_mem_partial_write_support();

  extern function void set_data_intg_passthru(bit enable);
  extern function bit get_data_intg_passthru();

  // This overrides uvm_mem::configure (which is *not* a virtual function), removing the check that
  // the requested "access" is RW or RO, because we want to support WO as well.
  //
  // *That* check is now done in the constructor, where we can see the requested "access".
  extern function void configure(uvm_reg_block parent, string hdl_path="");
endclass

function dv_base_mem::new(string           name,
                          longint unsigned size,
                          int unsigned     n_bits,
                          string           access = "RW",
                          int              has_coverage = UVM_NO_COVERAGE);
  super.new(name, size, n_bits, access, has_coverage);
  if (!(access inside {"RW", "RO", "WO"}))
    `uvm_error(`gfn, $sformatf("Memory can only be RW, RO or WO (saw %s)", access))
endfunction

function void dv_base_mem::set_mem_partial_write_support(bit enable);
  mem_partial_write_support = enable;
endfunction

function bit dv_base_mem::get_mem_partial_write_support();
  return mem_partial_write_support;
endfunction

function void dv_base_mem::set_data_intg_passthru(bit enable);
  data_intg_passthru = enable;
endfunction

function bit dv_base_mem::get_data_intg_passthru();
  return data_intg_passthru;
endfunction

// Note: This is a copied version of uvm_mem::configure, but tweaked to remove the check on m_access
// (loosened slightly and now moved to the constructor)
function void dv_base_mem::configure(uvm_reg_block parent, string hdl_path="");
   if (parent == null)
     `uvm_fatal(`gfn, "configure: parent argument is null")

   set_parent(parent);

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
endfunction
