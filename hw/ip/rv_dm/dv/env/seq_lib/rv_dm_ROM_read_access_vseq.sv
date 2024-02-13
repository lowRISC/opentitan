// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rv_dm_ROM_read_access_vseq extends rv_dm_base_vseq;

`uvm_object_utils(rv_dm_ROM_read_access_vseq)

  `uvm_object_new

  constraint lc_hw_debug_en_c {
    lc_hw_debug_en == lc_ctrl_pkg::On;
  }
  constraint scanmode_c {
    scanmode == prim_mubi_pkg::MuBi4False;
  }
  task body();
    uvm_reg_data_t read_data;
    repeat ($urandom_range(1, 40)) begin
      csr_wr(.ptr(jtag_dmi_ral.dmcontrol.haltreq), .value(1));
      csr_wr(.ptr(tl_mem_ral.halted), .value(0));
      for (int i = 0; i <= 39; i++) begin
        mem_rd(.ptr(tl_mem_ral.rom),.offset('h00+i),.data(read_data));
        `uvm_info(`gfn, $sformatf("\n \n  Access rom addr 0x%0h", read_data),UVM_LOW)
      end
    end
  endtask

endclass : rv_dm_ROM_read_access_vseq
