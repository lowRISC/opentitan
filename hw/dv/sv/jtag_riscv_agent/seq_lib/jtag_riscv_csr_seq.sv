// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A dmi access sequence to drive a single CSR read or write
class jtag_riscv_csr_seq extends jtag_riscv_base_seq;

  rand bit [  DMI_OPW-1:0] op;
  rand bit [DMI_DATAW-1:0] data;
  // This is not DTM address, but address for the CSR registers
  rand bit [DMI_DATAW+1:0] addr;
  rand bit                 do_write;

  constraint op_c {
    do_write == 1 -> op == DmiWrite;
    do_write == 0 -> op == DmiRead;
  }

  `uvm_object_utils_begin(jtag_riscv_csr_seq)
    `uvm_field_int(op, UVM_DEFAULT)
    `uvm_field_int(addr, UVM_DEFAULT)
    `uvm_field_int(data, UVM_DEFAULT)
    `uvm_field_int(do_write, UVM_DEFAULT)
  `uvm_object_utils_end

  function new(string name = "");
    super.new(name);
  endfunction

  virtual task body();
    `uvm_create_obj(REQ, req)
    start_item(req);

    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
      op   == local::op;
      // convert byte address to word address
      addr == (cfg.is_rv_dm ? local::addr : (local::addr >> DMI_WORD_SHIFT));
      data == local::data;
      activate_rv_dm == 0;)

    finish_item(req);
    get_response(rsp);

    if (!do_write) data = rsp.data;
    if (!cfg.allow_errors) begin
      `DV_CHECK_EQ(rsp.status, DmiNoErr, $sformatf("JTAG DMI %0s access failed!",
                                                   do_write ? "write" : "read"))
    end
  endtask

endclass
