// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class tl_reg_adapter_vseq extends tl_agent_base_vseq;
  `uvm_object_utils(tl_reg_adapter_vseq)
  `uvm_object_new

  virtual task body();
    tl_reg_adapter #() adapter;
    tl_seq_item bus_rsp;
    uvm_reg_bus_op rw;

    adapter = tl_reg_adapter#()::type_id::create("adapter");
    bus_rsp = tl_seq_item::type_id::create("bus_rsp");
    bus_rsp.a_opcode = tlul_pkg::Get;

    // A completed response without d_error is successful.
    bus_rsp.req_completed = 1'b1;
    bus_rsp.d_error = 1'b0;
    adapter.bus2reg(bus_rsp, rw);
    `DV_CHECK_EQ(rw.status, UVM_IS_OK)

    // A completed response with d_error must be reported as an error.
    bus_rsp.d_error = 1'b1;
    adapter.bus2reg(bus_rsp, rw);
    `DV_CHECK_EQ(rw.status, UVM_NOT_OK)

    // Preserve the existing behavior for an incomplete request.
    bus_rsp.req_completed = 1'b0;
    bus_rsp.d_error = 1'b0;
    adapter.bus2reg(bus_rsp, rw);
    `DV_CHECK_EQ(rw.status, UVM_NOT_OK)
  endtask
endclass
