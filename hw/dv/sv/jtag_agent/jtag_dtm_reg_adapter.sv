// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Adapter to access JTAG DTM registers via JTAG.
class jtag_dtm_reg_adapter extends uvm_reg_adapter;
  `uvm_object_utils(jtag_dtm_reg_adapter)

  // Ensure that when an instance of this adapter is created, the cfg handle below is initialized
  // to the `jtag_agent_cfg` instance associated with this adapter instance.
  jtag_agent_cfg cfg;

  function new(string name = "jtag_dtm_reg_adapter");
    super.new(name);
    supports_byte_enable = 0;
    provides_responses = 1;
    // Have the uvm_reg_map to use this sequence to sync with the driver instead.
    parent_sequence = jtag_base_seq::type_id::create("parent_sequence");
    `DV_CHECK_GE_FATAL(`UVM_REG_DATA_WIDTH, JTAG_DRW)
  endfunction

  function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
    jtag_item req;
    logic [JTAG_DRW-1:0] data;
    // Per JTAG protocol, the DR is simultaneously written and read at the same time. That means, if
    // we want to read a register, we need to write its DR with the same value we wrote before, to
    // read it back. Otherwise, we will end up inadvertantly writing 0s to it when reading it. To do
    // so, we find the mirrored value of the register and set that to DR. Unfortunately, we do not
    // know which map is associated with this adapter, so this does not support a multi-map system
    // at this point.
    if (rw.kind == UVM_READ) begin
      jtag_dtm_base_reg rg;
      uvm_reg_map maps[$];
      cfg.jtag_dtm_ral.get_maps(maps);
      `DV_CHECK_EQ_FATAL(maps.size(), 1, $sformatf("Multiple maps in RAL %0s is not supported",
                                                   cfg.jtag_dtm_ral.get_full_name()))
      `downcast(rg, maps[0].get_reg_by_offset(rw.addr))
      data = rg.get_wdata_for_read();
    end else begin
      data = rw.data[JTAG_DRW-1:0];
    end

    req = jtag_item::type_id::create("req");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
        ir_len == cfg.ir_len;
        ir     == rw.addr[JTAG_IRW-1:0];
        dr_len == rw.n_bits;
        dr     == local::data;
        bus_op == (rw.kind == UVM_WRITE) ? dv_utils_pkg::BusOpWrite : dv_utils_pkg::BusOpRead;
        skip_reselected_ir == 1;)
    `uvm_info(`gfn, $sformatf("reg2bus: %0s", req.sprint(uvm_default_line_printer)), UVM_HIGH)
    return req;
  endfunction

  function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
    jtag_item rsp;
    `DV_CHECK_NE_FATAL(bus_item, null)
    `downcast(rsp, bus_item)
    // Throw fatal error if a partial IR only or DR only transaction is captured.
    `DV_CHECK_GT_FATAL(rsp.ir_len, 0, $sformatf("No IR transation found in rsp: %0s",
                                                rsp.sprint(uvm_default_line_printer)))
    `DV_CHECK_GT_FATAL(rsp.dr_len, 0, $sformatf("No DR transation found in rsp: %0s",
                                                rsp.sprint(uvm_default_line_printer)))
    rw.addr = rsp.ir;
    if (rsp.bus_op == dv_utils_pkg::BusOpWrite) begin
      rw.kind = UVM_WRITE;
    end else begin
      rw.kind = UVM_READ;
      rw.data = rsp.dout;
    end
    // TODO: detect bad packet status.
    rw.status = UVM_IS_OK;
    `uvm_info(`gfn, $sformatf("bus2reg: %0s", rsp.sprint(uvm_default_line_printer)), UVM_HIGH)
  endfunction

endclass
