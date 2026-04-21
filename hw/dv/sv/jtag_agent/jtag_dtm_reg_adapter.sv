// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Adapter to access JTAG DTM registers via JTAG.
class jtag_dtm_reg_adapter extends uvm_reg_adapter;
  `uvm_object_utils(jtag_dtm_reg_adapter)

  // Used when producing bus items for reads. See notes above set_reg_block() for details.
  local uvm_reg_map m_reg_map;

  // IR length to use in transactions. Set this with set_ir_len.
  local int unsigned m_ir_len;

  function new(string name = "");
    super.new(name);
    supports_byte_enable = 0;
    provides_responses = 1;
    // Have the uvm_reg_map to use this sequence to sync with the driver instead.
    parent_sequence = jtag_base_seq::type_id::create("parent_sequence");
    `DV_CHECK_GE_FATAL(`UVM_REG_DATA_WIDTH, JTAG_DRW)
  endfunction

  // Pass a handle to a uvm_reg_map that represents the DTM registers. This will be used by the
  // register adapter to generate bus items that represent register reads (in reg2bus). The tricky
  // thing is that the only way to read a register over JTAG is to write something to it and then
  // see the DR that comes out. In order for the stimulus to have as little impact as possible, this
  // model allows a sequence to write the value that we currently believe is in the register.
  //
  // If there is no such map available, reg2bus will send a DR of zero to read a register.
  function void set_reg_map(uvm_reg_map reg_map);
    m_reg_map = reg_map;
  endfunction

  // Set the IR length to use for transactions
  function void set_ir_len(int unsigned ir_len);
    if (!ir_len) `uvm_fatal(get_name(), "ir_len must be greater than zero.")
    m_ir_len = ir_len;
  endfunction

  function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
    jtag_item req;
    logic [JTAG_DRW-1:0] data;

    data = (rw.kind == UVM_READ) ? get_wdata_for_read(rw.addr) : rw.data[JTAG_DRW-1:0];

    req = jtag_item::type_id::create("req");
    if (!req.randomize() with {
          ir_len == m_ir_len;
          ir     == rw.addr[JTAG_IRW-1:0];
          dr_len == rw.n_bits;
          dr     == local::data;
          bus_op == (rw.kind == UVM_WRITE) ? dv_utils_pkg::BusOpWrite : dv_utils_pkg::BusOpRead;
          skip_reselected_ir == 1;
        }) begin
      `uvm_fatal(get_name(), "Failed to randomize JTAG item.")
    end
    `uvm_info(`gfn, $sformatf("reg2bus: %0s", req.sprint(uvm_default_line_printer)), UVM_HIGH)
    return req;
  endfunction

  // Get the value to send in DR that we believe is least likely to alter the current value of a
  // register at addr. See notes above set_reg_map for more information.
  local function uvm_reg_data_t get_wdata_for_read(uvm_reg_addr_t addr);
    uvm_reg           base_reg;
    jtag_dtm_base_reg dtm_reg;

    if (m_reg_map == null) return 0;

    base_reg = m_reg_map.get_reg_by_offset(addr);
    if (base_reg == null) begin
      `uvm_info(get_name(),
                $sformatf("Picking wdata of zero for read of the %0s register.",
                          base_reg.get_name()),
                UVM_HIGH)
      return 0;
    end

    if (!$cast(dtm_reg, base_reg)) begin
      `uvm_info(get_name(),
                $sformatf({"Cannot infer wdata for a read from register %0s: ",
                           "it is not a jtag_dtm_base_reg."},
                          base_reg.get_name()),
                UVM_HIGH)
      return 0;
    end

    return dtm_reg.get_wdata_for_read();
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
