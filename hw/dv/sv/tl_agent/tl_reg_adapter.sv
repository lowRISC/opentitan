// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Class: register adapter type parameterized with the default tl_seq_item type. The idea is to
// extend tl_seq_item for further constraints or customizations if required and create the
// tl_reg_adapter instance with the overridden type.
class tl_reg_adapter #(type ITEM_T = tl_seq_item) extends uvm_reg_adapter;

  `uvm_object_param_utils(tl_reg_adapter#(ITEM_T))

  function new(string name = "tl_reg_adapter");
    super.new(name);
    supports_byte_enable = 1;
    provides_responses = 1;
  endfunction : new

  function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
    uvm_reg_item item = get_item();
    ITEM_T bus_item_loc;
    bus_item_loc = ITEM_T::type_id::create("bus_item_loc");

    // TODO: add a knob to contrl the randomization in case TLUL implementation changes and does
    // not support partial read/write
    // randomize CSR partial or full read
    // for partial read DUT (except memory) always return the entire 4 bytes bus data
    // if CSR full read (all bytes are enabled) & !MEM, randomly select full or partial read
    // if CSR field read, will do a partial read if protocal allows by setting a_mask to byte_en
    if (rw.kind == UVM_READ) begin
      if (rw.byte_en == '1 && item.element_kind == UVM_REG) begin // csr full read
        `DV_CHECK_RANDOMIZE_WITH_FATAL(bus_item_loc,
            a_opcode            == tlul_pkg::Get;
            a_addr[TL_AW-1:2]   == rw.addr[TL_AW-1:2];
            $countones(a_mask)  dist {TL_DBW       :/ 1,
                                      [0:TL_DBW-1] :/ 1};)
      end else begin // csr field read
        `DV_CHECK_RANDOMIZE_WITH_FATAL(bus_item_loc,
            a_opcode            == tlul_pkg::Get;
            a_addr[TL_AW-1:2]   == rw.addr[TL_AW-1:2];
            a_mask              == rw.byte_en;)
      end
    end else begin // randomize CSR partial or full write
      // Actual width of the CSR may be < TL_DW bits depending on fields and their widths
      // In that case, the transaction size in bytes and partial write mask need to be at least as
      // wide as the CSR to be a valid transaction. Otherwise, the DUT can return an error response
      int msb;

      // Check if csr addr or mem addr; accordingly, get the msb bit.
      if (item.element_kind == UVM_REG) begin
        dv_base_reg csr;
        uvm_object rg = item.element;
        `DV_CHECK_FATAL($cast(csr, rg))
        msb = csr.get_msb_pos();
      end else if (item.element_kind == UVM_MEM) begin
        msb = TL_DW - 1;
      end else begin
        `uvm_fatal(`gfn, $sformatf("Unexpected address 0x%0h", rw.addr))
      end
      `DV_CHECK_RANDOMIZE_WITH_FATAL(bus_item_loc,
          a_opcode inside {PutFullData, PutPartialData};
          a_addr    == rw.addr;
          a_data    == rw.data;
          a_mask[0] == 1;
          $countones(a_mask) > (msb / 8);)
    end
    `uvm_info(`gtn, $sformatf("tl reg req item: addr=0x%0h, op=%0s data=0x%0h, mask = %0h",
                              bus_item_loc.a_addr, rw.kind.name, bus_item_loc.a_data,
                              bus_item_loc.a_mask), UVM_HIGH)
    return bus_item_loc;
  endfunction : reg2bus

  function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
    ITEM_T bus_item_loc;
    if (!$cast(bus_item_loc, bus_item)) begin
      `uvm_fatal(`gtn, "Incorrect bus item type, expecting tl_seq_item (or it's derivative)");
    end
    rw.kind    = bus_item_loc.a_opcode == tlul_pkg::PutFullData ? UVM_WRITE : UVM_READ;
    rw.addr    = bus_item_loc.a_addr;
    rw.data    = (rw.kind == UVM_WRITE) ? bus_item_loc.a_data : bus_item_loc.d_data;
    rw.byte_en = bus_item_loc.a_mask;
    rw.status  = bus_item_loc.d_error ? UVM_NOT_OK : UVM_IS_OK;
    `uvm_info(`gtn, $sformatf("tl reg rsp item: addr=0x%0h, op=%0s data=0x%0h",
                              rw.addr, rw.kind.name, rw.data), UVM_HIGH)
  endfunction: bus2reg

endclass : tl_reg_adapter

