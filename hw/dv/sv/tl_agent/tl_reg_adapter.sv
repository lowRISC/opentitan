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
    ITEM_T  reg_item;
    reg_item = ITEM_T::type_id::create("reg_item");

    // tlul support partial rd but follow protocol standards
    // TODO: this code assumes TLUL data is always 32 bits wide, can explore more generic solution
    // TODO: seq_item level implemented constraints, so the constraints below could be optimized
    if (rw.kind == UVM_READ) begin
      reg_item.a_opcode = tlul_pkg::Get;
      case ($countones(rw.byte_en))
        3, 4: begin // no partial rd
          reg_item.a_mask = 'hf;
          reg_item.a_addr = rw.addr;
        end
        1: begin // partial rd 1 byte
          reg_item.a_mask = rw.byte_en;
          reg_item.a_addr = rw.addr + $clog2(rw.byte_en);
        end
        2: begin
          if (rw.byte_en == 'b0110) begin // no partial rd
            reg_item.a_mask = 'hf;
            reg_item.a_addr = rw.addr;
          end else begin // partial rd 2 bytes
            reg_item.a_mask = rw.byte_en;
            reg_item.a_addr = (rw.byte_en == 'b0011) ? rw.addr : rw.addr + 2;
          end
        end
        default: begin
          `uvm_fatal(`gtn, $sformatf("invalid byte_en value = 0x%0h", rw.byte_en));
        end
      endcase
      reg_item.a_size = $clog2($countones(reg_item.a_mask));
    end
    else begin // randomize CSR partial or full write
      // Actual width of the CSR may be < TL_DW bits depending on fields and their widths
      // In that case, the transaction size in bytes and partial write mask need to be at least as
      // wide as the CSR to be a valid transaction. Otherwise, the DUT can return an error response
      int          msb;
      dv_base_reg  csr;
      uvm_reg_item item    = get_item();
      uvm_reg_map  loc_map = item.local_map;
      uvm_reg      rg      = loc_map.get_reg_by_offset(rw.addr);
      `DV_CHECK_FATAL($cast(csr, rg))
      msb = csr.get_msb_pos();
      `DV_CHECK_RANDOMIZE_WITH_FATAL(reg_item,
          a_opcode inside {PutFullData, PutPartialData};
          a_addr    == rw.addr;
          a_data    == rw.data;
          a_mask[0] == 1;
          $countones(a_mask) > (msb / 8);)
    end
    `uvm_info(`gtn, $sformatf("tl reg req item: addr=0x%0h, op=%0s data=0x%0h, mask = %0h",
                              reg_item.a_addr, reg_item.a_opcode.name, reg_item.a_data,
                              reg_item.a_mask), UVM_HIGH)
    return reg_item;
  endfunction : reg2bus

  function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
    tl_seq_item reg_item;
    if (!$cast(reg_item, bus_item)) begin
      `uvm_fatal(`gtn, "Incorrect bus item type, expecting tl_seq_item");
    end
    rw.kind    = reg_item.a_opcode == tlul_pkg::PutFullData ? UVM_WRITE : UVM_READ;
    rw.addr    = reg_item.a_addr;
    rw.data    = (rw.kind == UVM_WRITE) ? reg_item.a_data : reg_item.d_data;
    rw.byte_en = reg_item.a_mask;
    rw.status  = reg_item.d_error? UVM_NOT_OK : UVM_IS_OK;
    `uvm_info(`gtn, $sformatf("tl reg rsp item: addr=0x%0h, op=%0s data=0x%0h",
                              rw.addr, rw.kind.name, rw.data), UVM_HIGH)
  endfunction: bus2reg

endclass : tl_reg_adapter

