// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Register adapter to access CSR via JTAG TAP
class jtag_riscv_reg_adapter extends uvm_reg_adapter;
  `uvm_object_utils(jtag_riscv_reg_adapter)

  // Ensure that when an instance of this adapter is created, the cfg handle below is initialized
  // to the `jtag_riscv_agent_cfg` instance associated with this adapter instance.
  jtag_riscv_agent_cfg cfg;

  function new(string name = "jtag_riscv_reg_adapter");
    super.new(name);
    // We don't do byte enables
    supports_byte_enable = 0;
    // We do send responses
    provides_responses   = 1;
  endfunction

  virtual function uvm_sequence_item reg2bus(const ref uvm_reg_bus_op rw);
    jtag_riscv_item jtag_item = jtag_riscv_item::type_id::create(
        "jtag_item", null, this.get_full_name()
    );
    // RV_DM can input CSR address up to 128 bits.
    bit [DMI_DATAW-1:0] rw_addr = cfg.is_rv_dm ? rw.addr[DMI_DATAW-1:0] :
                                  rw.addr[DMI_ADDRW + DMI_WORD_SHIFT - 1 : DMI_WORD_SHIFT];

    `DV_CHECK_RANDOMIZE_WITH_FATAL(jtag_item,
        if (local::rw.kind == UVM_WRITE) {
          op == DmiWrite;
        } else {
          op == DmiRead;
        }
        // Convert to word address by slicing
        addr == rw_addr;
        data == local::rw.data[DMI_DATAW-1:0];
        activate_rv_dm == 0;)
    `uvm_info(`gfn, $sformatf("reg2bus: %s", jtag_item.sprint(uvm_default_line_printer)), UVM_HIGH)
    return jtag_item;
  endfunction

  virtual function void bus2reg(uvm_sequence_item bus_item, ref uvm_reg_bus_op rw);
    jtag_riscv_item jtag_item;

    `DV_CHECK_NE_FATAL(bus_item, null)
    `downcast(jtag_item, bus_item)

    unique case (jtag_item.op)
      DmiWrite: rw.kind = UVM_WRITE;
      DmiRead:  rw.kind = UVM_READ;
      default:  `uvm_fatal(`gfn, $sformatf("Invalid operation code %h", jtag_item.op))
    endcase

    rw.addr = cfg.is_rv_dm ? jtag_item.addr : (jtag_item.addr << DMI_WORD_SHIFT);
    // No byte enables
    rw.byte_en = '1;
    rw.data = jtag_item.data;
    rw.status = (jtag_item.status == DmiNoErr) ? UVM_IS_OK : UVM_NOT_OK;

    `uvm_info(`gfn, $sformatf("bus2reg: rw=%p", rw), UVM_HIGH)
  endfunction

endclass
