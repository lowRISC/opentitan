// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// UVM Frontdoor sequence to be used for JTAG CSR tests.
class lc_ctrl_jtag_reg_frontdoor_seq  extends uvm_reg_frontdoor;

  `uvm_object_utils(lc_ctrl_jtag_reg_frontdoor_seq)

  function new(string name = "lc_ctrl_jtag_reg_frontoor");
    super.new(name);
  endfunction : new

  virtual task body();
    uvm_reg r;
    uvm_reg_addr_t reg_addr;
    jtag_riscv_csr_seq bus_req;

    `uvm_info(`gfn, $sformatf("rw_info = %s, sequencer = %s ",
        rw_info.convert2string(),
        sequencer.get_full_name()), UVM_HIGH)

    `downcast(r,rw_info.element);
    reg_addr = r.get_address();
    bus_req = jtag_riscv_csr_seq::type_id::create("bus_req");
    bus_req.exp_err = 0;

    if (rw_info.kind == UVM_READ) begin // Read
      `DV_CHECK_RANDOMIZE_WITH_FATAL(bus_req,
          do_write == 0;
          addr     == reg_addr[DMI_ADDRW + 1 : 0]; // Select register address
          data     == 0;)
    end else begin // Write
      `DV_CHECK_RANDOMIZE_WITH_FATAL(bus_req,
          do_write == 1;
          addr     == reg_addr[DMI_ADDRW + 1 : 0]; // Select register address
          data     == rw_info.value[0];)
    end

    bus_req.start(sequencer,this);

    if(rw_info.kind == UVM_READ) begin
      rw_info.value[0] = bus_req.data;
    end
    rw_info.status = UVM_IS_OK;

    `uvm_info(`gfn, $sformatf("body: performed a %s of register %s via JTAG TAP data=%8h",
        rw_info.kind==UVM_READ ? "read" : "write",
        r.get_full_name(), rw_info.value[0]), UVM_MEDIUM)

  endtask

endclass : lc_ctrl_jtag_reg_frontdoor_seq
