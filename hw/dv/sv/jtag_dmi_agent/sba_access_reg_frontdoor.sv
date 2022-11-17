// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Frontdoor (indirect) access of CSRs over SBA using the JTAG interface.
//
// The system CSRs are accessed indirectly using the jtag_rv_debugger::sba_access() utility. Note
// that if this frontdoor is attached to the chip RAL model, then it takes precedence over the
// TL-based register map / adapter based built-in frontdoor. To attach this frontdoor, simply set
// the user_ftdr arg of csr_utils_pkg::csr_rd*|wr|update|spinwait() tasks to this class' instance.
typedef class jtag_rv_debugger;
class sba_access_reg_frontdoor extends uvm_reg_frontdoor;
  `uvm_object_utils(sba_access_reg_frontdoor)

  // Handle to JTAG RV debugger instance.
  jtag_rv_debugger debugger_h;

  `uvm_object_new

  virtual task body();
    uvm_reg_data_t  data;
    csr_field_t     csr_or_fld;
    sba_access_item sba_item;

    `uvm_info(`gfn, $sformatf("CSR req via SBA started: %0s", rw_info.convert2string()), UVM_HIGH)
    `DV_CHECK_FATAL(rw_info.element_kind inside {UVM_REG, UVM_FIELD})
    `DV_CHECK_FATAL(rw_info.kind inside {UVM_READ, UVM_WRITE})
    `DV_CHECK_FATAL(rw_info.path == UVM_FRONTDOOR)

    csr_or_fld = decode_csr_or_field(rw_info.element);
    sba_item = sba_access_item::type_id::create("sba_item");
    sba_item.addr = csr_or_fld.csr.get_address();
    sba_item.size = SbaAccessSize32b;
    if (rw_info.kind == UVM_WRITE) begin
      sba_item.bus_op = BusOpWrite;
      data = rw_info.value[0];
      if (csr_or_fld.field != null) begin
        data = get_csr_val_with_updated_field(csr_or_fld.field, `gmv(csr_or_fld.csr),
                                              rw_info.value[0]);
      end
      sba_item.wdata[0] = data;
    end else begin
      sba_item.bus_op = BusOpRead;
      sba_item.readonaddr = 1;
      sba_item.readondata = 0;
    end

    debugger_h.sba_access(sba_item);

    if (sba_item.is_err || sba_item.is_busy_err || sba_item.timed_out) begin
      `uvm_info(`gfn, $sformatf({"CSR req via SBA has error: is_err = %0b, is_busy_err = %0b, ",
                                 "timed_out = %0b"}, sba_item.is_err, sba_item.is_busy_err,
                                sba_item.timed_out), UVM_LOW)
      rw_info.status = UVM_NOT_OK;
    end else begin
      rw_info.status = UVM_IS_OK;
      if (rw_info.kind == UVM_READ) begin
        rw_info.value = new[1];
        data = sba_item.rdata[0];
        if (csr_or_fld.field != null) begin
          data = get_field_val(csr_or_fld.field, data);
        end
        rw_info.value[0] = data;
      end
    end
    `uvm_info(`gfn, $sformatf("CSR req via SBA completed: %0s", rw_info.convert2string()), UVM_HIGH)
  endtask

endclass
