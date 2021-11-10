// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class jtag_riscv_monitor extends dv_base_monitor #(
  .ITEM_T(jtag_riscv_item),
  .CFG_T (jtag_riscv_agent_cfg),
  .COV_T (jtag_riscv_agent_cov)
);
  `uvm_component_utils(jtag_riscv_monitor)

  uvm_tlm_analysis_fifo #(jtag_item) jtag_item_fifo;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    jtag_item_fifo = new("jtag_item_fifo", this);
  endfunction

  // collect transactions
  virtual protected task collect_trans(uvm_phase phase);
    jtag_item jt;
    logic [DMI_ADDRW-1:0] addr = 'X;
    logic [DMI_DATAW-1:0] wdata = 'X, rdata = 'X;
    jtag_op_e op_trans = 'X, op = 'X;
    jtag_op_status_e status = 'X;
    bit dmi_selected = 0;
    ITEM_T monitor_item;
    forever begin
      jtag_item_fifo.get(jt);
      `uvm_info(`gfn, jt.sprint(uvm_default_line_printer), UVM_HIGH)
      if (jt.select_ir == 1) begin
        // Instruction register transaction
        if (jt.ir == JtagDmiAccess) dmi_selected = 1;
        else dmi_selected = 0;
      end else if (dmi_selected) begin
        // DR transaction and DMI selected by the nstruction register
        // Extract op from the transaction data register
        op_trans = jt.dr[DMI_OPW-1 : 0];
        if (op_trans === DmiRead || op_trans === DmiWrite) begin
          // Read / write request
          op    = op_trans;
          addr  = jt.dr[DMI_ADDRW + DMI_DATAW + DMI_OPW - 1 : DMI_DATAW + DMI_OPW];
          wdata = jt.dr[DMI_DATAW + DMI_OPW - 1 : DMI_OPW];
          `uvm_info(`gfn, $sformatf(
                    "Got request - op:%s(%h) addr:%h wdata:%h", op.name, op, addr, wdata),
                    UVM_MEDIUM)
        end else if (op_trans === DmiStatus) begin
          // Status / response DR transaction
          // Extract status fields
          status = jt.dout[DMI_OPW-1 : 0];
          rdata  = jt.dout[DMI_DATAW+DMI_OPW-1 : DMI_OPW];
          // Only monitor packets for completed transactions -
          // Not retries (status===DmiInProgress)
          if (status === DmiNoErr || status === DmiFail) begin
            `uvm_create_obj(ITEM_T, monitor_item)
            monitor_item.addr   = addr;
            monitor_item.op     = op;
            monitor_item.data   = (op == DmiRead) ? rdata : wdata;
            monitor_item.status = status;
            analysis_port.write(monitor_item);
            `uvm_info(`gfn, monitor_item.sprint(uvm_default_line_printer), UVM_MEDIUM)
          end else if (status === DmiInProgress) begin
            `uvm_info(`gfn, $sformatf(
                      "Got busy status (%s) - op:%s(%h) addr:%h", status.name, op.name, op, addr),
                      UVM_MEDIUM)
          end else begin
            `uvm_error(`gfn, $sformatf("Bad status - %s(%h) ", status.name, status))
          end
        end else begin
          `uvm_error(`gfn, $sformatf("Bad op - %s(%h) ", op_trans.name, op_trans))
        end
      end
    end
  endtask
endclass
