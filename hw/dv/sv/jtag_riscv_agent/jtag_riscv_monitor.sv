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
    jtag_item item;
    jtag_op_e op;
    logic [DMI_ADDRW-1:0] addr;
    logic [DMI_DATAW-1:0] data;
    jtag_op_status_e status;
    // Saved op field from initial transaction
    jtag_op_e saved_op;
    bit dmi_selected;
    ITEM_T monitor_item;

    forever begin
      jtag_item_fifo.get(item);
      `uvm_info(`gfn, item.sprint(uvm_default_line_printer), UVM_HIGH)
      if (item.ir_len) begin
        // Instruction register transaction
        if (item.ir == JtagDmiAccess) dmi_selected = 1;
        else dmi_selected = 0;
      end else if (dmi_selected) begin
        // DR transaction and DMI selected by the instruction register.
        // Extract op from the transaction data register.
        op = item.dr[DMI_OPW-1 : 0];
        if (op === DmiRead || op === DmiWrite) begin
          // Read / write request
          addr = item.dr[DMI_ADDRW+DMI_DATAW+DMI_OPW-1 : DMI_DATAW+DMI_OPW];
          data = item.dr[DMI_DATAW+DMI_OPW-1 : DMI_OPW];
          `uvm_info(`gfn, $sformatf(
                    "Got request - op:%0s addr:0x%0h data:0x%0h", op.name, addr, data), UVM_HIGH)
          // Save 'op' field to use when a successful status transaction arrives below
          saved_op = op;
        end else if (op === DmiStatus) begin
          // Status / response DR transaction
          // Extract status fields
          status = item.dout[DMI_OPW-1 : 0];
          addr   = item.dout[DMI_ADDRW+DMI_DATAW+DMI_OPW-1 : DMI_DATAW+DMI_OPW];
          data   = item.dout[DMI_DATAW+DMI_OPW-1 : DMI_OPW];
          // Only monitor packets for completed transactions -
          // Not retries (status===DmiInProgress)
          if (status === DmiNoErr || status === DmiFail) begin
            `uvm_create_obj(ITEM_T, monitor_item)
            monitor_item.addr   = addr;
            monitor_item.op     = saved_op;
            monitor_item.data   = data;
            monitor_item.status = status;
            analysis_port.write(monitor_item);
            `uvm_info(`gfn, monitor_item.sprint(uvm_default_line_printer), UVM_MEDIUM)
          end else if (status === DmiInProgress) begin
            `uvm_info(`gfn, $sformatf(
                      "Got busy status %0s - op:%0s addr:0x%0h", status.name, op.name, addr),
                      UVM_HIGH)
          end else begin
            if (!cfg.allow_errors) begin
              `uvm_error(`gfn, $sformatf("Bad status - %0s(0x%0h) ", status.name, status))
            end else begin
              `uvm_info(`gfn, $sformatf("Bad status - %0s(0x%0h) ", status.name, status), UVM_HIGH)
            end
          end
        end else begin
          `uvm_error(`gfn, $sformatf("Bad op - %0s(0x%0h)", op.name, op))
        end
      end
    end
  endtask
endclass
