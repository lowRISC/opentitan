// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Captures reads and writes to DTM DMI register to infer transactions on the DMI interface.
//
// Unlike the name suggests, this monitor does not actually monitor the DMI interface
// directly, but indirectly by snooping the reads and writes to the DTM DMI register.
// TODO: In future, it may be better to rename this to jtag_dmi_csr_monitor.
class jtag_dmi_monitor #(type ITEM_T = jtag_dmi_item) extends dv_base_monitor#(
    .ITEM_T (ITEM_T),
    .CFG_T  (jtag_agent_cfg));
  `uvm_component_param_utils(jtag_dmi_monitor #(ITEM_T))

  // A queue holding an unserviced DMI request.
  ITEM_T dmi_req_q[$];

  // Incoming raw JTAG transactions.
  uvm_tlm_analysis_fifo #(jtag_item) jtag_item_fifo;

  // Outgoing filtered JTAG DTM transactions that do not touch the DMI register.
  uvm_analysis_port #(jtag_item) non_dmi_jtag_dtm_analysis_port;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    jtag_item_fifo = new("jtag_item_fifo", this);
    non_dmi_jtag_dtm_analysis_port = new("non_dmi_jtag_dtm_analysis_port", this);
  endfunction

  task run_phase(uvm_phase phase);
    fork
      super.run_phase(phase);
      monitor_reset();
    join
  endtask

  virtual protected task collect_trans(uvm_phase phase);
    jtag_item jtag_item;
    bit dmi_selected;

    forever begin
      bit busy;
      jtag_item_fifo.get(jtag_item);
      // jtag_item can either be an IR update or a DR update. Check packet for validity.
      if ((jtag_item.ir_len > 0) ~^ (jtag_item.dr_len > 0)) begin
        `uvm_error(`gfn, $sformatf("Bad packet: %0s. ir_len & dr_len are both zero, or non-zero.",
                                   jtag_item.sprint(uvm_default_line_printer)))
        continue;
      end
      if (jtag_item.ir_len) begin
        dmi_selected = is_dmi_selected(jtag_item);
        if (!dmi_selected) non_dmi_jtag_dtm_analysis_port.write(jtag_item);
        continue;
      end
      if (!dmi_selected) begin
        non_dmi_jtag_dtm_analysis_port.write(jtag_item);
        continue;
      end

      // Item has both, the new DMI request, as well as the response for the previous request.
      // Capture the response first, then the request.
      busy = capture_response(jtag_item);

      // A new DMI request is accepted only if the previous DMI transaction completed.
      if (!busy) capture_request(jtag_item);
    end
  endtask

  // Checks if the DMI IR is chosen.
  virtual function bit is_dmi_selected(jtag_item item);
    // A non-zero IR length indicates an IR update transacrtion.
    if (!item.ir_len) return 0;
    // If IR value matches DTM DMI address, return 1, else 0.
    if (item.ir == cfg.jtag_dtm_ral.dmi.get_address()) return 1;
    return 0;
  endfunction

  // Capture a new DMI request, if the previous DMI transaction is not in progress.
  //
  // Returns true if the response was captured, or if there was no previous request, false if the
  // response returned was busy.
  virtual function bit capture_response(jtag_item jtag_item);
    jtag_dmi_op_rsp_e rsp_op = jtag_dmi_op_rsp_e'(
        get_field_val(cfg.jtag_dtm_ral.dmi.op, jtag_item.dout));

    if (dmi_req_q.size() != 0) begin
      if (rsp_op == DmiOpInProgress) begin
        return 1;
      end else begin
        ITEM_T dmi_item = dmi_req_q.pop_front();
        dmi_item.rsp_op = rsp_op;
        if (dmi_item.req_op == DmiOpRead) begin
          uvm_reg_data_t data = get_field_val(cfg.jtag_dtm_ral.dmi.data,
                                              jtag_item.dout);
          dmi_item.rdata = data;
        end
        `uvm_info(`gfn, $sformatf("Writing DMI item to analysis_port: %0s",
                                  dmi_item.sprint(uvm_default_line_printer)), UVM_HIGH)
        analysis_port.write(dmi_item);
      end
    end else begin
      if (rsp_op != DmiOpOk) begin
        `uvm_error(`gfn, $sformatf("Non-ok response seen with no previous DMI request."))
      end
    end
    return 0;
  endfunction

  // Capture a new DMI request.
  virtual function void capture_request(jtag_item jtag_item);
    jtag_dmi_op_req_e req_op = jtag_dmi_op_req_e'(
        get_field_val(cfg.jtag_dtm_ral.dmi.op, jtag_item.dr));

    if (req_op inside {DmiOpRead, DmiOpWrite}) begin
      ITEM_T dmi_item = ITEM_T::type_id::create("dmi_item");
      dmi_item.req_op = req_op;
      dmi_item.addr = uvm_reg_addr_t'(
          get_field_val(cfg.jtag_dtm_ral.dmi.address, jtag_item.dr));
      if (req_op == DmiOpWrite) begin
        dmi_item.wdata = get_field_val(cfg.jtag_dtm_ral.dmi.data, jtag_item.dr);
      end
      `uvm_info(`gfn, $sformatf("Writing DMI req to req_analysis_port: %0s",
                                dmi_item.sprint(uvm_default_line_printer)), UVM_HIGH)
      req_analysis_port.write(dmi_item);
      dmi_req_q.push_back(dmi_item);
      `DV_CHECK_EQ_FATAL(dmi_req_q.size(), 1)
    end
  endfunction

  virtual task monitor_ready_to_end();
    forever begin
      if (dmi_req_q.size() == 0) begin
        ok_to_end = 1'b1;
        wait (dmi_req_q.size());
      end else begin
        ok_to_end = 1'b0;
        wait (dmi_req_q.size() == 0);
      end
    end
  endtask

  virtual protected task monitor_reset();
    forever @cfg.in_reset begin
      if (cfg.in_reset) dmi_req_q.delete();
    end
  endtask

endclass
