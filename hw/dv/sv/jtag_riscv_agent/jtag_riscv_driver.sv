// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Pseudo driver to access CSR via JTAG TAP
class jtag_riscv_driver extends dv_base_driver #(jtag_riscv_item, jtag_riscv_agent_cfg);

  protected jtag_ir_seq m_ir_seq;
  protected jtag_dr_seq m_dr_seq;
  protected bit         reset_occured;
  `uvm_object_utils(jtag_riscv_driver)

  `uvm_object_new

  virtual task run_phase(uvm_phase phase);
    fork
      super.run_phase(phase);
      in_reset_proc();
    join_none
  endtask

  // reset signals
  virtual task reset_signals();
    `uvm_info(`gfn, "reset_signals: STARTED", UVM_MEDIUM)
    // Terminate any sequences currently running
    // No more will be started while cfg.in_reset is asserted
    if (m_ir_seq != null) m_ir_seq.kill();
    if (m_dr_seq != null) m_dr_seq.kill();
    reset_occured = 1;
    // Assert JTAG TRST
    // This clears the DMI Request and Response FIFOs.
    cfg.m_jtag_agent_cfg.vif.do_trst_n(2);
  endtask

  // drive trans received from sequencer
  protected virtual task get_and_drive();
    `uvm_info(`gfn, "get_and_drive: STARTED", UVM_MEDIUM)
    forever begin
      seq_item_port.get_next_item(req);
      `uvm_info(`gfn, {"got request: ", req.sprint(uvm_default_line_printer)}, UVM_HIGH)
      accept_tr(req);
      `downcast(rsp, req.clone())
      rsp.set_id_info(req);
      seq_item_port.item_done();
      drive_jtag(rsp);
      seq_item_port.put_response(rsp);
    end
  endtask

  protected virtual task drive_jtag(ITEM_T drive_req);
    bit [DMI_DATAW-1:0] dout;
    bit [DMI_DATAW-1:0] rdata;
    bit [  DMI_OPW-1:0] status;

    `uvm_info(`gfn, {"drive_jtag: ", drive_req.sprint(uvm_default_line_printer)}, UVM_HIGH)

    // Mark start of transaction processing
    void'(begin_tr(drive_req));

    if (reset_occured) begin
      // A previous reset happend via cfg.in_reset
      // Make sure the DMI is reset
      if (!cfg.in_reset) begin
        send_riscv_ir_req(JtagDtmCsr);
        send_dtmcs_dr_req(DmiHardReset);
        reset_occured = 0;
      end
    end

    if (!cfg.in_reset) begin
      // Drive IR with DMI access
      send_riscv_ir_req(JtagDmiAccess);
    end

    if (!cfg.in_reset) begin
      // Drive DR with operation type, address, and data
      send_csr_dr_req(.op(drive_req.op), .data(drive_req.data), .addr(drive_req.addr), .dout(dout));
    end

    if (!cfg.in_reset) begin
      // Get status of previous transfer
      check_csr_req_status(.status(status), .rdata(rdata));
      drive_req.status = status;
    end

    // Update CSR read data
    if (drive_req.op == DmiRead) drive_req.data = rdata;

    // Use status value in cfg if we have asserted in_reset
    if (cfg.in_reset) begin
      drive_req.status = cfg.status_in_reset;
      // Small delay to avoid infinite loops
      #1ns;
    end

    // Mark end of transaction processing
    end_tr(drive_req);

  endtask

  protected virtual task in_reset_proc();
    forever begin
      wait(cfg.in_reset == 1);
      `uvm_info(`gfn, "in_reset_proc: cfg.in_reset=1'b1", UVM_MEDIUM)
      reset_signals();
      wait(cfg.in_reset == 0);
      `uvm_info(`gfn, "in_reset_proc: cfg.in_reset=1'b0", UVM_MEDIUM)
    end
  endtask

  protected virtual task send_riscv_ir_req(jtag_ir_e riscv_ir_req);
    `uvm_create_obj(jtag_ir_seq, m_ir_seq);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(m_ir_seq,
        ir_len == DMI_IRW;
        ir     == riscv_ir_req;)
    m_ir_seq.start(cfg.jtag_sequencer_h);
  endtask

  protected virtual task send_dtmcs_dr_req(jtag_dtmcs_e dtmcs_req_idx);
    `uvm_create_obj(jtag_dr_seq, m_dr_seq);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(m_dr_seq,
        dr_len == DTMCS_DRW;
        dr     == 1 << dtmcs_req_idx;)
    m_dr_seq.start(cfg.jtag_sequencer_h);
  endtask

  // This task sends a CSR register read/write request via JTAG data register.
  protected virtual task send_csr_dr_req(
      input bit [DMI_OPW-1:0] op, input bit [DMI_DATAW-1:0] data,
      input bit [DMI_ADDRW-1:0] addr, output bit [DMI_DATAW-1:0] dout);
    `uvm_create_obj(jtag_dr_seq, m_dr_seq);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(m_dr_seq,
        dr_len == DMI_DRW;
        dr     == {addr, data, op};)
    m_dr_seq.start(cfg.jtag_sequencer_h);
    // Might be no response item if the sequence has been killed
    if (m_dr_seq.rsp != null) dout = m_dr_seq.rsp.dout;
  endtask

  // This task checks a CSR register read/write request status via data request.
  // This task will output operation status and rdata (this rdata is only meaningful if it is a
  // read operation).
  protected virtual task check_csr_req_status(ref bit [DMI_OPW-1:0] status,
                                              ref bit [DMI_DATAW-1:0] rdata);
    while (!cfg.in_reset) begin
      bit [DMI_DRW-1:0] dout;
      if (!cfg.in_reset) send_csr_dr_req(.op(DmiStatus), .addr(0), .data(0), .dout(dout));
      status = dout[0 +: DMI_OPW];

      // The DmiInProgress status is sticky and has to be cleared by dmireset via DTMCS.
      if (status == DmiInProgress) begin
        if (!cfg.in_reset) send_riscv_ir_req(JtagDtmCsr);
        if (!cfg.in_reset) send_dtmcs_dr_req(DmiReset);
        if (!cfg.in_reset) send_riscv_ir_req(JtagDmiAccess);
      end

      if (status === DmiNoErr || status === DmiFail) begin
        rdata = dout[DMI_OPW +: DMI_DATAW];
        break;
      end
    end
  endtask
endclass
