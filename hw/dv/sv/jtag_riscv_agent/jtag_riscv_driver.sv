// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Pseudo driver to access CSR via JTAG TAP
class jtag_riscv_driver extends dv_base_driver #(jtag_riscv_item, jtag_riscv_agent_cfg);

  protected bit do_hard_reset;

  `uvm_component_utils(jtag_riscv_driver)

  function new (string name="", uvm_component parent=null);
    super.new(name, parent);
  endfunction

  virtual task reset_signals();
    forever begin
      wait (cfg.in_reset == 1);
      `uvm_info(`gfn, "reset_signals: cfg.in_reset=1'b1", UVM_MEDIUM)

      do_hard_reset = 1;
      // Assert JTAG TRST
      // This clears the DMI Request and Response FIFOs.
      cfg.m_jtag_agent_cfg.vif.do_trst_n(2);
      cfg.rv_dm_activated = 0;

      wait (cfg.in_reset == 0);
      `uvm_info(`gfn, "reset_signals: cfg.in_reset=1'b0", UVM_MEDIUM)
    end
  endtask

  // drive trans received from sequencer
  virtual task get_and_drive();
    `uvm_info(`gfn, "get_and_drive: STARTED", UVM_MEDIUM)
    forever begin
      seq_item_port.get_next_item(req);
      `uvm_info(`gfn, {"got request: ", req.sprint(uvm_default_line_printer)}, UVM_HIGH)

      accept_tr(req);
      `downcast(rsp, req.clone())
      rsp.set_id_info(req);
      seq_item_port.item_done();

      `DV_SPINWAIT_EXIT(
          drive_jtag(rsp);,
          wait(cfg.in_reset == 1);,)

      if (cfg.in_reset) rsp.status = cfg.status_in_reset;
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

    if (do_hard_reset) begin
      // A previous reset happend via cfg.in_reset
      // Make sure the DMI is reset
      if (!cfg.in_reset) begin
        send_riscv_ir_req(JtagDtmCsr);
        send_dtmcs_dr_req(DmiHardReset);
        do_hard_reset = 0;
      end
    end

    send_riscv_ir_req(JtagDmiAccess);

    if (drive_req.activate_rv_dm) begin
      activate_rv_dm(drive_req.status);
    end else begin
      if (cfg.is_rv_dm) begin
        bit [DMI_DATAW-1:0] sbcs_val = (2'b10 << SbAccess) | ('b1 << SbBusy);
        if (drive_req.op == DmiRead) sbcs_val |= 'b1 << SbReadOnAddr;

        `DV_CHECK_FATAL(cfg.rv_dm_activated, "Please activate rv_dm before accessing CSRs!")

        // If using rv_dm to access csr, need to send the following seq:
        // 1). Set busy bit in sbcs.
        // 2). Write address to SBAddress0.
        // 3). Write/Read csr data via SbData0.
        send_csr_req(.op(DmiWrite), .data(sbcs_val), .addr(Sbcs), .dout(dout), .status(status));
        send_csr_req(.op(DmiWrite), .data(drive_req.addr), .addr(SbAddress0), .dout(dout),
                     .status(status));
        // For RV_DM jtag operation, all requests except sbcs write will be blocking until sbcs
        // indicates the request is done.
        if (drive_req.op == DmiRead) wait_sbcs_idle();
        send_csr_req(.op(drive_req.op), .data(drive_req.data), .addr(SbData0), .dout(dout),
                     .status(status));
      end else begin
        // Drive DR with operation type, address, and data.
        send_csr_req(.op(drive_req.op), .data(drive_req.data), .addr(drive_req.addr), .dout(dout),
                     .status(status));
      end

      // Get status of previous transfer
      drive_req.status = status;

      // Update CSR read data
      if (drive_req.op == DmiRead) drive_req.data = dout;
    end

    // Mark end of transaction processing
    end_tr(drive_req);
  endtask

  protected virtual task send_riscv_ir_req(jtag_ir_e riscv_ir_req);
    jtag_ir_seq m_ir_seq;
    `uvm_create_obj(jtag_ir_seq, m_ir_seq);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(m_ir_seq,
        ir_len == DMI_IRW;
        ir     == riscv_ir_req;)
    m_ir_seq.start(cfg.jtag_sequencer_h);
  endtask

  protected virtual task send_dtmcs_dr_req(jtag_dtmcs_e dtmcs_req_idx);
    jtag_dr_seq m_dr_seq;
    `uvm_create_obj(jtag_dr_seq, m_dr_seq);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(m_dr_seq,
        dr_len == DTMCS_DRW;
        dr     == 1 << dtmcs_req_idx;)
    m_dr_seq.start(cfg.jtag_sequencer_h);
  endtask

  // This task finishes a csr read/write transaction:
  // 1. Driving JTAG's DR register to start the transaction.
  // 2. Check status until the transaction is done.
  protected virtual task send_csr_req(input bit [DMI_OPW-1:0] op,
                                      input bit [DMI_DATAW-1:0] data,
                                      input bit [DMI_ADDRW-1:0] addr,
                                      output bit [DMI_DRW-1:0] dout,
                                      output bit [DMI_OPW-1:0] status);
    // Drive DR with operation type, address, and data.
    send_csr_dr_req(.op(op), .data(data), .addr(addr), .dout(dout));

    // Get status of previous transfer
    check_csr_req_status(.status(status), .rdata(dout));
  endtask

  // This task sends a CSR register read/write request via JTAG data register.
  protected virtual task send_csr_dr_req(
      input bit [DMI_OPW-1:0] op, input bit [DMI_DATAW-1:0] data,
      input bit [DMI_ADDRW-1:0] addr, output bit [DMI_DRW-1:0] dout);
    jtag_dr_seq m_dr_seq;
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
  protected virtual task check_csr_req_status(output bit [DMI_OPW-1:0] status,
                                              output bit [DMI_DATAW-1:0] rdata);
    while (!cfg.in_reset) begin
      bit [DMI_DRW-1:0] dout;
      if (!cfg.in_reset) send_csr_dr_req(.op(DmiStatus), .addr(0), .data(0), .dout(dout));
      status = dout[0 +: DMI_OPW];

      // The DmiInProgress status is sticky and has to be cleared by dmireset via DTMCS.
      // Accessing the reserved value means there is also something wrong with the JTAG sequence,
      // potentially IR request, so also need to reset.
      if (status inside {DmiInProgress, DmiReserved}) begin
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

  protected virtual task activate_rv_dm(output jtag_op_status_e activation_status);
    bit [bus_params_pkg::BUS_DW-1:0] dmctrl_val, sbcs_val;
    bit [DMI_OPW-1:0] status;
    int cnter;

    // Set dmcontrol's dmactive bit.
    while (dmctrl_val == 0 && cnter < cfg.max_rv_dm_activation_attempts) begin
      cnter++;
      send_csr_req(.op(DmiWrite), .data(1), .addr(DmControl), .dout(dmctrl_val), .status(status));
      send_csr_req(.op(DmiRead), .data(0), .addr(DmControl), .dout(dmctrl_val), .status(status));
    end
    if (cnter >= cfg.max_rv_dm_activation_attempts) begin
      string msg = $sformatf("Could not activate RV_DM after %0d attempts!", cnter);
      if (cfg.allow_rv_dm_activation_fail) begin
        `uvm_info(`gfn, msg, UVM_LOW)
      end else begin
        `uvm_error(`gfn, msg)
      end
      activation_status = DmiFail;
      return;
    end

    // Read system bus access control and status register.
    // Once the sbcs value is not 0, then RV_DM jtag is ready.
    while (sbcs_val == 0)  begin
      send_csr_req(.op(DmiRead), .data(0), .addr(Sbcs), .dout(sbcs_val), .status(status));
    end

    // Ensure the RV_DM is set to correct bus width.
    `DV_CHECK_EQ(sbcs_val[SbAccess32], 1, "expect SBA width to be 32 bits!", error, msg_id)

    cfg.rv_dm_activated = 1;
    activation_status = DmiNoErr;
  endtask

  protected virtual task wait_sbcs_idle();
    bit [DMI_DATAW-1:0] sbcs_val;
    `DV_SPINWAIT(
        do begin
          bit [DMI_OPW-1:0] status;
          send_csr_req(.op(DmiRead), .data(0), .addr(Sbcs), .dout(sbcs_val), .status(status));
        end while (sbcs_val[SbBusy] == 1);,
        "timeout waiting for sbcs to be idle", default_jtag_timeout
    )
  endtask

endclass
