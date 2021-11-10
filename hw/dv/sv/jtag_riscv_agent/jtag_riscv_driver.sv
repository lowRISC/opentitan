// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
// Pseudo driver to access CSR via JTAG TAP
class jtag_riscv_driver extends dv_base_driver #(jtag_riscv_item, jtag_riscv_agent_cfg);

  ITEM_T reqs[$];

  `uvm_object_utils(jtag_riscv_driver)

  `uvm_object_new

  // reset signals
  virtual task reset_signals();
    // Clear the queue
    reqs.delete();
  endtask

  // drive trans received from sequencer
  protected virtual task get_and_drive();
    fork
      drive_jtag();
    join_none

    forever begin
      seq_item_port.get_next_item(req);
      accept_tr(req);
      `downcast(rsp, req.clone())
      rsp.set_id_info(req);
      reqs.push_back(rsp);
      seq_item_port.item_done();
    end
  endtask

  protected virtual task drive_jtag();
    ITEM_T drive_req;
    bit [DMI_DATAW-1:0] dout;
    bit [DMI_DATAW-1:0] rdata;
    bit [DMI_ADDRW+1:0] word_addr;
    bit [DMI_OPW-1:0] status;
    forever begin
      wait (reqs.size());
      drive_req = reqs.pop_front();

      // Mark start of transaction processing
      void'(begin_tr(drive_req));

      // Byte to word address
      word_addr = drive_req.addr >> 2;

      // Drive IR with DMI access
      send_riscv_ir_req(JtagDmiAccess);

      // Drive DR with operation type, address, and data
      send_csr_dr_req(drive_req.op, drive_req.data, word_addr, dout);

      // Get status of previous transfer
      check_csr_req_status(status, rdata);
      drive_req.status = status;

      // Update CSR read data
      if (drive_req.op == DmiRead) drive_req.data = rdata;

      // Mark end of transaction processing
      end_tr(drive_req);

      // Send response
      rsp_port.write(drive_req);
    end
  endtask

 protected virtual task send_riscv_ir_req(jtag_ir_e riscv_ir_req);
    jtag_ir_seq ir_seq;
    `uvm_create_obj(jtag_ir_seq, ir_seq);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(ir_seq,
        ir_len == DMI_IRW;
        ir     == riscv_ir_req;)
    ir_seq.start(cfg.jtag_sequencer_h);
  endtask

  protected virtual task send_dtmcs_dr_req(jtag_dtmcs_e dtmcs_req_idx);
    jtag_dr_seq dr_seq;
    `uvm_create_obj(jtag_dr_seq, dr_seq);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(dr_seq,
        dr_len == DTMCS_DRW;
        dr     == 1 << dtmcs_req_idx;)
    dr_seq.start(cfg.jtag_sequencer_h);
  endtask

  // This task sends a CSR register read/write request via JTAG data register.
  protected virtual task send_csr_dr_req(input bit [DMI_OPW-1:0]    op,
                               input bit [DMI_DATAW-1:0]  data,
                               input bit [DMI_ADDRW-1:0]  addr,
                               output bit [DMI_DATAW-1:0] dout);
    jtag_dr_seq dr_seq;
    `uvm_create_obj(jtag_dr_seq, dr_seq);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(dr_seq,
        dr_len == DMI_DRW;
        dr     == {addr, data, op};)
    dr_seq.start(cfg.jtag_sequencer_h);
    dout = dr_seq.rsp.dout;
  endtask

  // This task checks a CSR register read/write request status via data request.
  // This task will output operation status and rdata (this rdata is only meaningful if it is a
  // read operation).
  protected virtual task check_csr_req_status(
      ref bit [DMI_OPW-1:0] status, ref bit [DMI_DATAW-1:0] rdata);
    while (1) begin
      bit [DMI_DRW-1:0] dout;
      send_csr_dr_req(DmiStatus, 0, 0, dout);
      status = dout[0 +: DMI_OPW];

      // The DmiInProgress status is sticky and has to be cleared by dmireset via DTMCS.
      if (status == DmiInProgress) begin
        send_riscv_ir_req(JtagDtmCsr);
        send_dtmcs_dr_req(DmiReset);
        send_riscv_ir_req(JtagDmiAccess);
      end

      if (status != DmiInProgress) begin
        rdata = dout[2 +: DMI_DATAW];
        break;
      end
    end
  endtask
endclass
