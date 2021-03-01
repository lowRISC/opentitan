// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A dmi access sequence to drive a single CSR read or write
class jtag_dmi_access_seq extends dv_base_seq #(
    .REQ         (jtag_riscv_item),
    .CFG_T       (jtag_riscv_agent_cfg),
    .SEQUENCER_T (jtag_riscv_sequencer)
  );

  rand bit [DMI_OPW-1:0]   op;
  rand bit [DMI_DATAW-1:0] data;
  rand bit [DMI_ADDRW-1:0] addr;
  rand bit do_write;
  bit      exp_err;

  constraint op_c {
    do_write == 1 -> op == DmiWrite;
    do_write == 0 -> op == DmiRead;
  }
  `uvm_object_utils(jtag_dmi_access_seq)
  `uvm_object_new

  virtual task body();
    bit [DMI_DATAW-1:0] rdata;

    // Drive IR with DMI access
    send_dmi_req();

    // Drive DR with operation type, address, and data
    send_csr_req(op, data, addr);

    // Get operation status
    check_csr_req_status(op, rdata);

    // Check status
    `DV_CHECK_EQ(op, (exp_err ? DmiFail : DmiNoErr),
                 $sformatf("JTAG DMI %0s access failed!", do_write ? "write" : "read"))

    // Update operation status
    if (!do_write) data = rdata;
  endtask

  // This task sends a DMI request via JTAG instruction register.
  virtual task send_dmi_req();
    jtag_ir_seq ir_seq;
    `uvm_create_on(ir_seq, p_sequencer.jtag_sequencer_h);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(ir_seq,
        ir_len == DMI_IRW;
        ir     == JtagDmiAccess;)
    `uvm_send(ir_seq)
  endtask

  // This task sends a CSR register read/write request via JTAG data register.
  virtual task send_csr_req(bit [DMI_OPW-1:0]   op,
                            bit [DMI_DATAW-1:0] data,
                            bit [DMI_ADDRW-1:0] addr);
    jtag_dr_seq dr_seq;
    `uvm_create_on(dr_seq, p_sequencer.jtag_sequencer_h);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(dr_seq,
        dr_len == DMI_DRW;
        dr     == {addr, data, op};)
    `uvm_send(dr_seq)
  endtask

  // This task checks a CSR register read/write request status via data request.
  // This task will output operation status and rdata (this rdata is only meaningful if it is a
  // read operation).
  virtual task check_csr_req_status(ref bit [DMI_OPW-1:0] status, ref bit [DMI_DATAW-1:0] rdata);
    while (1) begin
      jtag_dr_seq dr_seq;
      `uvm_create_on(dr_seq, p_sequencer.jtag_sequencer_h);
      `DV_CHECK_RANDOMIZE_WITH_FATAL(dr_seq,
          dr_len == DMI_DRW;
          dr     == DmiStatus;)
      `uvm_send(dr_seq)
      status = dr_seq.rsp.dout[0 +: DMI_OPW];

      if (status != DmiInProgress) begin
        rdata = dr_seq.rsp.dout[2 +: DMI_DATAW];
        break;
      end
    end
  endtask

endclass
