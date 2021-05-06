// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// A dmi access sequence to drive a single CSR read or write
class jtag_riscv_csr_seq extends jtag_riscv_base_seq;

  rand bit [DMI_OPW-1:0]   op;
  rand bit [DMI_DATAW-1:0] data;
  rand bit [DMI_ADDRW+1:0] addr; // Need to convert from csr(byte) address to word address
  rand bit do_write;
  bit      exp_err;

  constraint op_c {
    do_write == 1 -> op == DmiWrite;
    do_write == 0 -> op == DmiRead;
  }
  `uvm_object_utils(jtag_riscv_csr_seq)
  `uvm_object_new

  virtual task body();
    bit [DMI_DATAW-1:0] rdata;
    bit [DMI_DRW-1:0]   dout;

    // Update address from CSR address to word address
    addr = addr >> 2;

    // Drive IR with DMI access
    send_riscv_ir_req(JtagDmiAccess);

    // Drive DR with operation type, address, and data
    send_csr_dr_req(op, data, addr, dout);

    // Get operation status
    check_csr_req_status(op, rdata);

    // Check status
    `DV_CHECK_EQ(op, (exp_err ? DmiFail : DmiNoErr),
                 $sformatf("JTAG DMI %0s access failed!", do_write ? "write" : "read"))

    // Update CSR read data
    if (!do_write) data = rdata;
  endtask

  // This task checks a CSR register read/write request status via data request.
  // This task will output operation status and rdata (this rdata is only meaningful if it is a
  // read operation).
  virtual task check_csr_req_status(ref bit [DMI_OPW-1:0] status, ref bit [DMI_DATAW-1:0] rdata);
    while (1) begin
      bit [DMI_DRW-1:0] dout;
      send_csr_dr_req(DmiStatus, 0, 0, dout);
      status = rdata[0 +: DMI_OPW];

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
