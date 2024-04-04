// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class jtag_riscv_base_seq extends dv_base_seq #(
    .REQ         (jtag_riscv_item),
    .CFG_T       (jtag_riscv_agent_cfg),
    .SEQUENCER_T (jtag_riscv_sequencer)
  );

  `uvm_object_utils(jtag_riscv_base_seq)
  `uvm_object_new

  virtual task send_riscv_ir_req(jtag_ir_e riscv_ir_req);
    jtag_ir_seq ir_seq;
    `uvm_create_on(ir_seq, p_sequencer.jtag_sequencer_h);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(ir_seq,
        ir_len == DMI_IRW;
        ir     == riscv_ir_req;)
    `uvm_send(ir_seq)
  endtask

  virtual task send_dtmcs_dr_req(jtag_dtmcs_e dtmcs_req_idx);
    jtag_dr_seq dr_seq;
    `uvm_create_on(dr_seq, p_sequencer.jtag_sequencer_h);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(dr_seq,
        dr_len == DTMCS_DRW;
        dr     == 1 << dtmcs_req_idx;)
    `uvm_send(dr_seq)
  endtask

  // This task sends a CSR register read/write request via JTAG data register.
  virtual task send_csr_dr_req(input bit [DMI_OPW-1:0]    op,
                               input bit [DMI_DATAW-1:0]  data,
                               input bit [DMI_ADDRW-1:0]  addr,
                               output bit [DMI_DATAW-1:0] dout);
    jtag_dr_seq dr_seq;
    `uvm_create_on(dr_seq, p_sequencer.jtag_sequencer_h);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(dr_seq,
        dr_len == DMI_DRW;
        dr     == {addr, data, op};)
    `uvm_send(dr_seq)
    dout = dr_seq.rsp.dout;
  endtask

endclass
