// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class alert_handler_base_vseq extends cip_base_vseq #(
    .CFG_T               (alert_handler_env_cfg),
    .RAL_T               (alert_handler_reg_block),
    .COV_T               (alert_handler_env_cov),
    .VIRTUAL_SEQUENCER_T (alert_handler_virtual_sequencer)
  );
  `uvm_object_utils(alert_handler_base_vseq)

  // various knobs to enable certain routines
  bit do_alert_handler_init = 1'b0;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_alert_handler_init) alert_handler_init();
  endtask

  virtual task dut_shutdown();
    // nothing special yet
  endtask

  // setup basic alert_handler features
  virtual task alert_handler_init(bit [NUM_ALERT_HANDLER_CLASSES-1:0] intr_en = '1,
                                  bit                                 alert_en = 1'b1,
                                  bit [TL_DW-1:0]                     alert_class = 'he4,
                                  bit [TL_DW-1:0]                     classA_ctrl = 'h393d);
    // TODO: cfg_interrupts does not disable interrupt, need debug
    //cfg_interrupts(.interrupts(interrupts), .enable(1'b1));
    csr_wr(.csr(ral.intr_enable), .value(intr_en));
    ral.alert_en.set(alert_en);
    ral.alert_class.set(alert_class);
    ral.classa_ctrl.set(classA_ctrl);
    csr_update(.csr(ral.alert_en));
    csr_update(.csr(ral.alert_class));
    csr_update(.csr(ral.classa_ctrl));
  endtask

  virtual task drive_alert(int alert_index);
    alert_sender_seq alert_seq;
    `uvm_create_on(alert_seq, p_sequencer.alert_host_seqr_h[alert_index]);
    `DV_CHECK_RANDOMIZE_FATAL(alert_seq)
    `uvm_send(alert_seq)
  endtask

  virtual task clear_esc();
    csr_wr(.csr(ral.classa_clr), .value(1));
  endtask

  virtual task read_alert_cause();
    bit [TL_DW-1:0] alert_cause;
    // checking for this CSR is done in scb
    csr_rd(.ptr(ral.alert_cause), .value(alert_cause));
  endtask

endclass : alert_handler_base_vseq
