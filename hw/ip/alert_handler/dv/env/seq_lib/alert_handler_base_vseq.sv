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

  virtual task run_esc_rsp_seq_nonblocking();
    for (int i = 0; i < alert_pkg::N_ESC_SEV-1; i++) begin
      automatic int j = i;
      fork
        forever begin
          esc_receiver_esc_rsp_seq esc_seq =
              esc_receiver_esc_rsp_seq::type_id::create("esc_seq");
          `DV_CHECK_RANDOMIZE_FATAL(esc_seq);
          esc_seq.start(p_sequencer.esc_device_seqr_h[j]);
        end
      join_none
    end
  endtask

  virtual task run_ping_rsp_seq_nonblocking();
    for (int i = 0; i < alert_pkg::NAlerts-1; i++) begin
      automatic int j = i;
      fork
        forever begin
          alert_sender_ping_rsp_seq ping_seq =
              alert_sender_ping_rsp_seq::type_id::create("ping_seq");
          `DV_CHECK_RANDOMIZE_FATAL(ping_seq);
          ping_seq.start(p_sequencer.alert_host_seqr_h[j]);
        end
      join_none
    end
  endtask

endclass : alert_handler_base_vseq
