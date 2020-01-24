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
  // alert_class default 0 -> all alert will trigger interrupt classA
  virtual task alert_handler_init(bit [NUM_ALERT_HANDLER_CLASSES-1:0] intr_en = '1,
                                  bit [alert_pkg::NAlerts-1:0]        alert_en = '1,
                                  bit [TL_DW-1:0]                     alert_class = 'h0,
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

  virtual task drive_alert(bit[alert_pkg::NAlerts-1:0] alert_trigger);
    fork
      begin : isolation_fork
        foreach (alert_trigger[i]) begin
          if (alert_trigger[i]) begin
            automatic int index = i;
            fork
              begin
                alert_sender_seq alert_seq;
                `uvm_create_on(alert_seq, p_sequencer.alert_host_seqr_h[index]);
                `DV_CHECK_RANDOMIZE_FATAL(alert_seq)
                `uvm_send(alert_seq)
              end
            join_none
          end
        end
        wait fork;
      end
    join
  endtask

  virtual task clear_esc();
    csr_wr(.csr(ral.classa_clr), .value(1));
  endtask

  virtual task read_alert_cause();
    bit [TL_DW-1:0] alert_cause;
    // checking for this CSR is done in scb
    csr_rd(.ptr(ral.alert_cause), .value(alert_cause));
  endtask

  virtual task run_esc_rsp_seq_nonblocking();
    foreach(cfg.esc_device_cfg[i]) begin
      automatic int index = i;
      fork
        forever begin
          esc_receiver_esc_rsp_seq esc_seq =
              esc_receiver_esc_rsp_seq::type_id::create("esc_seq");
          `DV_CHECK_RANDOMIZE_FATAL(esc_seq);
          esc_seq.start(p_sequencer.esc_device_seqr_h[index]);
        end
      join_none
    end
  endtask

  virtual task run_ping_rsp_seq_nonblocking();
    foreach(cfg.alert_host_cfg[i]) begin
      automatic int index = i;
      fork
        forever begin
          alert_sender_ping_rsp_seq ping_seq =
              alert_sender_ping_rsp_seq::type_id::create("ping_seq");
          `DV_CHECK_RANDOMIZE_FATAL(ping_seq);
          ping_seq.start(p_sequencer.alert_host_seqr_h[i]);
        end
      join_none
    end
  endtask

endclass : alert_handler_base_vseq
