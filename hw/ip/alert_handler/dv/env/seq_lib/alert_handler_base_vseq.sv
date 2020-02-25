// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define RAND_AND_WR_CLASS_PHASES_CYCLE(i) \
  `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.class``i``_phase0_cyc, \
                                 class``i``_phase0_cyc.value inside {[0: max_phase_cyc]};); \
  `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.class``i``_phase1_cyc, \
                                 class``i``_phase1_cyc.value inside {[0: max_phase_cyc]};); \
  `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.class``i``_phase2_cyc, \
                                 class``i``_phase2_cyc.value inside {[0: max_phase_cyc]};); \
  `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.class``i``_phase3_cyc, \
                                 class``i``_phase3_cyc.value inside {[0: max_phase_cyc]};); \
  csr_update(ral.class``i``_phase0_cyc); \
  csr_update(ral.class``i``_phase1_cyc); \
  csr_update(ral.class``i``_phase2_cyc); \
  csr_update(ral.class``i``_phase3_cyc);

`define RAND_WRITE_CLASS_CTRL(i) \
  `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.class``i``_ctrl, lock.value == 1'b0;) \
  csr_wr(.csr(ral.class``i``_ctrl), .value(ral.class``i``_ctrl.get()));

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
  // alert_class default 0 -> all alert willtrigger interrupt classA
  virtual task alert_handler_init(bit [NUM_ALERT_HANDLER_CLASSES-1:0] intr_en = '1,
                                  bit [alert_pkg::NAlerts-1:0]        alert_en = '1,
                                  bit [TL_DW-1:0]                     alert_class = 'h0,
                                  bit [NUM_LOCAL_ALERT-1:0]           loc_alert_en = '1,
                                  bit [TL_DW-1:0]                     loc_alert_class = 'h0);
    csr_wr(.csr(ral.intr_enable), .value(intr_en));
    csr_wr(.csr(ral.alert_en), .value(alert_en));
    csr_wr(.csr(ral.alert_class), .value(alert_class));
    csr_wr(.csr(ral.loc_alert_en), .value(loc_alert_en));
    csr_wr(.csr(ral.loc_alert_class), .value(loc_alert_class));
  endtask

  virtual task alert_handle_rand_wr_class_ctrl(bit [NUM_ALERT_HANDLER_CLASSES-1:0] class_en =
                                               $urandom());
    if (class_en[0]) `RAND_WRITE_CLASS_CTRL(a)
    if (class_en[1]) `RAND_WRITE_CLASS_CTRL(b)
    if (class_en[2]) `RAND_WRITE_CLASS_CTRL(c)
    if (class_en[3]) `RAND_WRITE_CLASS_CTRL(d)
  endtask

  virtual task drive_alert(bit[alert_pkg::NAlerts-1:0] alert_trigger,
                           bit[alert_pkg::NAlerts-1:0] alert_int_err);
    fork
      begin : isolation_fork
        foreach (alert_trigger[i]) begin
          if (alert_trigger[i]) begin
            automatic int index = i;
            fork
              begin
                alert_sender_seq alert_seq;
                `uvm_create_on(alert_seq, p_sequencer.alert_host_seqr_h[index]);
                `DV_CHECK_RANDOMIZE_WITH_FATAL(alert_seq, int_err == alert_int_err[index];)
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
    csr_wr(.csr(ral.classb_clr), .value(1));
    csr_wr(.csr(ral.classc_clr), .value(1));
    csr_wr(.csr(ral.classd_clr), .value(1));
  endtask

  virtual task read_alert_cause();
    bit [TL_DW-1:0] alert_cause;
    // checking for this CSR is done in scb
    csr_rd(.ptr(ral.alert_cause), .value(alert_cause));
    csr_rd(.ptr(ral.loc_alert_cause), .value(alert_cause));
  endtask

  virtual task read_esc_status();
    bit [TL_DW-1:0] accum_cnt;
    csr_rd(.ptr(ral.classa_accum_cnt), .value(accum_cnt));
    csr_rd(.ptr(ral.classb_accum_cnt), .value(accum_cnt));
    csr_rd(.ptr(ral.classc_accum_cnt), .value(accum_cnt));
    csr_rd(.ptr(ral.classd_accum_cnt), .value(accum_cnt));
  endtask

  virtual task wait_alert_esc_handshake_done(int wait_clk_cycs_esc);
    cfg.clk_rst_vif.wait_clks(2);
    foreach (cfg.alert_host_cfg[i]) cfg.alert_host_cfg[i].vif.wait_ack_complete();

    cfg.clk_rst_vif.wait_clks(wait_clk_cycs_esc);
    foreach (cfg.esc_device_cfg[i]) cfg.esc_device_cfg[i].vif.wait_esc_complete();
  endtask

  virtual task wr_phases_cycle(int max_phase_cyc);
    `RAND_AND_WR_CLASS_PHASES_CYCLE(a);
    `RAND_AND_WR_CLASS_PHASES_CYCLE(b);
    `RAND_AND_WR_CLASS_PHASES_CYCLE(c);
    `RAND_AND_WR_CLASS_PHASES_CYCLE(d);
  endtask

  virtual task wr_intr_timeout_cycle(bit[TL_DW-1:0] intr_timeout_cyc[NUM_ALERT_HANDLER_CLASSES]);
    csr_wr(.csr(ral.classa_timeout_cyc), .value(intr_timeout_cyc[0]));
    csr_wr(.csr(ral.classb_timeout_cyc), .value(intr_timeout_cyc[1]));
    csr_wr(.csr(ral.classc_timeout_cyc), .value(intr_timeout_cyc[2]));
    csr_wr(.csr(ral.classd_timeout_cyc), .value(intr_timeout_cyc[3]));
  endtask

  virtual task wr_class_accum_threshold(bit[TL_DW-1:0] accum_thresh[NUM_ALERT_HANDLER_CLASSES]);
    csr_wr(.csr(ral.classa_accum_thresh), .value(accum_thresh[0]));
    csr_wr(.csr(ral.classb_accum_thresh), .value(accum_thresh[1]));
    csr_wr(.csr(ral.classc_accum_thresh), .value(accum_thresh[2]));
    csr_wr(.csr(ral.classd_accum_thresh), .value(accum_thresh[3]));
  endtask

  virtual task run_esc_rsp_seq_nonblocking();
    foreach (cfg.esc_device_cfg[i]) begin
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
    foreach (cfg.alert_host_cfg[i]) begin
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

`undef RAND_AND_WR_CLASS_PHASES_CYCLE
`undef RAND_WRITE_CLASS_CTRL
