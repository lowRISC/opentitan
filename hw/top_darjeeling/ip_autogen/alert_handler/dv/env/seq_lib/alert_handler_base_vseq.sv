// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define RAND_AND_WR_CLASS_PHASES_CYCLE(i)                                 \
  `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.class``i``_phase0_cyc_shadowed,      \
      class``i``_phase0_cyc_shadowed.value inside {[0: max_phase_cyc]};); \
  `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.class``i``_phase1_cyc_shadowed,      \
      class``i``_phase1_cyc_shadowed.value inside {[0: max_phase_cyc]};); \
  `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.class``i``_phase2_cyc_shadowed,      \
      class``i``_phase2_cyc_shadowed.value inside {[0: max_phase_cyc]};); \
  `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.class``i``_phase3_cyc_shadowed,      \
      class``i``_phase3_cyc_shadowed.value inside {[0: max_phase_cyc]};); \
  csr_update(ral.class``i``_phase0_cyc_shadowed);                         \
  csr_update(ral.class``i``_phase1_cyc_shadowed);                         \
  csr_update(ral.class``i``_phase2_cyc_shadowed);                         \
  csr_update(ral.class``i``_phase3_cyc_shadowed);

`define RAND_WRITE_CLASS_CTRL(i, en_bit, lock_bit) \
  `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.class``i``_ctrl_shadowed, \
                                 en.value == en_bit; lock.value == lock_bit;)  \
  csr_wr(.ptr(ral.class``i``_ctrl_shadowed), .value(ral.class``i``_ctrl_shadowed.get()));

class alert_handler_base_vseq extends cip_base_vseq #(
    .CFG_T               (alert_handler_env_cfg),
    .RAL_T               (alert_handler_reg_block),
    .COV_T               (alert_handler_env_cov),
    .VIRTUAL_SEQUENCER_T (alert_handler_virtual_sequencer)
  );
  `uvm_object_utils(alert_handler_base_vseq)

  // various knobs to enable certain routines
  bit do_alert_handler_init = 1'b0;
  bit config_locked         = 1'b0;

  `uvm_object_new

  virtual task dut_init(string reset_kind = "HARD");
    cfg.alert_handler_vif.init();
    super.dut_init();
    if (do_alert_handler_init) alert_handler_init();
    config_locked = 0;
  endtask

  virtual task dut_shutdown();
    // nothing special yet
  endtask

  // setup basic alert_handler features
  // alert_class default 0 -> all alert will trigger interrupt classA
  virtual task alert_handler_init(
      bit [NUM_ALERT_CLASSES-1:0]                       intr_en = '1,
      bit [NUM_ALERTS-1:0]                              alert_en = '1,
      bit [NUM_ALERTS-1:0][NUM_ALERT_CLASSES-1:0]       alert_class = 'h0,
      bit [NUM_LOCAL_ALERTS-1:0]                        loc_alert_en = '1,
      bit [NUM_LOCAL_ALERTS-1:0][NUM_ALERT_CLASSES-1:0] loc_alert_class = 'h0);

    csr_wr(.ptr(ral.intr_enable), .value(intr_en));
    foreach (alert_en[i])        csr_wr(.ptr(ral.alert_en_shadowed[i]),
                                        .value(alert_en[i]));
    foreach (alert_class[i])     csr_wr(.ptr(ral.alert_class_shadowed[i]),
                                        .value(alert_class[i]));
    foreach (loc_alert_en[i])    csr_wr(.ptr(ral.loc_alert_en_shadowed[i]),
                                        .value(loc_alert_en[i]));
    foreach (loc_alert_class[i]) csr_wr(.ptr(ral.loc_alert_class_shadowed[i]),
                                        .value(loc_alert_class[i]));
  endtask

  virtual task alert_handler_rand_wr_class_ctrl(bit [NUM_ALERT_CLASSES-1:0] lock_bit,
                                                bit [NUM_ALERT_CLASSES-1:0] class_en);
    `RAND_WRITE_CLASS_CTRL(a, class_en[0], lock_bit[0])
    `RAND_WRITE_CLASS_CTRL(b, class_en[1], lock_bit[1])
    `RAND_WRITE_CLASS_CTRL(c, class_en[2], lock_bit[2])
    `RAND_WRITE_CLASS_CTRL(d, class_en[3], lock_bit[3])
  endtask

  virtual task alert_handler_wr_regwen_regs(bit [NUM_ALERT_CLASSES-1:0] regwen = 0,
                                            bit [NUM_ALERTS-1:0]        alert_regwen = 0,
                                            bit [NUM_LOCAL_ALERTS-1:0]  loc_alert_regwen = 0,
                                            bit                         ping_timer_regwen = 0,
                                            bit [NUM_ALERT_CLASSES-1:0] class_regwen = 0);

    csr_wr(.ptr(ral.classa_clr_regwen), .value(regwen[0]));
    csr_wr(.ptr(ral.classb_clr_regwen), .value(regwen[1]));
    csr_wr(.ptr(ral.classc_clr_regwen), .value(regwen[2]));
    csr_wr(.ptr(ral.classd_clr_regwen), .value(regwen[3]));

    foreach (alert_regwen[i]) csr_wr(.ptr(ral.alert_regwen[i]), .value(alert_regwen[i]));

    foreach (loc_alert_regwen[i]) begin
      csr_wr(.ptr(ral.loc_alert_regwen[i]), .value(loc_alert_regwen[i]));
    end

    csr_wr(.ptr(ral.ping_timer_regwen), .value(ping_timer_regwen));

    csr_wr(.ptr(ral.classa_regwen), .value(class_regwen[0]));
    csr_wr(.ptr(ral.classb_regwen), .value(class_regwen[1]));
    csr_wr(.ptr(ral.classc_regwen), .value(class_regwen[2]));
    csr_wr(.ptr(ral.classd_regwen), .value(class_regwen[3]));
  endtask

  // If do_lock_config is set, write value 1 to ping_timer_en register.
  // If not set, this task has 50% of chance to write value 1 to ping_timer_en register.
  virtual task lock_config(bit do_lock_config);
    if (do_lock_config || $urandom_range(0, 1)) begin
      csr_wr(.ptr(ral.ping_timer_en_shadowed), .value(do_lock_config));
    end
  endtask

  virtual task drive_alert(bit[NUM_ALERTS-1:0] alert_trigger, bit[NUM_ALERTS-1:0] alert_int_err);
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

  // This sequence will drive standalone esc_resp_p/n without esc_p/n
  virtual task drive_esc_rsp(bit [NUM_ESCS-1:0] esc_int_errs);
    fork
      begin : isolation_fork
        foreach (cfg.esc_device_cfg[i]) begin
          automatic int index = i;
          if (esc_int_errs[index]) begin
            fork
              begin
                esc_receiver_esc_rsp_seq esc_seq =
                    esc_receiver_esc_rsp_seq::type_id::create("esc_seq");
                `DV_CHECK_RANDOMIZE_WITH_FATAL(esc_seq, int_err == 1; standalone_int_err == 1;
                                               ping_timeout == 0;)
                esc_seq.start(p_sequencer.esc_device_seqr_h[index]);
              end
            join_none
          end
        end
        wait fork;
      end
    join
  endtask

  // alert_handler scb will compare the read value with expected value
  // Not using "clear_all_interrupts" function in cip_base_vseq because of the signal interity
  // error: after clearing intr_state, intr_state might come back to 1 in the next cycle.
  virtual task check_alert_interrupts();
    bit [TL_DW-1:0] intr;
    // Wait until there is no ping handshake.
    // This will avoid the case where interrupt is set and cleared at the same cycle.
    `DV_WAIT((cfg.alert_handler_vif.alert_ping_reqs || cfg.alert_handler_vif.esc_ping_reqs) == 0)
    csr_rd(.ptr(ral.intr_state), .value(intr));
    `DV_WAIT((cfg.alert_handler_vif.alert_ping_reqs || cfg.alert_handler_vif.esc_ping_reqs) == 0)
    csr_wr(.ptr(ral.intr_state), .value('1));
  endtask

  virtual task clear_esc();
    csr_wr(.ptr(ral.classa_clr_shadowed), .value(1));
    csr_wr(.ptr(ral.classb_clr_shadowed), .value(1));
    csr_wr(.ptr(ral.classc_clr_shadowed), .value(1));
    csr_wr(.ptr(ral.classd_clr_shadowed), .value(1));
  endtask

  // checking for csr_rd is done in scb
  virtual task read_alert_cause();
    bit [TL_DW-1:0] alert_cause;
    foreach (ral.alert_cause[i]) begin
      if ($urandom_range(0, 1)) begin
        csr_rd(.ptr(ral.alert_cause[i]), .value(alert_cause));
      end
    end
    foreach (ral.loc_alert_cause[i]) begin
      if ($urandom_range(0, 1)) begin
        csr_rd(.ptr(ral.loc_alert_cause[i]), .value(alert_cause));
      end
    end
  endtask

  virtual task read_esc_status();
    bit [TL_DW-1:0] csr_val;
    csr_rd(.ptr(ral.classa_accum_cnt), .value(csr_val));
    csr_rd(.ptr(ral.classb_accum_cnt), .value(csr_val));
    csr_rd(.ptr(ral.classc_accum_cnt), .value(csr_val));
    csr_rd(.ptr(ral.classd_accum_cnt), .value(csr_val));

    csr_rd(.ptr(ral.classa_state), .value(csr_val));
    csr_rd(.ptr(ral.classb_state), .value(csr_val));
    csr_rd(.ptr(ral.classc_state), .value(csr_val));
    csr_rd(.ptr(ral.classd_state), .value(csr_val));

    csr_rd(.ptr(ral.classa_esc_cnt), .value(csr_val));
    csr_rd(.ptr(ral.classb_esc_cnt), .value(csr_val));
    csr_rd(.ptr(ral.classc_esc_cnt), .value(csr_val));
    csr_rd(.ptr(ral.classd_esc_cnt), .value(csr_val));
  endtask

  virtual task wait_alert_handshake_done();
    cfg.clk_rst_vif.wait_clks(2);
    foreach (cfg.alert_host_cfg[i]) begin
      if (!cfg.alert_host_cfg[i].en_alert_lpg) cfg.alert_host_cfg[i].vif.wait_ack_complete();
    end
  endtask

  virtual function bit check_esc_done(bit[TL_DW-1:0] vals[$]);
    foreach (vals[i]) begin
      esc_state_e val = esc_state_e'(vals[i]);
      if (val inside {EscStatePhase0, EscStatePhase1, EscStatePhase2, EscStatePhase3}) return 0;
    end
    return 1;
  endfunction

  virtual task wait_esc_handshake_done();
    bit [TL_DW-1:0] csr_vals[4];
    do begin
      csr_rd(.ptr(ral.classa_state), .value(csr_vals[0]));
      csr_rd(.ptr(ral.classb_state), .value(csr_vals[1]));
      csr_rd(.ptr(ral.classc_state), .value(csr_vals[2]));
      csr_rd(.ptr(ral.classd_state), .value(csr_vals[3]));
    end while (!check_esc_done(csr_vals));
    // check if there is any esc ping
    foreach (cfg.esc_device_cfg[i]) cfg.esc_device_cfg[i].vif.wait_esc_complete();
  endtask

  // This task wait until any alert or esc protocol received a ping from LFSR.
  // This task will also return the protocol index:
  // alert index starts from 1; esc index stats from NUM_ALERTS
  virtual task wait_alert_esc_ping(ref int ping_index);
    int ping_i;
    fork
      begin : isolation_fork
        foreach (cfg.alert_host_cfg[i]) begin
          automatic int index = i;
          fork
            begin
              cfg.alert_host_cfg[index].vif.wait_alert_ping();
              ping_i = index + 1;
            end
          join_none
        end
        foreach (cfg.esc_device_cfg[i]) begin
          automatic int index = i;
          fork
            begin
              cfg.esc_device_cfg[index].vif.wait_esc_ping();
              ping_i = index + NUM_ALERTS + 1;
            end
          join_none
        end
        wait (ping_i > 0);
        disable fork;
        ping_index = ping_i;
      end
    join
  endtask

  function void enable_lpg_group(bit [NUM_ALERTS-1:0] alert_en_i);
    foreach (alert_en_i[i]) begin
      if (alert_en_i[i]) set_alert_lpg(i);
    end
  endfunction

  // Enable alert's LPG based on alert_i input.
  //
  // Only enable this alert's LPG if the lgp input `lpg_cg_en` or `lpg_rst_en` if not Mubi4True.
  // Because one LPG will turn off a set of alert sensers. So this task will also set all LPG's
  // alert_host_cfgs' `en_alert_lpg` to 1.
  virtual function void set_alert_lpg(int alert_i);
    int       lpg_i = alert_handler_reg_pkg::LpgMap[alert_i];
    bit [1:0] set_lpg;

    if (cfg.alert_handler_vif.get_lpg_status(lpg_i) == 0) begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(set_lpg, set_lpg > 0;);
      if (set_lpg[0]) cfg.alert_handler_vif.set_lpg_cg_en(lpg_i);
      if (set_lpg[1]) cfg.alert_handler_vif.set_lpg_rst_en(lpg_i);
      foreach (alert_handler_reg_pkg::LpgMap[i]) begin
        if (alert_handler_reg_pkg::LpgMap[i] == lpg_i) cfg.alert_host_cfg[i].en_alert_lpg = 1;
      end
    end
  endfunction

  virtual task alert_handler_crashdump_phases(bit [1:0] classa_phase = $urandom(),
                                              bit [1:0] classb_phase = $urandom(),
                                              bit [1:0] classc_phase = $urandom(),
                                              bit [1:0] classd_phase = $urandom());
    csr_wr(.ptr(ral.classa_crashdump_trigger_shadowed), .value(classa_phase));
    csr_wr(.ptr(ral.classb_crashdump_trigger_shadowed), .value(classb_phase));
    csr_wr(.ptr(ral.classc_crashdump_trigger_shadowed), .value(classc_phase));
    csr_wr(.ptr(ral.classd_crashdump_trigger_shadowed), .value(classd_phase));
  endtask

  virtual task wr_phases_cycle(int max_phase_cyc);
    `RAND_AND_WR_CLASS_PHASES_CYCLE(a);
    `RAND_AND_WR_CLASS_PHASES_CYCLE(b);
    `RAND_AND_WR_CLASS_PHASES_CYCLE(c);
    `RAND_AND_WR_CLASS_PHASES_CYCLE(d);
  endtask

  virtual task wr_intr_timeout_cycle(bit[TL_DW-1:0] intr_timeout_cyc[NUM_ALERT_CLASSES]);
    csr_wr(.ptr(ral.classa_timeout_cyc_shadowed), .value(intr_timeout_cyc[0]));
    csr_wr(.ptr(ral.classb_timeout_cyc_shadowed), .value(intr_timeout_cyc[1]));
    csr_wr(.ptr(ral.classc_timeout_cyc_shadowed), .value(intr_timeout_cyc[2]));
    csr_wr(.ptr(ral.classd_timeout_cyc_shadowed), .value(intr_timeout_cyc[3]));
  endtask

  virtual task wr_class_accum_threshold(bit[TL_DW-1:0] accum_thresh[NUM_ALERT_CLASSES]);
    csr_wr(.ptr(ral.classa_accum_thresh_shadowed), .value(accum_thresh[0]));
    csr_wr(.ptr(ral.classb_accum_thresh_shadowed), .value(accum_thresh[1]));
    csr_wr(.ptr(ral.classc_accum_thresh_shadowed), .value(accum_thresh[2]));
    csr_wr(.ptr(ral.classd_accum_thresh_shadowed), .value(accum_thresh[3]));
  endtask

  virtual task wr_ping_timeout_cycle(bit[TL_DW-1:0] timeout_val);
    csr_wr(.ptr(ral.ping_timeout_cyc_shadowed), .value(timeout_val));
    if (`gmv(ral.ping_timer_regwen)) begin
      if (timeout_val == 0) timeout_val = 1;
      foreach (cfg.alert_host_cfg[i]) cfg.alert_host_cfg[i].ping_timeout_cycle = timeout_val;
      foreach (cfg.esc_device_cfg[i]) cfg.esc_device_cfg[i].ping_timeout_cycle = timeout_val;
    end
  endtask

  // This sequence will automatically response to all escalation ping and esc responses
  virtual task run_esc_rsp_seq_nonblocking(bit [NUM_ESCS-1:0] esc_int_errs = '0,
                                           bit [NUM_ESCS-1:0] ping_timeout_errs = '0);
    foreach (cfg.esc_device_cfg[i]) begin
      automatic int index = i;
      fork
        forever begin
          bit esc_int_err      = esc_int_errs[index]      ? $urandom_range(0, 1) : 0;
          bit ping_timeout_err = ping_timeout_errs[index] ? $urandom_range(0, 1) : 0;
          esc_receiver_esc_rsp_seq esc_seq =
              esc_receiver_esc_rsp_seq::type_id::create("esc_seq");
          `DV_CHECK_RANDOMIZE_WITH_FATAL(esc_seq, int_err == esc_int_err; standalone_int_err == 0;
                                         ping_timeout == ping_timeout_err;)
          esc_seq.start(p_sequencer.esc_device_seqr_h[index]);
        end
      join_none
    end
  endtask

endclass : alert_handler_base_vseq

`undef RAND_AND_WR_CLASS_PHASES_CYCLE
`undef RAND_WRITE_CLASS_CTRL
