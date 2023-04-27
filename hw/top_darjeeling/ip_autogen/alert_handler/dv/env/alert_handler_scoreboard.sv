// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define ASSIGN_CLASS_PHASE_REGS(index, i) \
  reg_esc_phase_cycs_per_class_q[``index``] = \
      {ral.class``i``_phase0_cyc_shadowed, ral.class``i``_phase1_cyc_shadowed, \
       ral.class``i``_phase2_cyc_shadowed, ral.class``i``_phase3_cyc_shadowed};

class alert_handler_scoreboard extends cip_base_scoreboard #(
    .CFG_T(alert_handler_env_cfg),
    .RAL_T(alert_handler_reg_block),
    .COV_T(alert_handler_env_cov)
  );
  `uvm_component_utils(alert_handler_scoreboard)

  // esc_phase_cyc_per_class_q: each class has four phase cycles, stores each cycle length
  // --- class --- phase0_cyc    ---    phase1_cyc   ---    phase2_cyc   ---     phase3_cyc  ---
  // ---   A   -classa_phase0_cyc - classa_phase1_cyc - classa_phase2_cyc - classa_phase3_cyc --
  // ---   B   -classb_phase0_cyc - classb_phase1_cyc - classb_phase2_cyc - classb_phase3_cyc --
  // ---   C   -classc_phase0_cyc - classc_phase1_cyc - classc_phase2_cyc - classc_phase3_cyc --
  // ---   D   -classd_phase0_cyc - classd_phase1_cyc - classd_phase2_cyc - classd_phase3_cyc --
  dv_base_reg   reg_esc_phase_cycs_per_class_q[NUM_ALERT_CLASSES][$];

  uvm_reg_field intr_state_fields[$];
  uvm_reg_field intr_state_field;
  // once escalation triggers, no alerts can trigger another escalation in the same class
  // until the class esc is cleared
  bit [NUM_ALERT_CLASSES-1:0] under_esc_classes;
  bit [NUM_ALERT_CLASSES-1:0] under_intr_classes;
  bit [NUM_ALERT_CLASSES-1:0] clr_esc_under_intr;
  int intr_cnter_per_class    [NUM_ALERT_CLASSES];
  int accum_cnter_per_class   [NUM_ALERT_CLASSES];
  esc_state_e state_per_class [NUM_ALERT_CLASSES];
  int  esc_signal_release  [NUM_ESC_SIGNALS];
  int  esc_sig_class       [NUM_ESC_SIGNALS]; // one class can increment one esc signal at a time
  // For different alert classify in the same class and trigger at the same cycle, design only
  // count once. So record the alert triggered timing here
  realtime last_triggered_alert_per_class[NUM_ALERT_CLASSES];

  string class_name[] = {"a", "b", "c", "d"};
  bit [TL_DW-1:0] intr_state_val;

  bit [NUM_ALERT_CLASSES-1:0] crashdump_triggered = 0;

  bit ping_timer_en;

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(alert_esc_seq_item) alert_fifo[NUM_ALERTS];
  uvm_tlm_analysis_fifo #(alert_esc_seq_item) esc_fifo[NUM_ESCS];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ral.intr_state.get_fields(intr_state_fields);
    `ASSIGN_CLASS_PHASE_REGS(0, a)
    `ASSIGN_CLASS_PHASE_REGS(1, b)
    `ASSIGN_CLASS_PHASE_REGS(2, c)
    `ASSIGN_CLASS_PHASE_REGS(3, d)

    foreach (alert_fifo[i]) alert_fifo[i] = new($sformatf("alert_fifo[%0d]", i), this);
    foreach (esc_fifo[i])   esc_fifo[i]   = new($sformatf("esc_fifo[%0d]"  , i), this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_alert_fifo();
      process_esc_fifo();
      process_edn_fifos();
      check_ping_timer();
      check_crashdump();
      check_intr_timeout_trigger_esc();
      esc_phase_signal_cnter();
      release_esc_signal();
    join_none
  endtask

  virtual task process_alert_fifo();
    foreach (alert_fifo[i]) begin
      automatic int index = i;
      automatic int lpg_index = alert_handler_reg_pkg::LpgMap[index];
      fork
        forever begin
          bit alert_en, loc_alert_en;
          alert_esc_seq_item act_item;
          alert_fifo[index].get(act_item);
          alert_en = ral.alert_en_shadowed[index].get_mirrored_value() &&
              prim_mubi_pkg::mubi4_test_false_loose(cfg.alert_handler_vif.lpg_cg_en[lpg_index]) &&
              prim_mubi_pkg::mubi4_test_false_loose(cfg.alert_handler_vif.lpg_rst_en[lpg_index]);

          // Check that ping mechanism will only ping alerts that have been enabled and locked.
          if (act_item.alert_esc_type == AlertEscPingTrans) begin
            `DV_CHECK(alert_en, $sformatf("alert %0s ping triggered but not enabled", index))
            `DV_CHECK((`gmv(ral.alert_regwen[index]) == 0),
                      $sformatf("alert %0s ping triggered but not locked", index))
          end

          if (alert_en) begin
            // alert detected
            if (act_item.alert_esc_type == AlertEscSigTrans && !act_item.ping_timeout &&
                act_item.alert_handshake_sta == AlertReceived) begin
              process_alert_sig(index, 0);
            // alert integrity fail
            end else if (act_item.alert_esc_type == AlertEscIntFail) begin
              loc_alert_en = ral.loc_alert_en_shadowed[LocalAlertIntFail].get_mirrored_value();
              if (loc_alert_en) process_alert_sig(index, 1, LocalAlertIntFail);
            end else if (act_item.alert_esc_type == AlertEscPingTrans &&
                         act_item.ping_timeout) begin
              loc_alert_en = ral.loc_alert_en_shadowed[LocalAlertPingFail].get_mirrored_value();
              if (loc_alert_en) begin
                process_alert_sig(index, 1, LocalAlertPingFail);
                `uvm_info(`gfn, $sformatf("alert %0d ping timeout, timeout_cyc reg is %0d",
                          index, ral.ping_timeout_cyc_shadowed.get_mirrored_value()), UVM_LOW);
              end
            end
          end
        end
      join_none
    end
  endtask : process_alert_fifo

  virtual task process_esc_fifo();
    foreach (esc_fifo[i]) begin
      automatic int index = i;
      fork
        forever begin
          alert_esc_seq_item act_item;
          esc_fifo[index].get(act_item);
          // escalation triggered, check signal length
          if (act_item.alert_esc_type == AlertEscSigTrans &&
              act_item.esc_handshake_sta == EscRespComplete) begin
            check_esc_signal(act_item.sig_cycle_cnt, index);
          // escalation integrity fail
          end else if (act_item.alert_esc_type == AlertEscIntFail ||
               (act_item.esc_handshake_sta == EscIntFail && !act_item.ping_timeout)) begin
            bit loc_alert_en = ral.loc_alert_en_shadowed[LocalEscIntFail].get_mirrored_value();
            if (loc_alert_en) process_alert_sig(index, 1, LocalEscIntFail);
          // escalation ping timeout
          end else if (act_item.alert_esc_type == AlertEscPingTrans) begin
            if (act_item.ping_timeout) begin
              bit loc_alert_en = ral.loc_alert_en_shadowed[LocalEscPingFail].get_mirrored_value();
              if (loc_alert_en) begin
                process_alert_sig(index, 1, LocalEscPingFail);
                `uvm_info(`gfn, $sformatf("esc %0d ping timeout, timeout_cyc reg is %0d",
                          index, ral.ping_timeout_cyc_shadowed.get_mirrored_value()), UVM_LOW);
              end
            end
          end
        end
      join_none
    end
  endtask : process_esc_fifo

  // Alert_handler ping timer is designed to fetch EDN value periodically.
  virtual task process_edn_fifos();
    fork begin: isolation_fork
      int num_edn_reqs;
      forever begin
        wait (cfg.under_reset == 0);
        fork
          begin
             check_edn_request_cycles();
             num_edn_reqs++;
            if (cfg.en_cov) cov.num_edn_reqs_cg.sample(num_edn_reqs);
          end
          begin
            wait (cfg.under_reset == 1);
            num_edn_reqs = 0;
          end
        join_any
        disable fork;
      end
    end join
  endtask

  virtual task check_edn_request_cycles();
    int edn_wait_cycles;
    fork
      begin : isolation_fork
        fork
          begin
            while (edn_wait_cycles < MAX_EDN_REQ_WAIT_CYCLES) begin
              cfg.clk_rst_vif.wait_clks(1);
              edn_wait_cycles++;
            end
            `uvm_error(`gfn, "Timeout occured waiting for an EDN request!");
          end
          begin
            push_pull_item#(.DeviceDataWidth(EDN_DATA_WIDTH)) edn_item;
            edn_fifos[0].get(edn_item);
          end
        join_any
        disable fork;
      end
    join
  endtask

  // this task process alert signal by checking if intergrity fail, then classify it to the
  // mapping classes, then check if escalation is triggered by accumulation
  // this task delayed to a negedge clk to avoid updating and checking regs at the same time
  virtual task process_alert_sig(int alert_i, bit is_int_err,
                                 local_alert_type_e local_alert_type = LocalAlertIntFail);
    fork
      begin
        cfg.clk_rst_vif.wait_n_clks(1);
        if (!under_reset) begin
          bit [TL_DW-1:0] intr_en, class_ctrl;
          bit [NUM_ALERT_CLASS_MSB:0] class_i;
          if (!is_int_err) begin
            class_i = `gmv(ral.alert_class_shadowed[alert_i]);
            void'(ral.alert_cause[alert_i].predict(1));
            if (cfg.en_cov) cov.alert_cause_cg.sample(alert_i, class_i);
          end else begin
            class_i = `gmv(ral.loc_alert_class_shadowed[int'(local_alert_type)]);
            void'(ral.loc_alert_cause[int'(local_alert_type)].predict(
                .value(1), .kind(UVM_PREDICT_READ)));
            if (cfg.en_cov) begin
              if (local_alert_type inside {LocalAlertPingFail, LocalAlertIntFail}) begin
                cov.alert_loc_alert_cause_cg.sample(local_alert_type, alert_i, class_i);
              end else begin
                cov.esc_loc_alert_cause_cg.sample(local_alert_type, alert_i, class_i);
              end
            end
          end

          intr_state_field = intr_state_fields[class_i];
          void'(intr_state_field.predict(.value(1), .kind(UVM_PREDICT_READ)));
          intr_en = ral.intr_enable.get_mirrored_value();

          // calculate escalation
          class_ctrl = get_class_ctrl(class_i);
          `uvm_info(`gfn, $sformatf("class %0d is triggered, class ctrl=%0h, under_esc=%0b",
                                    class_i, class_ctrl, under_esc_classes[class_i]), UVM_DEBUG)
          // if class escalation is enabled, add alert to accumulation count
          if (class_ctrl[AlertClassCtrlEn] &&
              (class_ctrl[AlertClassCtrlEnE3:AlertClassCtrlEnE0] > 0)) begin
            alert_accum_cal(class_i);
          end

          // according to issue #841, interrupt will have one clock cycle delay
          // add an extra cycle for synchronizers from clk_edn to clk
          cfg.clk_rst_vif.wait_n_clks(1);
          if (!under_reset) begin
            `DV_CHECK_CASE_EQ(cfg.intr_vif.pins[class_i], intr_en[class_i],
                            $sformatf("Interrupt class_%s, is_local_err %0b, local_alert_type %s",
                            class_name[class_i],is_int_err, local_alert_type));
            if (!under_intr_classes[class_i] && intr_en[class_i]) under_intr_classes[class_i] = 1;
          end
        end
      end
    join_none
  endtask

  // calculate alert accumulation count per class, if accumulation exceeds the threshold,
  // and if current class is not under escalation, then predict escalation
  // note: if more than one alerts triggered on the same clk cycle, only accumulates one
  virtual function void alert_accum_cal(int class_i);
    bit [TL_DW-1:0] accum_thresh = get_class_accum_thresh(class_i);
    realtime curr_time = $realtime();
    if (curr_time != last_triggered_alert_per_class[class_i] && !cfg.under_reset) begin
      last_triggered_alert_per_class[class_i] = curr_time;
      // avoid accum_cnt saturate
      if (accum_cnter_per_class[class_i] < 'hffff) begin
        accum_cnter_per_class[class_i] += 1;
        if (accum_cnter_per_class[class_i] > accum_thresh && !under_esc_classes[class_i]) begin
          predict_esc(class_i);
        end
      end
    end
    `uvm_info(`gfn,
              $sformatf("alert_accum: class=%0d, alert_cnt=%0d, thresh=%0d, under_esc=%0b",
              class_i, accum_cnter_per_class[class_i], accum_thresh,
              under_esc_classes[class_i]), UVM_DEBUG)
  endfunction

  // if clren register is disabled, predict escalation signals by setting the corresponding
  // under_esc_classes bit based on class_ctrl's lock bit
  virtual function void predict_esc(int class_i);
    bit [TL_DW-1:0] class_ctrl = get_class_ctrl(class_i);
    if (class_ctrl[AlertClassCtrlLock]) begin
      uvm_reg clren_rg;
      clren_rg = ral.get_reg_by_name($sformatf("class%s_clr_regwen", class_name[class_i]));
      `DV_CHECK_NE_FATAL(clren_rg, null)
      void'(clren_rg.predict(0));
    end
    under_esc_classes[class_i] = 1;
  endfunction

  // check if escalation signal's duration length is correct
  virtual function void check_esc_signal(int cycle_cnt, int esc_sig_i);
    int class_a = `gmv(ral.classa_ctrl_shadowed);
    int class_b = `gmv(ral.classb_ctrl_shadowed);
    int class_c = `gmv(ral.classc_ctrl_shadowed);
    int class_d = `gmv(ral.classd_ctrl_shadowed);
    int sig_index = AlertClassCtrlEnE0+esc_sig_i;
    bit [NUM_ALERT_CLASSES-1:0] select_class = {class_d[sig_index], class_c[sig_index],
                                                class_b[sig_index], class_a[sig_index]};


    // Only compare the escalation signal length if exactly one class is assigned to this signal.
    // Otherwise scb cannot predict the accurate cycle length if multiple classes are merged.
    if ($countones(select_class) == 1) begin
      int exp_cycle, phase, class_i;
      // Find the class that triggers the escalation, and find which phase the escalation signal is
      // reflecting.
      for (class_i = 0; class_i < NUM_ALERT_CLASSES; class_i++) begin
        if (select_class[class_i] == 1) begin
          phase = `gmv(ral.get_reg_by_name($sformatf("class%0s_ctrl_shadowed",
                                                     class_name[class_i])));
          break;
        end
      end
      phase = phase[(AlertClassCtrlMapE0 + esc_sig_i * 2) +: 2];
      exp_cycle = `gmv(ral.get_reg_by_name($sformatf("class%0s_phase%0d_cyc_shadowed",
                       class_name[class_i], phase))) + 1;
      // Minimal phase length is 2 cycles.
      exp_cycle = exp_cycle < 2 ? 2 : exp_cycle;
      `uvm_info(`gfn, $sformatf("esc_signal_%0d, esc phase %0d, esc class %0d",
                esc_sig_i, phase, class_i), UVM_HIGH);

      // If the escalation signal is interrupted by reset or esc_clear, we expect the signal length
      // to be shorter than the phase_cycle_length.
      if (cfg.under_reset || under_esc_classes[class_i] == 0) begin
        `DV_CHECK_LE(cycle_cnt, exp_cycle)
      end else begin
        `DV_CHECK_EQ(cycle_cnt, exp_cycle)
      end
      if (cfg.en_cov) cov.esc_sig_length_cg.sample(esc_sig_i, cycle_cnt);
    end
    esc_sig_class[esc_sig_i] = 0;
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg        csr;
    dv_base_reg    dv_base_csr;
    bit            do_read_check   = 1'b1;
    bit            write           = item.is_write();
    uvm_reg_addr_t csr_addr = {item.a_addr[TL_AW-1:2], 2'b00};

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
      `downcast(dv_base_csr, csr)
    end
    if (csr == null) begin
      // we hit an oob addr - expect error response and return
      `DV_CHECK_EQ(item.d_error, 1'b1)
      return;
    end

    if (channel == AddrChannel) begin
      // if incoming access is a write to a valid csr, then make updates right away
      if (write) begin
        string csr_name = csr.get_name();
        void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
        // process the csr req
        // for write, update local variable and fifo at address phase
        case (csr_name)
          // add individual case item for each csr
          "intr_test": begin
            bit [TL_DW-1:0] intr_state_exp = item.a_data | ral.intr_state.get_mirrored_value();
            if (cfg.en_cov) begin
              bit [TL_DW-1:0] intr_en = ral.intr_enable.get_mirrored_value();
              for (int i = 0; i < NUM_ALERT_CLASSES; i++) begin
                cov.intr_test_cg.sample(i, item.a_data[i], intr_en[i], intr_state_exp[i]);
              end
            end
            void'(ral.intr_state.predict(.value(intr_state_exp), .kind(UVM_PREDICT_DIRECT)));
          end
          // disable intr_enable or clear intr_state will clear the interrupt timeout cnter
          "intr_state": begin
            fork
              begin
                // after interrupt is set, it needs one clock cycle to update the value and stop
                // the intr_timeout counter
                cfg.clk_rst_vif.wait_clks(1);
                if (!cfg.under_reset) begin
                  foreach (under_intr_classes[i]) begin
                    if (item.a_data[i]) begin
                      under_intr_classes[i] = 0;
                      clr_esc_under_intr[i] = 0;
                      if (!under_esc_classes[i]) state_per_class[i] = EscStateIdle;
                    end
                  end
                  void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE),
                                    .be(item.a_mask)));
                end
              end
            join_none
          end
          "intr_enable": begin
            foreach (under_intr_classes[i]) begin
              if (item.a_data[i] == 0) under_intr_classes[i] = 0;
            end
          end
          "classa_clr_shadowed": begin
            if (!dv_base_csr.is_staged() && ral.classa_clr_regwen.get_mirrored_value()) begin
              clr_reset_esc_class(0);
            end
          end
          "classb_clr_shadowed": begin
            if (!dv_base_csr.is_staged() && ral.classb_clr_regwen.get_mirrored_value()) begin
              clr_reset_esc_class(1);
            end
          end
          "classc_clr_shadowed": begin
            if (!dv_base_csr.is_staged() && ral.classc_clr_regwen.get_mirrored_value()) begin
              clr_reset_esc_class(2);
            end
          end
          "classd_clr_shadowed": begin
            if (!dv_base_csr.is_staged() && ral.classd_clr_regwen.get_mirrored_value()) begin
              clr_reset_esc_class(3);
            end
          end
          "ping_timer_en_shadowed": begin
            if (shadowed_reg_wr_completed(dv_base_csr) &&
                item.a_data &&
                `gmv(ral.ping_timer_regwen)) begin
              ping_timer_en = 1;
            end
          end
         "alert_test", "ping_timeout_cyc_shadowed", "ping_timer_regwen": begin
            // Do nothing. Already auto update mirrored value.
          end
          default: begin
            // The following regs only need to auto update mirrored value.
            if (!uvm_re_match("*alert_en_shadowed*", csr_name) ||
                !uvm_re_match("*alert_class_shadowed*", csr_name) ||
                !uvm_re_match("class*_ctrl_shadowed", csr_name) ||
                !uvm_re_match("class*_crashdump_trigger_shadowed", csr_name) ||
                !uvm_re_match("class*_phase*_cyc_shadowed", csr_name) ||
                !uvm_re_match("class*_timeout_cyc_shadowed", csr_name) ||
                !uvm_re_match("class*_accum_thresh_shadowed", csr_name) ||
                !uvm_re_match("class*_clr_regwen", csr_name) ||
                !uvm_re_match("class*_regwen", csr_name) ||
                !uvm_re_match("*alert_regwen_*", csr_name)) begin
            end else begin
              `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
            end
          end
        endcase
      end
    end

    // process the csr req
    // for read, update predication at address phase and compare at data phase

    if (!write) begin
      // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
      if (channel == DataChannel) begin
        if (cfg.en_cov) begin
          if (csr.get_name() == "intr_state") begin
            bit [TL_DW-1:0] intr_en = ral.intr_enable.get_mirrored_value();
            for (int i = 0; i < NUM_ALERT_CLASSES; i++) begin
              cov.intr_cg.sample(i, intr_en[i], item.d_data[i]);
              cov.intr_pins_cg.sample(i, cfg.intr_vif.pins[i]);
            end
          end else begin
            for (int i = 0; i < NUM_ALERT_CLASSES; i++) begin
              if (csr.get_name() == $sformatf("class%s_accum_cnt", class_name[i])) begin
                cov.accum_cnt_cg.sample(i, item.d_data);
              end
            end
          end
        end
        if (csr.get_name == "intr_state") begin
          `DV_CHECK_EQ(intr_state_val, item.d_data, $sformatf("reg name: %0s", "intr_state"))
          do_read_check = 0;
        end
        if (do_read_check) begin
          `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                       $sformatf("reg name: %0s", csr.get_full_name()))
        end
        void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
      end else begin
        // predict in address phase to avoid the register's value changed during the read
        for (int i = 0; i < NUM_ALERT_CLASSES; i++) begin
          if (csr.get_name() == $sformatf("class%s_esc_cnt", class_name[i])) begin
            void'(csr.predict(.value(intr_cnter_per_class[i]), .kind(UVM_PREDICT_READ)));
          end else if (csr.get_name() == $sformatf("class%s_accum_cnt", class_name[i])) begin
            void'(csr.predict(.value(accum_cnter_per_class[i]), .kind(UVM_PREDICT_READ)));
          end else if (csr.get_name() == $sformatf("class%s_state", class_name[i])) begin
            void'(csr.predict(.value(state_per_class[i]), .kind(UVM_PREDICT_READ)));
          end
        end
        if (csr.get_name() == "intr_state") intr_state_val = csr.get_mirrored_value();
      end
    end
  endtask

  virtual task check_ping_timer();
    int num_checked_pings;
    fork begin : isolation_fork
      forever begin
        wait (ping_timer_en == 1);
        fork
          begin
            wait (cfg.under_reset == 1);
            ping_timer_en = 0;
            num_checked_pings = 0;
          end
          begin
            check_ping_triggered_cycles();
            num_checked_pings++;
            if (cfg.en_cov) cov.num_checked_pings_cg.sample(num_checked_pings);
          end
        join_any
        disable fork;
      end
    end join
  endtask

  // This task checks if pings are triggered within the expected time.
  //
  // The ping timer is 16 bits so ideally we should see alert_ping -> esc_ping ->  alert_ping ...
  // with the max length of 16'hFFFF clock cycle. However alert_ping is randomly selected so we
  // can not guarantee the random alert index is valid (exists), enabld, and locked.
  // However, esc ping timer should are always expected to trigger.
  // So the max wait time is 'hFFFF*2.
  // This task also used the probed design signal instead of detected ping requests from monitor.
  // Because if esc ping request and real esc request come at the same time, design will ignore the
  // ping requests. But the probed signal will still set to 1.
  virtual task check_ping_triggered_cycles();
    int ping_wait_cycs;
    while (ping_wait_cycs <= MAX_PING_WAIT_CYCLES * 2) begin
    if (cfg.alert_handler_vif.alert_ping_reqs > 0) begin
      if (cfg.en_cov) begin
        int alert_id = $clog2(cfg.alert_handler_vif.alert_ping_reqs);
        cov.ping_with_lpg_cg_wrap[alert_id].alert_ping_with_lpg_cg.sample(
            cfg.alert_host_cfg[alert_id].en_alert_lpg);
      end
      break;
    end
    if (cfg.alert_handler_vif.esc_ping_reqs > 0) break;
      cfg.clk_rst_vif.wait_clks(1);
      ping_wait_cycs++;
    end
    if (ping_wait_cycs > MAX_PING_WAIT_CYCLES * 2) begin
      `uvm_error(`gfn, "Timeout occured waiting for a ping.");
    end
    if (cfg.en_cov) cov.cycles_between_pings_cg.sample(ping_wait_cycs);

    // Wait for ping request to finish to avoid infinite loop.
    wait (cfg.alert_handler_vif.alert_ping_reqs == 0 && cfg.alert_handler_vif.esc_ping_reqs == 0);
  endtask

  virtual task check_crashdump();
    forever begin
      wait (cfg.under_reset == 0 && cfg.en_scb == 1);
      @(cfg.crashdump_vif.pins) begin
        alert_pkg::alert_crashdump_t crashdump_val =
            alert_pkg::alert_crashdump_t'(cfg.crashdump_vif.sample());

        // Wait two negedge clock cycles to make sure csr mirrored values are updated.
        `DV_SPINWAIT_EXIT(cfg.clk_rst_vif.wait_n_clks(2);, wait (cfg.under_reset == 1);)

        if (!cfg.under_reset) begin
          // If crashdump reached the phase programmed at `crashdump_trigger_shadowed`,
          // `crashdump_o` value should keep stable until reset.
          if (crashdump_triggered) begin
            `uvm_fatal(`gfn,
                       "crashdump value should not change after trigger condition is reached!")
          end

          foreach (crashdump_val.class_esc_state[i]) begin
            uvm_reg crashdump_trigger_csr = ral.get_reg_by_name(
                    $sformatf("class%0s_crashdump_trigger_shadowed", class_name[i]));
            if (crashdump_val.class_esc_state[i] == (`gmv(crashdump_trigger_csr) + 3'b100)) begin
              crashdump_triggered[i] = 1;
              if (cfg.en_cov) cov.crashdump_trigger_cg.sample(`gmv(crashdump_trigger_csr));
              break;
             end
          end

          for (int i = 0; i < NUM_ALERTS; i++) begin
            `DV_CHECK_EQ(crashdump_val.alert_cause[i], `gmv(ral.alert_cause[i]))
          end
          for (int i = 0; i < NUM_LOCAL_ALERTS; i++) begin
            `DV_CHECK_EQ(crashdump_val.loc_alert_cause[i], `gmv(ral.loc_alert_cause[i]))
          end
        end
      end
    end
  endtask

  // a counter to count how long each interrupt pins stay high until it is being reset
  // if counter exceeds threshold, call predict_esc() function to calculate related esc
  virtual task check_intr_timeout_trigger_esc();
    for (int i = 0; i < NUM_ALERT_CLASSES; i++) begin
      fork
        automatic int class_i = i;
        begin : intr_sig_counter
          forever @(under_intr_classes[class_i] && !under_esc_classes[class_i]) begin
            fork
              begin
                bit [TL_DW-1:0] timeout_cyc, class_ctrl;
                // if escalation cleared but interrupt not cleared, wait one more clk cycle for the
                // FSM to reset to Idle, then start to count
                if (clr_esc_under_intr[class_i]) cfg.clk_rst_vif.wait_n_clks(1);
                clr_esc_under_intr[class_i] = 0;
                // wait a clk for esc signal to go high
                cfg.clk_rst_vif.wait_n_clks(1);
                class_ctrl = get_class_ctrl(class_i);
                if (class_ctrl[AlertClassCtrlEn] &&
                    class_ctrl[AlertClassCtrlEnE3:AlertClassCtrlEnE0] > 0) begin
                  intr_cnter_per_class[class_i] = 1;
                  `uvm_info(`gfn, $sformatf("Class %0d start counter", class_i), UVM_HIGH)
                  timeout_cyc = get_class_timeout_cyc(class_i);
                  if (timeout_cyc > 0) begin
                    state_per_class[class_i] = EscStateTimeout;
                    while (under_intr_classes[class_i]) begin
                      @(cfg.clk_rst_vif.cbn);
                      if (intr_cnter_per_class[class_i] >= timeout_cyc) begin
                        predict_esc(class_i);
                        if (cfg.en_cov) cov.intr_timeout_cnt_cg.sample(class_i, timeout_cyc);
                      end
                      intr_cnter_per_class[class_i] += 1;
                      `uvm_info(`gfn, $sformatf("counter_%0d value: %0d", class_i,
                                intr_cnter_per_class[class_i]), UVM_HIGH)
                    end
                  end
                  intr_cnter_per_class[class_i] = 0;
                end
              end
              begin
                wait(under_esc_classes[class_i]);
              end
            join_any
            disable fork;
          end // end forever
        end
      join_none
    end
  endtask

  // two counters for phases cycle length and esc signals cycle length
  // phase cycle cnter: "intr_cnter_per_class" is used to check "esc_cnt" registers
  virtual task esc_phase_signal_cnter();
    for (int i = 0; i < NUM_ALERT_CLASSES; i++) begin
      fork
        automatic int class_i = i;
        begin : esc_phases_counter
          forever @(!cfg.under_reset && under_esc_classes[class_i]) begin
            fork
              begin : inc_esc_cnt
                for (int phase_i = 0; phase_i < NUM_ESC_PHASES; phase_i++) begin
                  int phase_thresh = `gmv(reg_esc_phase_cycs_per_class_q[class_i][phase_i]);
                  bit[TL_DW-1:0] class_ctrl = get_class_ctrl(class_i);
                  int enabled_sig_q[$];
                  for (int sig_i = 0; sig_i < NUM_ESC_SIGNALS; sig_i++) begin
                    if (class_ctrl[sig_i*2+7 -: 2] == phase_i && class_ctrl[sig_i+2]) begin
                      enabled_sig_q.push_back(sig_i);
                    end
                  end
                  if (under_esc_classes[class_i]) begin
                    intr_cnter_per_class[class_i] = 1;
                    state_per_class[class_i] = esc_state_e'(phase_i + int'(EscStatePhase0));
                    cfg.clk_rst_vif.wait_n_clks(1);
                    while (under_esc_classes[class_i] &&
                           intr_cnter_per_class[class_i] < phase_thresh) begin
                      intr_cnter_per_class[class_i]++;
                      cfg.clk_rst_vif.wait_n_clks(1);
                    end
                    foreach (enabled_sig_q[i]) begin
                      int index = enabled_sig_q[i];
                      if (esc_sig_class[index] == (class_i + 1)) esc_signal_release[index] = 1;
                    end
                  end
                end  // end four phases
                intr_cnter_per_class[class_i] = 0;
                if (under_esc_classes[class_i]) state_per_class[class_i] = EscStateTerminal;
              end
              begin
                wait(cfg.under_reset || !under_esc_classes[class_i]);
                if (!under_esc_classes[class_i]) begin
                  // wait 1 clk cycles until esc_signal_release is set
                  cfg.clk_rst_vif.wait_clks(1);
                end
              end
            join_any
            disable fork;
            intr_cnter_per_class[class_i] = 0;
          end // end forever
        end
      join_none
    end
  endtask

  // release escalation signal after one clock cycle, to ensure happens at the end of the clock
  // cycle, waited 1 clks here
  virtual task release_esc_signal();
    for (int i = 0; i < NUM_ESC_SIGNALS; i++) begin
      fork
        automatic int sig_i = i;
        forever @ (esc_signal_release[sig_i]) begin
          cfg.clk_rst_vif.wait_clks(1);
          esc_sig_class[sig_i] = 0;
          esc_signal_release[sig_i] = 0;
        end
      join_none
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    under_intr_classes    = '{default:0};
    intr_cnter_per_class  = '{default:0};
    under_esc_classes     = '{default:0};
    esc_sig_class         = '{default:0};
    accum_cnter_per_class = '{default:0};
    state_per_class       = '{default:EscStateIdle};
    clr_esc_under_intr    = 0;
    crashdump_triggered   = 0;
    ping_timer_en         = 0;
    last_triggered_alert_per_class = '{default:$realtime};
  endfunction

  // clear accumulative counters, and escalation counters if they are under escalation
  // interrupt timeout counters cannot be cleared by this
  task clr_reset_esc_class(int i);
    fork
      automatic int class_i = i;
      begin
        cfg.clk_rst_vif.wait_clks(1);
        crashdump_triggered[class_i] = 0;
        if (under_intr_classes[class_i]) begin
          if (cfg.en_cov) cov.clear_intr_cnt_cg.sample(class_i);
          clr_esc_under_intr[class_i] = 1;
        end
        if (under_esc_classes [class_i]) begin
          if (cfg.en_cov) cov.clear_esc_cnt_cg.sample(class_i);
          intr_cnter_per_class[class_i] = 0;
        end
        under_esc_classes[class_i] = 0;
        cfg.clk_rst_vif.wait_n_clks(1);
        last_triggered_alert_per_class[class_i] = $realtime;
        accum_cnter_per_class[class_i] = 0;
        if (state_per_class[class_i] != EscStateTimeout) state_per_class[class_i] = EscStateIdle;
      end
    join_none
  endtask

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
  endfunction

  // get class_ctrl register mirrored value by class
  function bit [TL_DW-1:0] get_class_ctrl(int class_i);
    uvm_reg class_ctrl_rg;
    class_ctrl_rg = ral.get_reg_by_name($sformatf("class%s_ctrl_shadowed", class_name[class_i]));
    `DV_CHECK_NE_FATAL(class_ctrl_rg, null)
    return class_ctrl_rg.get_mirrored_value();
  endfunction

  // get class_accum_thresh register mirrored value by class
  function bit [TL_DW-1:0] get_class_accum_thresh(int class_i);
    uvm_reg class_thresh_rg;
    class_thresh_rg = ral.get_reg_by_name($sformatf("class%s_accum_thresh_shadowed",
                                                    class_name[class_i]));
    `DV_CHECK_NE_FATAL(class_thresh_rg, null)
    return class_thresh_rg.get_mirrored_value();
  endfunction

  // get class_timeout_cyc register mirrored value by class
  function bit [TL_DW-1:0] get_class_timeout_cyc(int class_i);
    dv_base_reg class_timeout_rg =
        ral.get_dv_base_reg_by_name($sformatf("class%s_timeout_cyc_shadowed",
                                              class_name[class_i]));
    return class_timeout_rg.get_mirrored_value();
  endfunction

  function bit shadowed_reg_wr_completed(dv_base_reg dv_base_reg);
    return (!dv_base_reg.is_staged() && !dv_base_reg.get_shadow_update_err());
  endfunction

endclass
`undef ASSIGN_CLASS_PHASE_REGS
