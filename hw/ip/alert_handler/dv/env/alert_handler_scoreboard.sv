// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define ASSIGN_CLASS_PHASE_REGS(index, i) \
  reg_esc_phase_cycs_per_class_q[``index``] = \
      {ral.class``i``_phase0_cyc, ral.class``i``_phase1_cyc, \
       ral.class``i``_phase2_cyc, ral.class``i``_phase3_cyc};

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
  dv_base_reg   reg_esc_phase_cycs_per_class_q[NUM_ALERT_HANDLER_CLASSES][$];

  uvm_reg_field alert_cause_fields[$];
  uvm_reg_field intr_state_fields[$];
  uvm_reg_field loc_alert_cause_fields[$];
  uvm_reg_field alert_cause_field, intr_state_field, loc_alert_cause_field;
  // once escalation triggers, no alerts can trigger another escalation in the same class
  // until the class esc is cleared
  bit [NUM_ALERT_HANDLER_CLASSES-1:0] under_esc_classes;
  bit [NUM_ALERT_HANDLER_CLASSES-1:0] under_intr_classes;
  bit [NUM_ALERT_HANDLER_CLASSES-1:0] clr_esc_under_intr;
  int intr_cnter_per_class    [NUM_ALERT_HANDLER_CLASSES];
  int accum_cnter_per_class   [NUM_ALERT_HANDLER_CLASSES];
  esc_state_e state_per_class [NUM_ALERT_HANDLER_CLASSES];
  int  esc_cnter_per_signal[NUM_ESC_SIGNALS];
  int  esc_signal_release  [NUM_ESC_SIGNALS];
  int  esc_sig_class       [NUM_ESC_SIGNALS]; // one class can increment one esc signal at a time
  // For different alert classify in the same class and trigger at the same cycle, design only
  // count once. So record the alert triggered timing here
  realtime last_triggered_alert_per_class[NUM_ALERT_HANDLER_CLASSES];

  string class_name[] = {"a", "b", "c", "d"};
  bit [TL_DW-1:0] intr_state_val;
  // TLM agent fifos
  uvm_tlm_analysis_fifo #(alert_esc_seq_item) alert_fifo[NUM_ALERTS];
  uvm_tlm_analysis_fifo #(alert_esc_seq_item) esc_fifo[NUM_ESCS];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ral.alert_cause_0.get_fields(alert_cause_fields);
    ral.loc_alert_cause_0.get_fields(loc_alert_cause_fields);
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
      check_intr_timeout_trigger_esc();
      esc_phase_signal_cnter();
      release_esc_signal();
    join_none
  endtask

  virtual task process_alert_fifo();
    foreach (alert_fifo[i]) begin
      automatic int index = i;
      fork
        forever begin
          bit [TL_DW-1:0] alert_en;
          alert_esc_seq_item act_item;
          alert_fifo[index].get(act_item);
          alert_en = ral.alert_en_0.get_mirrored_value();
          if (alert_en[index]) begin
            // alert detected
            if (act_item.alert_esc_type == AlertEscSigTrans && !act_item.ping_timeout &&
                act_item.alert_handshake_sta == AlertReceived) begin
              process_alert_sig(index, 0);
            // alert integrity fail
            end else if (act_item.alert_esc_type == AlertEscIntFail) begin
              bit [TL_DW-1:0] loc_alert_en = ral.loc_alert_en_0.get_mirrored_value();
              if (loc_alert_en[LocalAlertIntFail]) process_alert_sig(index, 1, LocalAlertIntFail);
            end else if (act_item.alert_esc_type == AlertEscPingTrans &&
                         act_item.ping_timeout) begin
              bit [TL_DW-1:0] loc_alert_en = ral.loc_alert_en_0.get_mirrored_value();
              if (loc_alert_en[LocalAlertPingFail]) begin
                process_alert_sig(index, 1, LocalAlertPingFail);
                `uvm_info(`gfn, $sformatf("alert %0d ping timeout, timeout_cyc reg is %0d",
                          index, ral.ping_timeout_cyc.get_mirrored_value()), UVM_LOW);
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
            bit [TL_DW-1:0] loc_alert_en = ral.loc_alert_en_0.get_mirrored_value();
            if (loc_alert_en[LocalEscIntFail]) process_alert_sig(index, 1, LocalEscIntFail);
          // escalation ping timeout
          end else if (act_item.alert_esc_type == AlertEscPingTrans && act_item.ping_timeout) begin
            bit [TL_DW-1:0] loc_alert_en = ral.loc_alert_en_0.get_mirrored_value();
            if (loc_alert_en[LocalEscPingFail]) begin
              process_alert_sig(index, 1, LocalEscPingFail);
              `uvm_info(`gfn, $sformatf("esc %0d ping timeout, timeout_cyc reg is %0d",
                        index, ral.ping_timeout_cyc.get_mirrored_value()), UVM_LOW);
            end
          end
        end
      join_none
    end
  endtask : process_esc_fifo

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
          bit [NUM_ALERTS*2-1:0] alert_class;
          bit [NUM_ALERT_HANDLER_CLASS_MSB:0] class_i;
          if (!is_int_err) begin
            alert_class = get_alert_class_mirrored_val();
            // extract the two bits that indicates which intr class this alert will trigger
            class_i = (alert_class >> alert_i * 2) & 'b11;
            alert_cause_field = alert_cause_fields[alert_i];
            void'(alert_cause_field.predict(1));
          end else begin
            alert_class = ral.loc_alert_class_0.get_mirrored_value();
            class_i = (alert_class >> local_alert_type * 2) & 'b11;
            loc_alert_cause_field = loc_alert_cause_fields[local_alert_type];
            void'(loc_alert_cause_field.predict(.value(1), .kind(UVM_PREDICT_READ)));
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
    // if ping periodic check enabled, will not check cycle count, because cycle count might be
    // connected with ping request, which makes the length unpredictable
    // it is beyond this scb to check ping timer (FPV checks it).
    if (ral.ping_timer_en.get_mirrored_value() && !cfg.under_reset) begin
      `DV_CHECK_EQ(cycle_cnt, esc_cnter_per_signal[esc_sig_i],
                   $sformatf("check signal_%0d", esc_sig_i))
      if (cfg.en_cov) cov.esc_sig_length_cg.sample(esc_sig_i, cycle_cnt);
    end
    esc_cnter_per_signal[esc_sig_i] = 0;
    esc_sig_class[esc_sig_i] = 0;
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = {item.a_addr[TL_AW-1:2], 2'b00};

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs[ral_name]}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end
    if (csr == null) begin
      // we hit an oob addr - expect error response and return
      `DV_CHECK_EQ(item.d_error, 1'b1)
      return;
    end

    if (channel == AddrChannel) begin
      // if incoming access is a write to a valid csr, then make updates right away
      if (write) begin
        void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
        // process the csr req
        // for write, update local variable and fifo at address phase
        case (csr.get_name())
          // add individual case item for each csr
          "intr_test": begin
            bit [TL_DW-1:0] intr_state_exp = item.a_data | ral.intr_state.get_mirrored_value();
            if (cfg.en_cov) begin
              bit [TL_DW-1:0] intr_en = ral.intr_enable.get_mirrored_value();
              for (int i = 0; i < NUM_ALERT_HANDLER_CLASSES; i++) begin
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
          "classa_clr": if (ral.classa_clr_regwen.get_mirrored_value()) clr_reset_esc_class(0);
          "classb_clr": if (ral.classb_clr_regwen.get_mirrored_value()) clr_reset_esc_class(1);
          "classc_clr": if (ral.classc_clr_regwen.get_mirrored_value()) clr_reset_esc_class(2);
          "classd_clr": if (ral.classd_clr_regwen.get_mirrored_value()) clr_reset_esc_class(3);
          default: begin
           //`uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
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
            for (int i = 0; i < NUM_ALERT_HANDLER_CLASSES; i++) begin
              cov.intr_cg.sample(i, intr_en[i], item.d_data[i]);
              cov.intr_pins_cg.sample(i, cfg.intr_vif.pins[i]);
            end
          end else begin
            for (int i = 0; i < NUM_ALERT_HANDLER_CLASSES; i++) begin
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
        for (int i = 0; i < NUM_ALERT_HANDLER_CLASSES; i++) begin
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

  // a counter to count how long each interrupt pins stay high until it is being reset
  // if counter exceeds threshold, call predict_esc() function to calculate related esc
  virtual task check_intr_timeout_trigger_esc();
    for (int i = 0; i < NUM_ALERT_HANDLER_CLASSES; i++) begin
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
                  timeout_cyc = get_class_timeout_cyc(class_i);
                  if (timeout_cyc > 0) begin
                    state_per_class[class_i] = EscStateTimeout;
                    while (under_intr_classes[class_i]) begin
                      @(cfg.clk_rst_vif.cbn);
                      if (intr_cnter_per_class[class_i] >= timeout_cyc) predict_esc(class_i);
                      intr_cnter_per_class[class_i] += 1;
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
  // esc signal cnter: "esc_cnter_per_signal" is used to check escalation esc_p/n cycle length
  // escalation signal is always one cycle longer than phase length, and the esc_p/n signal is an
  // "OR" result of different classes
  virtual task esc_phase_signal_cnter();
    for (int i = 0; i < NUM_ALERT_HANDLER_CLASSES; i++) begin
      fork
        automatic int class_i = i;
        begin : esc_phases_counter
          forever @(!cfg.under_reset && under_esc_classes[class_i]) begin
            fork
              begin : inc_esc_cnt
                for (int phase_i = 0; phase_i < NUM_ESC_PHASES; phase_i++) begin
                  int phase_thresh = reg_esc_phase_cycs_per_class_q[class_i][phase_i]
                                     .get_mirrored_value();
                  bit[TL_DW-1:0] class_ctrl = get_class_ctrl(class_i);
                  int enabled_sig_q[$];
                  for (int sig_i = 0; sig_i < NUM_ESC_SIGNALS; sig_i++) begin
                    if (class_ctrl[sig_i*2+7 -: 2] == phase_i && class_ctrl[sig_i+2]) begin
                      enabled_sig_q.push_back(sig_i);
                    end
                  end
                  if (under_esc_classes[class_i]) begin
                    incr_esc_sig_cnt(enabled_sig_q, class_i);
                    intr_cnter_per_class[class_i] = 1;
                    state_per_class[class_i] = esc_state_e'(phase_i + int'(EscStatePhase0));
                    cfg.clk_rst_vif.wait_n_clks(1);
                    while (under_esc_classes[class_i] &&
                           intr_cnter_per_class[class_i] < phase_thresh) begin
                      incr_esc_sig_cnt(enabled_sig_q, class_i);
                      intr_cnter_per_class[class_i]++;
                      cfg.clk_rst_vif.wait_n_clks(1);
                    end
                    incr_esc_sig_cnt(enabled_sig_q, class_i);
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

  // increase signal count only when current signal is not incremented by other class already
  // so use esc_sig_class to gate only one class access the counter at a time
  virtual function void incr_esc_sig_cnt(const ref int sig_q[$], int class_i);
    foreach (sig_q[i]) begin
      int index = sig_q[i];
      if (esc_sig_class[index] == 0) esc_sig_class[index] = class_i + 1;
      if (esc_sig_class[index] == (class_i + 1)) begin
        if (!under_reset) esc_cnter_per_signal[index]++;
        `uvm_info(`gfn, $sformatf("class_%0d signal_%0d, esc_cnt=%0d", class_i, index,
                                  esc_cnter_per_signal[index]), UVM_DEBUG)
      end
    end
  endfunction

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    under_intr_classes    = '{default:0};
    intr_cnter_per_class  = '{default:0};
    under_esc_classes     = '{default:0};
    esc_cnter_per_signal  = '{default:0};
    esc_sig_class         = '{default:0};
    accum_cnter_per_class = '{default:0};
    state_per_class       = '{default:EscStateIdle};
    clr_esc_under_intr    = 0;
    last_triggered_alert_per_class = '{default:$realtime};
  endfunction

  // clear accumulative counters, and escalation counters if they are under escalation
  // interrupt timeout counters cannot be cleared by this
  task clr_reset_esc_class(int class_i);
    fork
      begin
        cfg.clk_rst_vif.wait_clks(1);
        if (under_intr_classes[class_i]) clr_esc_under_intr[class_i] = 1;
        if (under_esc_classes [class_i]) intr_cnter_per_class[class_i] = 0;
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
    class_ctrl_rg = ral.get_reg_by_name($sformatf("class%s_ctrl", class_name[class_i]));
    `DV_CHECK_NE_FATAL(class_ctrl_rg, null)
    return class_ctrl_rg.get_mirrored_value();
  endfunction

  // get class_accum_thresh register mirrored value by class
  function bit [TL_DW-1:0] get_class_accum_thresh(int class_i);
    uvm_reg class_thresh_rg;
    class_thresh_rg = ral.get_reg_by_name($sformatf("class%s_accum_thresh", class_name[class_i]));
    `DV_CHECK_NE_FATAL(class_thresh_rg, null)
    return class_thresh_rg.get_mirrored_value();
  endfunction

  // get class_timeout_cyc register mirrored value by class
  function bit [TL_DW-1:0] get_class_timeout_cyc(int class_i);
    dv_base_reg class_timeout_rg = ral.get_dv_base_reg_by_name($sformatf("class%s_timeout_cyc",
                                                               class_name[class_i]));
    return class_timeout_rg.get_mirrored_value();
  endfunction

  // If num_alerts exceeds TL_DW/2, then alert_class will need more than one reg to hold its value
  function bit [NUM_ALERTS*2-1:0] get_alert_class_mirrored_val();
    for (int i = 0; i < $ceil(NUM_ALERTS * 2 / TL_DW); i++) begin
      string alert_name = (NUM_ALERTS <= TL_DW / 2) ? "alert_class" :
                                                      $sformatf("alert_class_%0d", i);
      dv_base_reg alert_class_csr = ral.get_dv_base_reg_by_name(alert_name);
      get_alert_class_mirrored_val |= (alert_class_csr.get_mirrored_value() << i * TL_DW);
    end
  endfunction
endclass

`undef ASSIGN_CLASS_PHASE_REGS
