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

  // local variables
  // esc_phase_per_sig_q: each escalation signal corresponse to one phase (from the class_ctrl reg)
  // --- signal --- phase  ---
  // ---    0   --- MAP_E0 ---
  // ---    1   --- MAP_E1 ---
  // ---    2   --- MAP_E2 ---
  // ---    3   --- MAP_E3 ---
  esc_phase_e   esc_phase_per_sig_q[NUM_ESC_SIGNALS][$];

  // esc_phase_cyc_per_class_q: each class has four phase cycles, stores each cycle length
  // --- class --- phase0_cyc    ---    phase1_cyc   ---    phase2_cyc   ---     phase3_cyc  ---
  // ---   A   -classa_phase0_cyc - classa_phase1_cyc - classa_phase2_cyc - classa_phase3_cyc --
  // ---   B   -classb_phase0_cyc - classb_phase1_cyc - classb_phase2_cyc - classb_phase3_cyc --
  // ---   C   -classc_phase0_cyc - classc_phase1_cyc - classc_phase2_cyc - classc_phase3_cyc --
  // ---   D   -classd_phase0_cyc - classd_phase1_cyc - classd_phase2_cyc - classd_phase3_cyc --
  dv_base_reg   reg_esc_phase_cycs_per_class_q[NUM_ALERT_HANDLER_CLASSES][$];
  dv_base_reg   reg_accum_cnts[NUM_ALERT_HANDLER_CLASSES];

  uvm_reg_field alert_cause_fields[$];
  uvm_reg_field intr_state_fields[$];
  uvm_reg_field loc_alert_cause_fields[$];
  uvm_reg_field alert_cause_field, intr_state_field, loc_alert_cause_field;
  // once escalation triggers, no alerts can trigger another escalation in the same class
  // until the class esc is cleared
  bit [NUM_ALERT_HANDLER_CLASSES-1:0] under_esc_classes;
  bit [NUM_ALERT_HANDLER_CLASSES-1:0] under_intr_classes;
  bit [NUM_ALERT_HANDLER_CLASS_MSB:0] esc_class_trigger;
  int      intr_timer_per_class[NUM_ALERT_HANDLER_CLASSES];
  // For different alert classify in the same class and trigger at the same cycle, design only
  // count once. So record the alert triggered timing here
  realtime last_triggered_alert_per_class[NUM_ALERT_HANDLER_CLASSES];

  string class_name[] = {"a", "b", "c", "d"};

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(alert_esc_seq_item) alert_fifo[alert_pkg::NAlerts];
  uvm_tlm_analysis_fifo #(alert_esc_seq_item) esc_fifo[alert_pkg::N_ESC_SEV];

  // local queues to hold incoming packets pending comparison

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ral.alert_cause.get_fields(alert_cause_fields);
    ral.loc_alert_cause.get_fields(loc_alert_cause_fields);
    ral.intr_state.get_fields(intr_state_fields);
    `ASSIGN_CLASS_PHASE_REGS(0, a)
    `ASSIGN_CLASS_PHASE_REGS(1, b)
    `ASSIGN_CLASS_PHASE_REGS(2, c)
    `ASSIGN_CLASS_PHASE_REGS(3, d)
    reg_accum_cnts = {ral.classa_accum_cnt, ral.classb_accum_cnt, ral.classc_accum_cnt,
                      ral.classd_accum_cnt};

    foreach (alert_fifo[i]) alert_fifo[i] = new($sformatf("alert_fifo[%0d]", i), this);
    foreach (esc_fifo[i])   esc_fifo[i]   = new($sformatf("esc_fifo[%0d]", i), this);
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
          // once the alert is received
          alert_en = ral.alert_en.get_mirrored_value();
          if (alert_en[index]) begin
            if (act_item.alert_esc_type == AlertEscSigTrans && !act_item.timeout &&
                act_item.alert_handshake_sta == AlertReceived) begin
              process_alert_sig(index, 0);
            end else if (act_item.alert_esc_type == AlertEscIntFail) begin
              bit [TL_DW-1:0] loc_alert_en = ral.loc_alert_en.get_mirrored_value();
              if (loc_alert_en[LocalAlertIntFail]) process_alert_sig(index, 1, LocalAlertIntFail);
            end
          end
        end
      join_none
    end
  endtask : process_alert_fifo

  virtual task process_esc_fifo();
    foreach (esc_fifo[i]) begin
      automatic int index = i;
      automatic esc_phase_t phase_info;
      fork
        forever begin
          alert_esc_seq_item act_item;
          esc_fifo[index].get(act_item);
          // once esc signal is received
          if (act_item.alert_esc_type == AlertEscSigTrans &&
              act_item.esc_handshake_sta == EscReceived) begin
            process_esc_sig(esc_phase_per_sig_q[index], index, phase_info);
          end
          if (act_item.alert_esc_type == AlertEscSigTrans &&
              act_item.esc_handshake_sta == EscRespComplete) begin
            check_esc_phase(phase_info);
          end
        end
      join_none
    end
  endtask : process_esc_fifo

  // this function process alert signal by checking if intergrity fail, then classify it to the
  // mapping classes, then check if escalation is triggered by accumulation
  virtual function void process_alert_sig(int alert_i, bit is_int_err,
                                          local_alert_type_e local_alert_type = LocalAlertIntFail);
    bit [TL_DW-1:0] alert_class, intr_en;
    bit [NUM_ALERT_HANDLER_CLASS_MSB:0] class_i;
    bit [TL_DW-1:0] class_ctrl;

    if (!is_int_err) begin
      alert_class = ral.alert_class.get_mirrored_value();
      // extract the two bits that indicates which intr class this alert will trigger
      class_i = (alert_class >> alert_i * 2) & 'b11;
      alert_cause_field = alert_cause_fields[alert_i];
      void'(alert_cause_field.predict(1));
    end else begin
      alert_class = ral.loc_alert_class.get_mirrored_value();
      class_i = (alert_class >> local_alert_type * 2) & 'b11;
      loc_alert_cause_field = loc_alert_cause_fields[local_alert_type];
      void'(loc_alert_cause_field.predict(1));
    end

    intr_state_field = intr_state_fields[class_i];
    void'(intr_state_field.predict(1));
    intr_en = ral.intr_enable.get_mirrored_value();
    if (!under_intr_classes[class_i] && intr_en[class_i]) under_intr_classes[class_i] = 1;
    // calculate escalation
    class_ctrl = get_class_ctrl(class_i);
    `uvm_info(`gfn, $sformatf("class %0d is triggered, class ctrl=%0h, under_esc=%0b",
                              class_i, class_ctrl, under_esc_classes[class_i]), UVM_DEBUG)
    // if class escalation is enabled, add alert to accumulation count
    if (class_ctrl[AlertClassCtrlEn] &&
        (class_ctrl[AlertClassCtrlEnE3:AlertClassCtrlEnE0] > 0)) begin
      alert_accum_cal(class_i);
    end
  endfunction

  // calculate alert accumulation count per class, if accumulation exceeds the threshold,
  // and if current class not under escalation, then predict escalation
  // more thatn one alerts triggered on the same clk cycle only counts for one
  virtual function void alert_accum_cal(int class_i);
    bit [TL_DW-1:0] accum_thresh = get_class_accum_thresh(class_i);
    int accum_cnt = reg_accum_cnts[class_i].get_mirrored_value();
    realtime curr_time = $realtime();
    if (curr_time != last_triggered_alert_per_class[class_i]) begin
      last_triggered_alert_per_class[class_i] = curr_time;
      accum_cnt += 1;
      void'(reg_accum_cnts[class_i].predict(accum_cnt));
    end
    esc_class_trigger = class_i;
    `uvm_info(`gfn, $sformatf("alert_accum: class=%0d, alert_cnt=%0d, thresh=%0d, under_esc=%0b",
        class_i, accum_cnt, accum_thresh, under_esc_classes[class_i]), UVM_DEBUG)
    if (accum_cnt > accum_thresh && !under_esc_classes[class_i]) predict_esc(class_i);
  endfunction

  // predict escalation signals by matching which phase should the esc signal will be triggered
  virtual function void predict_esc(int class_i);
    bit [TL_DW-1:0] class_ctrl = get_class_ctrl(class_i);
    under_esc_classes[class_i] = 1;
    for (int i = 0; i < NUM_ALERT_HANDLER_CLASSES; i++) begin
      if (class_ctrl[i + AlertClassCtrlEnE0]) begin
        esc_phase_per_sig_q[i].push_back((class_ctrl >> i*2+6) & 'b11);
        `DV_CHECK_LT_FATAL(esc_phase_per_sig_q[i].size(), 2, "esc signal should only match 1 phase")
      end
    end
  endfunction

  virtual function void process_esc_sig(ref esc_phase_e esc_phase_q[$], int esc_sig_i,
                                        ref esc_phase_t phase_info);
    if (esc_phase_q.size() == 0) begin
      `uvm_error(`gfn, $sformatf("found unexpected esc signal %0d", esc_sig_i))
    end
    phase_info.phase = esc_phase_q.pop_front();
    phase_info.start_time = $realtime;
    `uvm_info(`gfn, $sformatf("esc signal_%0d triggered at %s", esc_sig_i, phase_info.phase.name),
              UVM_LOW)
  endfunction

  virtual function void check_esc_phase(ref esc_phase_t phase_info);
    realtime end_time = $realtime;
    int      cal_cycle, act_cycle;
    if (under_esc_classes == 0) `uvm_error(`gfn, "please check if esc signal goes high")
    cal_cycle = (end_time - phase_info.start_time) * 1000 / cfg.clk_rst_vif.clk_period_ps;
    act_cycle =
        reg_esc_phase_cycs_per_class_q[esc_class_trigger][phase_info.phase].get_mirrored_value();

    if (act_cycle < 2) act_cycle = 2;
    `DV_CHECK_EQ(act_cycle, cal_cycle)
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = {item.a_addr[TL_AW-1:2], 2'b00};

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs}) begin
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
             void'(ral.intr_state.predict(.value(intr_state_exp), .kind(UVM_PREDICT_DIRECT)));
          end
          "intr_state": begin
            foreach (under_intr_classes[i]) begin
              if (item.a_data[i]) under_intr_classes[i] = 0;
            end
          end
          "classa_clr": clr_reset_esc_class(0);
          "classb_clr": clr_reset_esc_class(1);
          "classc_clr": clr_reset_esc_class(2);
          "classd_clr": clr_reset_esc_class(3);
          default: begin
           //`uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
          end
        endcase
      end
    end

    // process the csr req
    // for read, update predication at address phase and compare at data phase

    if (!write && do_read_check) begin
      // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
      if (channel == DataChannel) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
        void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
      end else begin
        case (csr.get_name())
          "classa_esc_cnt": begin
            void'(ral.classa_esc_cnt.predict(.value(intr_timer_per_class[0]),
                  .kind(UVM_PREDICT_READ)));
          end
          "classb_esc_cnt": begin
            void'(ral.classb_esc_cnt.predict(.value(intr_timer_per_class[1]),
                  .kind(UVM_PREDICT_READ)));
          end
          "classc_esc_cnt": begin
            void'(ral.classc_esc_cnt.predict(.value(intr_timer_per_class[2]),
                  .kind(UVM_PREDICT_READ)));
          end
          "classd_esc_cnt": begin
            void'(ral.classd_esc_cnt.predict(.value(intr_timer_per_class[3]),
                  .kind(UVM_PREDICT_READ)));
          end
          default: begin
           //`uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
          end
        endcase
      end
    end
  endtask

  // a counter to count how long each interrupt pins stay high until it is being reset.
  // check if escalation will be triggered if the interrupt counter is larger than the threshold
  virtual task check_intr_timeout_trigger_esc();
    for (int i=0; i < NUM_ALERT_HANDLER_CLASSES; i++) begin
      automatic int             class_i = i;
      automatic bit [TL_DW-1:0] timeout_cyc, class_ctrl;
      fork
        begin : intr_sig_counter
          forever @(under_intr_classes[class_i] && !under_esc_classes[class_i]) begin
            // wait a clk for esc signal to go high
            cfg.clk_rst_vif.wait_clks(1);
            class_ctrl = get_class_ctrl(class_i);
            if (class_ctrl[AlertClassCtrlEn] &&
                (class_ctrl[AlertClassCtrlEnE3:AlertClassCtrlEnE0] > 0)) begin
              intr_timer_per_class[class_i] = 0;
              // counter continues to increment if:
              // interrupt is not cleared, and class is not under escalation by accum_alerts
              while (under_intr_classes[class_i] != 0 && !under_esc_classes[class_i]) begin
                @(cfg.clk_rst_vif.cb);
                intr_timer_per_class[class_i] += 1;
                timeout_cyc = get_class_timeout_cyc(class_i);
                if (timeout_cyc != 0 && intr_timer_per_class[class_i] >= timeout_cyc &&
                    !under_esc_classes[class_i]) begin
                  predict_esc(class_i);
                end
              end
              intr_timer_per_class[class_i] = 0;
            end
          end //end forever
        end
        begin : esc_phases_counter
          forever @(under_esc_classes[class_i]) begin
            for (int phase_i = 0; phase_i < NUM_ESC_PHASES; phase_i++) begin
              int phase_thresh = reg_esc_phase_cycs_per_class_q[class_i][phase_i]
                                .get_mirrored_value();
              @(cfg.clk_rst_vif.cb);
              intr_timer_per_class[class_i] = 1;
              while (under_esc_classes[class_i] != 0 &&
                     intr_timer_per_class[class_i] < phase_thresh) begin
                @(cfg.clk_rst_vif.cb);
                intr_timer_per_class[class_i] += 1;
              end
            end
            @(cfg.clk_rst_vif.cb);
            intr_timer_per_class[class_i] = 0;
          end // end forever
        end
      join_none
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
    for (int i = 0; i < NUM_ALERT_HANDLER_CLASSES; i++) clr_reset_esc_class(i);
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
    foreach (esc_phase_per_sig_q[i]) begin
      `DV_CHECK_EQ(esc_phase_per_sig_q[i].size(), 0, $sformatf("failed esc_phase %0d", i))
    end
  endfunction

  function void clr_reset_esc_class(int class_i);
    under_esc_classes[class_i] = 0;
    foreach (esc_phase_per_sig_q[i]) esc_phase_per_sig_q[i].delete();
    // clear all the counters and timers for esc
    intr_timer_per_class[class_i] = 0;
    last_triggered_alert_per_class[class_i] = 0;
    under_intr_classes[class_i] = 0;
    intr_timer_per_class[class_i] = 0;
    void'(reg_accum_cnts[class_i].predict(0));
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
    uvm_reg class_timeout_rg;
    class_timeout_rg = ral.get_reg_by_name($sformatf("class%s_timeout_cyc", class_name[class_i]));
    `DV_CHECK_NE_FATAL(class_timeout_rg, null)
    return class_timeout_rg.get_mirrored_value();
  endfunction

endclass

`undef ASSIGN_CLASS_PHASE_REGS
