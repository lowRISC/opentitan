// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define ASSIGN_CLASS_PHASE_REGS(index, i) \
  esc_phase_cycs_per_class_q[``index``] = {ral.class``i``_phase0_cyc, ral.class``i``_phase1_cyc, \
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
  dv_base_reg   esc_phase_cycs_per_class_q[NUM_ALERT_HANDLER_CLASSES][$];

  uvm_reg_field alert_cause_fields[$];
  uvm_reg_field intr_state_fields[$];
  uvm_reg_field alert_cause_field, intr_state_field;
  // once escalation triggers, no alerts can trigger another escalation in the same class
  // until the class esc is cleared
  bit [NUM_ALERT_HANDLER_CLASSES-1:0] under_esc_classes;
  bit [NUM_ALERT_HANDLER_CLASS_MSB:0] esc_class_trigger;

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(alert_esc_seq_item) alert_fifo[alert_pkg::NAlerts];
  uvm_tlm_analysis_fifo #(alert_esc_seq_item) esc_fifo[alert_pkg::N_ESC_SEV];

  // local queues to hold incoming packets pending comparison

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    ral.alert_cause.get_fields(alert_cause_fields);
    ral.intr_state.get_fields(intr_state_fields);
    `ASSIGN_CLASS_PHASE_REGS(0, a)
    `ASSIGN_CLASS_PHASE_REGS(1, b)
    `ASSIGN_CLASS_PHASE_REGS(2, c)
    `ASSIGN_CLASS_PHASE_REGS(3, d)

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
    join_none
  endtask

  virtual task process_alert_fifo();
    foreach (alert_fifo[i]) begin
      automatic int index = i;
      fork
        forever begin
          alert_esc_seq_item act_item;
          alert_fifo[index].get(act_item);
          // once the alert is received
          if (act_item.alert_esc_type == AlertEscSigTrans && !act_item.timeout &&
              act_item.alert_handshake_sta == AlertReceived) begin
            bit [TL_DW-1:0] alert_en = ral.alert_en.get_mirrored_value();
            if (alert_en[index]) process_alert_sig(index);
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

  virtual function void process_alert_sig(int index);
    bit [TL_DW-1:0] alert_class = ral.alert_class.get_mirrored_value();
    // extract the two bits that indicates which intr class this alert will trigger
    bit [NUM_ALERT_HANDLER_CLASS_MSB:0] intr_class = (alert_class >> index * 2) & 'b11;
    bit [TL_DW-1:0] class_ctrl;
    alert_cause_field = alert_cause_fields[index];
    intr_state_field = intr_state_fields[intr_class];
    void'(alert_cause_field.predict(1));
    void'(intr_state_field.predict(1));
    // calculate escalation
    case (intr_class)
      0: class_ctrl = ral.classa_ctrl.get_mirrored_value();
      1: class_ctrl = ral.classb_ctrl.get_mirrored_value();
      2: class_ctrl = ral.classc_ctrl.get_mirrored_value();
      3: class_ctrl = ral.classd_ctrl.get_mirrored_value();
      default: `uvm_error(`gfn, $sformatf("no matches for intr class %0d", intr_class))
    endcase
    // if class escalation is enabled
    if (class_ctrl[AlertClassCtrlEn] && (class_ctrl[AlertClassCtrlEnE3:AlertClassCtrlEnE0] > 0) &&
        !under_esc_classes[intr_class]) begin
      under_esc_classes[intr_class] = 1;
      esc_class_trigger = intr_class;
      for (int i = 0; i < NUM_ALERT_HANDLER_CLASSES; i++) begin
        if (class_ctrl[i + AlertClassCtrlEnE0]) begin
          push_and_check_queue(esc_phase_per_sig_q[i], ((class_ctrl >> i*2+6) & 'b11));
        end
      end
    end
  endfunction

  virtual function void push_and_check_queue(ref esc_phase_e queue[$], input int element);
    queue.push_back(element);
    `DV_CHECK_LT_FATAL(queue.size(), 2, "each esc signal should only assign 1 phase")
  endfunction

  virtual function void process_esc_sig(ref esc_phase_e esc_phase_q[$], int index,
                                        ref esc_phase_t phase_info);
    if (esc_phase_q.size() == 0) begin
      `uvm_error(`gfn, $sformatf("found unexpected esc signal %0d", index))
    end
    phase_info.phase = esc_phase_q.pop_front();
    phase_info.start_time = $realtime;
    `uvm_info(`gfn, $sformatf("esc signal_%0d triggered at %s", index, phase_info.phase.name),
              UVM_LOW)
  endfunction

  virtual function void check_esc_phase(ref esc_phase_t phase_info);
    realtime end_time = $realtime;
    int      cal_cycle, act_cycle;
    if (under_esc_classes == 0) `uvm_error(`gfn, "please check if esc signal goes high")
    cal_cycle = (end_time - phase_info.start_time) * 1000 / cfg.clk_rst_vif.clk_period_ps;
    act_cycle =
        esc_phase_cycs_per_class_q[esc_class_trigger][phase_info.phase].get_mirrored_value();

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
      end
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    if (write) begin
      case (csr.get_name())
        // add individual case item for each csr
        "intr_test": begin
           bit [TL_DW-1:0] intr_state_exp = item.a_data | ral.intr_state.get_mirrored_value();
           void'(ral.intr_state.predict(.value(intr_state_exp), .kind(UVM_PREDICT_DIRECT)));
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

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (!write && channel == DataChannel) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
    foreach (esc_phase_per_sig_q[i]) begin
      `DV_CHECK_EQ(esc_phase_per_sig_q[i].size(), 0, $sformatf("failed esc_phase %0d", i))
    end
  endfunction

  function void clr_reset_esc_class(int index);
    under_esc_classes[index] = 0;
    foreach (esc_phase_per_sig_q[i]) esc_phase_per_sig_q[i].delete();
  endfunction
endclass

`undef ASSIGN_CLASS_PHASE_REGS
