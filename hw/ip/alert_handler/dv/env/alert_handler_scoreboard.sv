// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`define ASSIGN_CLASS_PHASE_REGS(index, i) \
  class_phase_cycs_q[``index``] = {ral.class``i``_phase0_cyc, ral.class``i``_phase1_cyc, \
                                   ral.class``i``_phase2_cyc, ral.class``i``_phase3_cyc};

class alert_handler_scoreboard extends cip_base_scoreboard #(
    .CFG_T(alert_handler_env_cfg),
    .RAL_T(alert_handler_reg_block),
    .COV_T(alert_handler_env_cov)
  );
  `uvm_component_utils(alert_handler_scoreboard)

  // local variables
  // for each escalator signals, stores the matching phase
  esc_phase_e   esc_phases_q[NUM_ALERT_HANDLER_CLASSES][$];
  dv_base_reg   class_phase_cycs_q[NUM_ALERT_HANDLER_CLASSES][$];
  uvm_reg_field alert_cause_fields[$];
  uvm_reg_field intr_state_fields[$];
  uvm_reg_field alert_cause_field, intr_state_field;
  // once escalation triggers, no alerts can trigger another escalation until it is cleared
  bit           under_esc;
  bit [NUM_ALERT_HANDLER_CLASS_MSB:0] triggered_alert_class;

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
            process_esc_sig(esc_phases_q[index], index, phase_info);
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
    bit [NUM_ALERT_HANDLER_CLASS_MSB:0] intr_class  = (alert_class >> index * 2) & 'b11;
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
    if (class_ctrl[0] && (class_ctrl[5:2] > 0) && !under_esc) begin
      under_esc = 1;
      triggered_alert_class = intr_class;
      for (int i = 0; i < NUM_ALERT_HANDLER_CLASSES; i++) begin
        if (class_ctrl[i + 2]) begin
          push_and_check_queue(esc_phases_q[i], ((class_ctrl >> i*2+6) & 'b11));
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
    if (!under_esc) `uvm_error(`gfn, "please check if esc signal goes high")
    cal_cycle = (end_time - phase_info.start_time) * 1000 / cfg.clk_rst_vif.clk_period_ps;
    act_cycle = class_phase_cycs_q[triggered_alert_class][phase_info.phase].get_mirrored_value();

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
     case (csr.get_name())
      // add individual case item for each csr
       "intr_test": begin
         if (write) begin
           bit [TL_DW-1:0] intr_state_exp = item.a_data | ral.intr_state.get_mirrored_value();
           void'(ral.intr_state.predict(.value(intr_state_exp), .kind(UVM_PREDICT_DIRECT)));
         end
       end
       "classa_clr": if (under_esc && (triggered_alert_class == 0)) under_esc = 0;
       "classb_clr": if (under_esc && (triggered_alert_class == 1)) under_esc = 0;
       "classc_clr": if (under_esc && (triggered_alert_class == 2)) under_esc = 0;
       "classd_clr": if (under_esc && (triggered_alert_class == 3)) under_esc = 0;
       default: begin
        //`uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
       end
     endcase

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
    foreach (esc_phases_q[i]) `DV_CHECK_EQ(esc_phases_q[i].size(), 0)
  endfunction

endclass

`undef ASSIGN_CLASS_PHASE_REGS
