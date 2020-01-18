// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class alert_handler_scoreboard extends cip_base_scoreboard #(
    .CFG_T(alert_handler_env_cfg),
    .RAL_T(alert_handler_reg_block),
    .COV_T(alert_handler_env_cov)
  );
  `uvm_component_utils(alert_handler_scoreboard)

  // local variables

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(alert_esc_seq_item) alert_fifo[alert_pkg::NAlerts];
  uvm_tlm_analysis_fifo #(alert_esc_seq_item) esc_fifo[alert_pkg::N_ESC_SEV];

  // local queues to hold incoming packets pending comparison

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    foreach(alert_fifo[i]) alert_fifo[i] = new($sformatf("alert_fifo[%0d]", i), this);
    // TODO: esc fifo is not connected
    foreach(esc_fifo[i])   esc_fifo[i]   = new($sformatf("esc_fifo[%0d]", i), this);
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
    uvm_reg_field alert_cause_fields[$];
    uvm_reg_field intr_state_fields[$];
    ral.alert_cause.get_fields(alert_cause_fields);
    ral.intr_state.get_fields(intr_state_fields);
    foreach (alert_fifo[i]) begin
      automatic int index = i;
      fork
        forever begin
          alert_esc_seq_item act_item;
          alert_fifo[index].get(act_item);
          // once the alert is received
          if (act_item.alert_esc_type == AlertEscSigTrans && !act_item.timeout &&
              act_item.alert_handshake_sta == AlertReceived) begin
            uvm_reg_field alert_cause_field, intr_state_field;
            bit [TL_DW-1:0] alert_en = ral.alert_en.get_mirrored_value();

            if (alert_en[index]) begin
              bit [TL_DW-1:0] intr_class = ral.alert_class.get_mirrored_value();
              alert_cause_field = alert_cause_fields[index];
              // extract the two bits that indicates which intr class this alert will trigger
              intr_state_field = intr_state_fields[(intr_class >> index*2) & 'b11];
              void'(alert_cause_field.predict(1));
              void'(intr_state_field.predict(1));
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
        end
      join_none
    end
  endtask : process_esc_fifo

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
  endfunction

endclass
