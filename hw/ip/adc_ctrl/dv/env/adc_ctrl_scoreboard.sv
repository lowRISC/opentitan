// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class adc_ctrl_scoreboard extends cip_base_scoreboard #(
  .CFG_T(adc_ctrl_env_cfg),
  .RAL_T(adc_ctrl_reg_block),
  .COV_T(adc_ctrl_env_cov)
);

  `uvm_component_utils(adc_ctrl_scoreboard)

  // Analysis FIFOs for ADC push pull monitor transactions
  adc_push_pull_fifo_t m_adc_push_pull_fifo[ADC_CTRL_CHANNELS];

  // Latest value for each channel
  protected adc_value_logic_t m_adc_latest_values[int];

  // Interrupt value for each channel
  protected adc_value_logic_t m_adc_interrupt_values[int];

  // Sampled interrupts
  protected logic [NUM_MAX_INTERRUPTS-1:0] m_interrupts;

  // Our interrupt line
  protected logic m_interrupt;

  // Interrupt asserted this ADC sample
  protected logic m_interrupt_posedge;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // Create ADC push pull FIFOs
    for (int idx = 0; idx < ADC_CTRL_CHANNELS; idx++) begin
      string name = $sformatf("m_adc_push_pull_fifo_%0d", idx);
      m_adc_push_pull_fifo[idx] = new(name, this);
    end
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    int idx = 0;
    super.run_phase(phase);
    fork
      monitor_intr_proc();
    join_none

    for (idx = 0; idx < ADC_CTRL_CHANNELS; idx++) begin
      // Local copy see LRM 9.3.2 for details
      int idx_local = idx;
      fork
        adc_push_pull_fifo_proc(m_adc_push_pull_fifo[idx_local], idx_local);
      join_none
    end
  endtask


  // Monitor interrupt line
  protected virtual task monitor_intr_proc();
    forever begin
      cfg.clk_rst_vif.wait_clks(1);
      // Sample the interrupt lines
      m_interrupts = cfg.intr_vif.sample();
      `uvm_info(`gfn, $sformatf("interrupts=%b", m_interrupts), UVM_DEBUG)

      // Detect a positive edge on our interrupt line
      m_interrupt_posedge = ~m_interrupt & m_interrupts[ADC_CTRL_INTERRUPT_INDEX];
      m_interrupt         = m_interrupts[ADC_CTRL_INTERRUPT_INDEX];

      // If we see a positive edge on the interrupt line capture the lastest values
      if (m_interrupt_posedge) begin
        foreach (m_adc_latest_values[channel]) begin
          m_adc_interrupt_values[channel] = m_adc_latest_values[channel];
        end
      end

    end
  endtask

  // Process ADC push pull fifos
  protected virtual task adc_push_pull_fifo_proc(adc_push_pull_fifo_t fifo, int channel);
    adc_push_pull_item_t item;
    forever begin
      fifo.get(item);
      cfg.trigger_adc_rx_event(channel);
      // Set latest value
      m_adc_latest_values[channel] = item.d_data;
      `uvm_info(
          `gfn, $sformatf(
          "adc_push_pull_fifo_proc channel %0d: %s", channel, item.sprint(uvm_default_line_printer)
          ), UVM_LOW)
    end
  endtask

  // Return the latest ADC value for the respective channel
  virtual function adc_value_logic_t get_adc_latest_value(input int channel);
    adc_value_logic_t value = m_adc_latest_values[channel];
    `uvm_info(`gfn, $sformatf("get_adc_latest_value channel=%0d  value=%0h", channel, value),
              UVM_HIGH)
    return value;
  endfunction

  // Return the latest ADC interrupt value for the respective channel
  virtual function adc_value_logic_t get_adc_interrupt_value(input int channel);
    adc_value_logic_t value = m_adc_interrupt_values[channel];
    `uvm_info(`gfn, $sformatf("get_adc_interrupt_value channel=%0d  value=%0h", channel, value),
              UVM_HIGH)
    return value;
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg        csr;
    bit            do_read_check = 1'b1;
    bit            write = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    bit            addr_phase_read = (!write && channel == AddrChannel);
    bit            addr_phase_write = (write && channel == AddrChannel);
    bit            data_phase_read = (!write && channel == DataChannel);
    bit            data_phase_write = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // if incoming access is a write to a valid csr, then make updates right away
    if (addr_phase_write) begin
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr.get_name())
      // add individual case item for each csr
      "intr_state": begin
        // FIXME
        do_read_check = 1'b0;
      end
      "intr_enable": begin
        // FIXME
      end
      "intr_test": begin
        // FIXME
      end
      "adc_intr_status": begin
        do_read_check = 1'b0;
      end
      "adc_intr_ctl": begin
        // FIXME
      end
      "adc_en_ctl": begin
        // FIXME
      end

      "adc_chn0_filter_ctl_0", "adc_chn0_filter_ctl_1", "adc_chn0_filter_ctl_2",
          "adc_chn0_filter_ctl_3", "adc_chn0_filter_ctl_4", "adc_chn0_filter_ctl_5",
          "adc_chn0_filter_ctl_6", "adc_chn0_filter_ctl_7", "adc_chn1_filter_ctl_0",
          "adc_chn1_filter_ctl_1", "adc_chn1_filter_ctl_2", "adc_chn1_filter_ctl_3",
          "adc_chn1_filter_ctl_4", "adc_chn1_filter_ctl_5", "adc_chn1_filter_ctl_6",
          "adc_chn1_filter_ctl_7"
          : begin
        // FIXME
      end

      "adc_chn_val_0": begin
        // Predict values
        if (addr_phase_read) begin
          // Latest ADC value
          void'(ral.adc_chn_val[0].adc_chn_value.predict(
              .value(get_adc_latest_value(0)), .kind(UVM_PREDICT_READ)
          ));

          // Interrupt ADC value
          `uvm_info(`gfn, $sformatf(
                    "adc_en_ctl.oneshot_mode=%0x", ral.adc_en_ctl.oneshot_mode.get_mirrored_value()
                    ), UVM_HIGH)
          if (ral.adc_en_ctl.oneshot_mode.get_mirrored_value() == 1) begin
            // In oneshot mode latest and interrupt fields are the same
            void'(ral.adc_chn_val[0].adc_chn_value_intr.predict(
                .value(get_adc_latest_value(0)), .kind(UVM_PREDICT_READ)
            ));
          end else begin
            `uvm_info(`gfn, "FIXME: Predict adc_chn_val_0.adc_chn_value_intr", UVM_NONE)
          end
        end
      end
      "adc_chn_val_1": begin
        // Predict values
        if (addr_phase_read) begin

          void'(ral.adc_chn_val[1].adc_chn_value.predict(
              .value(get_adc_latest_value(1)), .kind(UVM_PREDICT_READ)
          ));

          // Interrupt ADC value
          if (ral.adc_en_ctl.oneshot_mode.get_mirrored_value() == 1) begin
            // In oneshot mode latest and interrupt fields are the same
            void'(ral.adc_chn_val[1].adc_chn_value_intr.predict(
                .value(get_adc_latest_value(1)), .kind(UVM_PREDICT_READ)
            ));
          end else begin
            `uvm_info(`gfn, "FIXME: Predict adc_chn_val_1.adc_chn_value_intr", UVM_NONE)
          end
        end
      end


      default: begin
        `uvm_error(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data, $sformatf(
                     "reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
    // Latest values
    m_adc_latest_values.delete();
    m_adc_interrupt_values.delete();
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

endclass
