// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class adc_ctrl_scoreboard extends cip_base_scoreboard #(
    .CFG_T(adc_ctrl_env_cfg),
    .RAL_T(adc_ctrl_reg_block),
    .COV_T(adc_ctrl_env_cov)
  );

  // Analysis FIFO for ADC monitor transactions
  uvm_tlm_analysis_fifo #(ast_adc_item)   m_ast_adc_fifo;

  // Queue of ADC monitor transactions
  protected ast_adc_item m_ast_adc_item_q[$];

  // Latest ast_adc_item
  protected ast_adc_item m_ast_adc_item;

  // Latest value for each channel
  protected ast_adc_value_t m_adc_latest_values[int];

  // Interrupt value for each channel
  protected ast_adc_value_t m_adc_interrupt_values[int];

  // Sampled interrupts
  protected logic [NUM_MAX_INTERRUPTS-1:0] m_interrupts;

  // Our interrupt line
  protected logic m_interrupt;

  // Interrupt asserted this ADC sample
  protected logic m_interrupt_posedge;


  `uvm_component_utils(adc_ctrl_scoreboard)

  // local variables

  // TLM agent fifos

  // local queues to hold incoming packets pending comparison

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    m_ast_adc_fifo = new("m_ast_adc_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_ast_adc_fifo();
      monitor_intr_proc();
    join_none
  endtask


  // Monitor interrupt line
  protected virtual task monitor_intr_proc();
    forever begin
      @(posedge cfg.m_ast_adc_agent_cfg.vif.clk_i);
      // Sample the interrupt lines
      m_interrupts = cfg.intr_vif.sample();
      `uvm_info(`gfn, $sformatf("interrupts=%b", m_interrupts), UVM_DEBUG)

      // Detect a positive edge on our interrupt line (set in config object)
      m_interrupt_posedge = ~m_interrupt & m_interrupts[cfg.intr_idx];
      m_interrupt         = m_interrupts[cfg.intr_idx];

      // If we see a positive edge on the interrupt line capture the lastest values
      if(m_interrupt_posedge) begin
        foreach(m_adc_latest_values[channel]) begin
          m_adc_interrupt_values[channel] = m_adc_latest_values[channel];
        end
      end

    end
  endtask


  // Deal with AST ADC monitor packet
  protected virtual task process_ast_adc_fifo();
    forever begin
      // Get next ADC transaction - blocking
      m_ast_adc_fifo.get(m_ast_adc_item);
      // Add to queue
      m_ast_adc_item_q.push_back(m_ast_adc_item);
      // Set latest value
      m_adc_latest_values[m_ast_adc_item.channel] = m_ast_adc_item.data;
      `uvm_info(`gfn, {"process_m_ast_adc_fifo:", m_ast_adc_item.sprint()}, UVM_LOW)
    end
  endtask 

  // Return the latest ADC value for the respective channel
  virtual function ast_adc_value_logic_t get_adc_latest_value(input int channel);
    return m_adc_latest_values[channel];
  endfunction

  // Return the latest ADC interrupt value for the respective channel
  virtual function ast_adc_value_logic_t get_adc_interrupt_value(input int channel);
    // TODO: Fix to return the latest before the interrupt signal
    return m_adc_interrupt_values[channel];
  endfunction


  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit     do_read_check   = 1'b1;
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = ral.get_word_aligned_addr(item.a_addr);

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end
    else begin
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
      "adc_intr_status" : begin
        do_read_check = 1'b0;
      end
      "adc_intr_ctl" : begin
        // FIXME
      end
      "adc_en_ctl" : begin
        // FIXME
      end

      "adc_chn0_filter_ctl_0", "adc_chn0_filter_ctl_1", "adc_chn0_filter_ctl_2", "adc_chn0_filter_ctl_3", 
          "adc_chn0_filter_ctl_4", "adc_chn0_filter_ctl_5", "adc_chn0_filter_ctl_6", "adc_chn0_filter_ctl_7", 
          "adc_chn1_filter_ctl_0", "adc_chn1_filter_ctl_1", "adc_chn1_filter_ctl_2", "adc_chn1_filter_ctl_3", 
          "adc_chn1_filter_ctl_4", "adc_chn1_filter_ctl_5", "adc_chn1_filter_ctl_6", "adc_chn1_filter_ctl_7"
          : begin
        // FIXME
      end  

      "adc_chn_val_0": begin
        // Predict values
        if(addr_phase_read) begin
          // Latest ADC value
          void'(ral.adc_chn_val[0].adc_chn_value.predict(
            .value(get_adc_latest_value(0)),
            .kind(UVM_PREDICT_READ)
          ));
          
          // Interrupt ADC value
          `uvm_info(`gfn, $sformatf("adc_en_ctl.oneshot_mode=%0x", 
            ral.adc_en_ctl.oneshot_mode.get_mirrored_value()),UVM_HIGH)
          if(ral.adc_en_ctl.oneshot_mode.get_mirrored_value() == 1) begin
            // In oneshot mode latest and interrupt fields are the same
            void'(ral.adc_chn_val[0].adc_chn_value_intr.predict(
              .value(get_adc_latest_value(0)),
              .kind(UVM_PREDICT_READ)
              ));    
          end
          else begin
            `uvm_info(`gfn, "FIXME: Predict adc_chn_val_0.adc_chn_value_intr", UVM_NONE)
          end  
        end
      end
      "adc_chn_val_1": begin
        // Predict values
        if(addr_phase_read) begin
          
          void'(ral.adc_chn_val[1].adc_chn_value.predict(
            .value(get_adc_latest_value(1)),
            .kind(UVM_PREDICT_READ)
          ));
          
          // Interrupt ADC value
          if(ral.adc_en_ctl.oneshot_mode.get_mirrored_value() == 1) begin
            // In oneshot mode latest and interrupt fields are the same
            void'(ral.adc_chn_val[1].adc_chn_value_intr.predict(
              .value(get_adc_latest_value(1)),
              .kind(UVM_PREDICT_READ)
            ));
          end
          else begin
            `uvm_info(`gfn, "FIXME: Predict adc_chn_val_1.adc_chn_value_intr", UVM_NONE)
          end     
        end

        // FIXME
        // Ignore for now
        `uvm_info(`gfn, "FIXME: Disabled read check for adc_chn_val_1", UVM_NONE)
        do_read_check = 1'b0;
      end


      default: begin
        `uvm_error(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read) begin
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

    // AST ADC FIFO
    m_ast_adc_fifo.flush();
    // AST ADC Queue
    m_ast_adc_item_q.delete();
    // Latest values
    m_adc_latest_values.delete();
    m_adc_interrupt_values.delete(); 
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

endclass
