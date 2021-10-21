// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ast_adc_driver extends dv_base_driver #(.ITEM_T(ast_adc_item),
                                              .CFG_T (ast_adc_agent_cfg));

  protected ITEM_T m_active_requests [AdcChannels] [$];
  protected int unsigned m_channel;

  // Most recent ADC value sent for each channel
  bit [AdcDataWidth-1 : 0]   m_ast_adc_value [AdcChannels];

  `uvm_component_utils(ast_adc_driver)

  // the base class provides the following handles for use:
  // ast_adc_agent_cfg: cfg

  `uvm_component_new

  virtual task run_phase(uvm_phase phase);
    fork drive_signals();
    join_none
    // base class forks off reset_signals() and get_and_drive() tasks
    super.run_phase(phase);
  endtask

    // Send a message via the IF
  virtual function void driver_msg(string msg);
    cfg.vif.driver_msg = msg;
  endfunction


  // reset signals
  virtual task reset_signals();
    cfg.vif.adc_i.data_valid <= 0;
    cfg.vif.adc_i.data       <= 'X;
  endtask

  // drive trans received from sequencer
  virtual task get_and_drive();
    forever begin
      seq_item_port.get_next_item(req);
      accept_tr(req);
      `uvm_info(`gfn, $sformatf("rcvd item:\n%0s", req.sprint()), UVM_HIGH)

      if(req.channel < AdcChannels) begin
        // Put request on the queue if there is room
        // otherwise wait
        wait(m_active_requests[req.channel].size() < MaxOutstandingTrans);
        m_active_requests[req.channel].push_back(req);
      end
      else begin // Out of range
        `uvm_error(get_full_name(),
          $sformatf("Invalid channel in request %0d maximum %0d", req.channel, AdcChannels-1))
      end

      // Item done
      `uvm_info(`gfn, "item done", UVM_HIGH)
      seq_item_port.item_done();
    end
  endtask


  // Drive the signals
  protected virtual task drive_signals();
    ITEM_T drive_req;
    forever begin
      // Clock event
      @(cfg.vif.driver_cb);

      // Wait for power down deasserted
      while(cfg.vif.driver_cb.adc_o.pd !== 0) begin
        driver_msg("Wait Power Up ");
        @(cfg.vif.driver_cb);
      end

      // Wait for channel_sel[x] asserted
      while((cfg.vif.driver_cb.adc_o.pd === 0) &&
        ((|cfg.vif.driver_cb.adc_o.channel_sel) !== 1)) begin
        driver_msg("Wait Selected");
        @(cfg.vif.driver_cb);
      end

      // Start again if power goes down
      if(cfg.vif.driver_cb.adc_o.pd !== 0)
        continue;

      // Decode channel_sel into an index
      m_channel = $clog2(cfg.vif.driver_cb.adc_o.channel_sel);

      driver_msg($sformatf("Selected %0d waiting random delay", m_channel));

      // Random delay
      // Maximum and minimum delays defined in config object
      repeat($urandom_range(cfg.resp_dly_max, cfg.resp_dly_min))
        @(cfg.vif.driver_cb);

      if(!m_active_requests[m_channel].size()) begin
        driver_msg($sformatf("Selected %0d waiting for request", m_channel));
      end

      // wait for a request for this channel
      while((!m_active_requests[m_channel].size()) &&
        (cfg.vif.driver_cb.adc_o.pd === 0)) begin
        @(cfg.vif.driver_cb);
      end

      driver_msg($sformatf("Driving data for channel %0d", m_channel));
      if(cfg.vif.driver_cb.adc_o.pd === 0) begin
          drive_req = m_active_requests[m_channel].pop_front();

        if(drive_req != null) begin

          // Drive the interface
          cfg.vif.driver_cb.adc_i <= '{data: drive_req.data, data_valid:1};

          // Record start of the transaction
          void'(begin_tr(drive_req));
        end
      end

      // Wait for channel_sel to go inactive
      while((cfg.vif.driver_cb.adc_o.pd === 0) &&
        ((|cfg.vif.driver_cb.adc_o.channel_sel) === 1)) begin
        @(cfg.vif.driver_cb);
      end

      if(drive_req != null) begin
        // Record the end of the transaction
        end_tr(drive_req);

        // Create response
        $cast(rsp, drive_req.clone());
        rsp.set_id_info(drive_req);

        // Send response back to the sequencer
        seq_item_port.put(rsp);
      end

      // Deassert data_valid and make data bus X
      cfg.vif.driver_cb.adc_i <= '{data: 'X, data_valid:0};
      drive_req = null;

    end
  endtask

endclass
