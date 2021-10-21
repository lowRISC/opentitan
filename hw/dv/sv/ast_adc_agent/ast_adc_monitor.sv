// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ast_adc_monitor extends dv_base_monitor #(
    .ITEM_T (ast_adc_item),
    .CFG_T  (ast_adc_agent_cfg),
    .COV_T  (ast_adc_agent_cov)
  );

  protected ITEM_T m_address_phase_q [$]; // Queue of from the address phase

  `uvm_component_utils(ast_adc_monitor)

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
  endtask

  // Send a message via the IF
  virtual function void monitor_msg(string msg);
    cfg.vif.send_monitor_msg(msg);
  endfunction

  // Perform the address phase monitoring
  // Looks at channel_sel and pd
  virtual protected task request_phase_proc(uvm_phase phase);
    int    channel_sel;            // Channel currently selected
    bit    channel_active;         // A channel has been seleced by channel_sel bus
    bit    channel_active_prev;    // m_channel_active delayed one cycle
    bit    channel_active_posedge; // Active channel selected this cycle
    ITEM_T monitor_item;
    forever begin
      // Clock event
      @(cfg.vif.monitor_cb);


      if(cfg.vif.monitor_cb.adc_o.pd !== 0) begin // Power down
          channel_active = 0;
          channel_active_prev = 0;
          channel_active_posedge = 0;

          if( m_address_phase_q.size() ) begin
            // Uncompleted transactions in queue
            `uvm_error(`gfn,"Uncompleted transactions when powerdown asserted")
            // Clear queue
            m_address_phase_q.delete();
          end
          monitor_msg("Power Down");
      end else begin

        // Detect an active channel select - Only if a valid one hot request
        channel_active =  ( (|cfg.vif.monitor_cb.adc_o.channel_sel) &
          $onehot(cfg.vif.monitor_cb.adc_o.channel_sel) );

        // Detect positive edges on m_channel_active
        channel_active_posedge = channel_active &  ~channel_active_prev;

        // Delay m_channel_active for edge detection
        channel_active_prev = channel_active;

        if(channel_active_posedge) begin
          // Decode channel by taking the log to base 2 which will
          // give the index of the most significant asserted bit
          channel_sel = $clog2(cfg.vif.monitor_cb.adc_o.channel_sel);
          // Start transaction when a channel is selected
          monitor_item = ITEM_T::type_id::create("monitor_item");
          // Assign the channel
          monitor_item.channel = channel_sel;
          // Record the start time
          void'(monitor_item.begin_tr());
          // Put transaction on the queue for the data phase
          m_address_phase_q.push_back(monitor_item);
          monitor_msg($sformatf("Selected channel %0d", channel_sel));
        end // channel_sel changed

      end

    end
  endtask

  virtual protected task response_phase_proc(uvm_phase phase);
    logic data_valid_posedge;     // Positive edge detected on data_valid
    logic data_valid_prev;        // data_valid delayed one cycle
    ITEM_T monitor_item;
    forever begin
      // Clock event
      @(cfg.vif.monitor_cb);

      if(cfg.vif.monitor_cb.adc_o.pd !== 0) begin // Power down
          data_valid_posedge = 0;
          data_valid_prev    = 0;
          monitor_item         = null;
      end else begin
        // Detect positive edges on data_valid
        data_valid_posedge = ~data_valid_prev & cfg.vif.monitor_cb.adc_i.data_valid;
        data_valid_prev = cfg.vif.monitor_cb.adc_i.data_valid;
        if(data_valid_posedge === 1) begin
          if(m_address_phase_q.size()) begin
            monitor_item = m_address_phase_q.pop_front();
            // Sample the data
            monitor_item.data    = cfg.vif.monitor_cb.adc_i.data;
            // Record end time
            monitor_item.end_tr();
            // Send to port
            analysis_port.write(monitor_item);
            monitor_msg($sformatf("Sample data channel %0d", monitor_item.channel));
          end else begin
              // Response without request
              `uvm_error(get_full_name(), "Spurious response");
              monitor_msg("Spurious response");
          end
        end
      end
    end
  endtask


  // collect transactions forever - already forked in dv_base_moditor::run_phase
  virtual protected task collect_trans(uvm_phase phase);
    ITEM_T monitor_item;
    monitor_msg({get_full_name(), " Started"});
    forever begin
      wait(cfg.vif.rst_ni === 1);
      // Reset deasserted - initialise monitor
      m_address_phase_q.delete();
      monitor_msg("Exited reset");

      fork begin : isolation_proc
        fork
          request_phase_proc(phase);
          response_phase_proc(phase);
          begin : reset_proc
            // Wait for active reset
            @(negedge cfg.vif.rst_ni);
            monitor_msg("Entered reset");
          end
        join_any
        disable fork;
      end : isolation_proc
      join
    end // forever
  endtask
endclass
