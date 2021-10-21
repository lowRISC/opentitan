// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class ast_adc_monitor extends dv_base_monitor #(
    .ITEM_T (ast_adc_item),
    .CFG_T  (ast_adc_agent_cfg),
    .COV_T  (ast_adc_agent_cov)
  );

  protected ITEM_T m_address_phase_q [$]; // Queue of from the address phase

  protected int   m_channel_sel;            // Channel currently selected
  protected bit   m_channel_active;         // A channel has been seleced by channel_sel bus
  protected bit   m_channel_active_prev;    // m_channel_active delayed one cycle
  protected bit   m_channel_active_posedge; // Active channel selected this cycle
  protected logic m_data_valid_posedge;     // Positive edge detected on data_valid
  protected logic m_data_valid_prev;        // data_valid delayed one cycle

  `uvm_component_utils(ast_adc_monitor)

  // the base class provides the following handles for use:
  // ast_adc_agent_cfg: cfg
  // ast_adc_agent_cov: cov
  // uvm_analysis_port #(ast_adc_item): analysis_port

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    m_channel_sel = '1;
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
  endtask

  // Send a message via the IF
  virtual function void monitor_msg(string msg);
    cfg.vif.monitor_msg = msg;
  endfunction

  // Perform the address phase monitoring
  // Looks at channel_sel and pd
  virtual protected task address_phase_proc(uvm_phase phase);
    ITEM_T monitor_item;
    forever begin
      // Clock event
      @(cfg.vif.monitor_cb);


      if(cfg.vif.monitor_cb.adc_o.pd !== 0) begin // Power down
          m_channel_active = 0;
          m_channel_active_prev = 0;
          m_channel_active_posedge = 0;

          if( m_address_phase_q.size() ) begin
            // Uncompleted transactions in queue
            `uvm_error(`gfn,"Uncompleted transactions when powerdown asserted")
            // Clear queue
            m_address_phase_q.delete();
          end
          monitor_msg("Power Down");
      end else begin

        // Detect an active channel select - Only if a valid one hot request
        m_channel_active =  ( (|cfg.vif.monitor_cb.adc_o.channel_sel) &
          $onehot(cfg.vif.monitor_cb.adc_o.channel_sel) );

        // Detect positive edges on m_channel_active
        m_channel_active_posedge = m_channel_active &  ~m_channel_active_prev;

        // Delay m_channel_active for edge detection
        m_channel_active_prev = m_channel_active;

        if(m_channel_active_posedge) begin
          // Decode channel by taking the log to base 2 which will
          // give the index of the most significant asserted bit
          m_channel_sel = $clog2(cfg.vif.monitor_cb.adc_o.channel_sel);

          // Start transaction when a channel is selected
          monitor_item = ITEM_T::type_id::create("monitor_item");

          // Assign the channel
          monitor_item.channel = m_channel_sel;

          // Record the start time
          void'(monitor_item.begin_tr());

          // Put transaction on the queue for the data phase
          m_address_phase_q.push_back(monitor_item);

          monitor_msg($sformatf("Selected channel %0d", m_channel_sel));
        end // channel_sel changed

      end

    end
  endtask

  virtual protected task data_phase_proc(uvm_phase phase);
    ITEM_T monitor_item;
    forever begin
      // Clock event
      @(cfg.vif.monitor_cb);


      if(cfg.vif.monitor_cb.adc_o.pd !== 0) begin // Power down
          m_data_valid_posedge = 0;
          m_data_valid_prev    = 0;
          monitor_item         = null;
      end else begin
        // Detect positive edges on data_valid
        m_data_valid_posedge = ~m_data_valid_prev & cfg.vif.monitor_cb.adc_i.data_valid;
        m_data_valid_prev = cfg.vif.monitor_cb.adc_i.data_valid;

      if(m_data_valid_posedge === 1) begin
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
      m_channel_active = 0;
      m_channel_active_prev = 0;
      m_channel_active_posedge = 0;
      m_data_valid_posedge = 0;
      m_data_valid_prev = 0;
      monitor_msg("Exited reset");

      fork begin : isolation_proc
        fork
          address_phase_proc(phase);
          data_phase_proc(phase);
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




    // forever begin
    //   // Clock event
    //   @(cfg.vif.monitor_cb);





    //   if(cfg.vif.monitor_cb.rst_ni === 0) begin // Reset
    //     m_channel_sel = '1;
    //     m_channel_active = 0;
    //     m_channel_active_prev = 0;
    //     m_channel_active_posedge = 0;
    //     m_pd_prev = 0;
    //     m_pd_negedge = 0;

    //     // If just entered reset send mnessage to if
    //     if(!m_in_reset) begin
    //       monitor_msg("Entered reset");
    //       m_in_reset = 1;
    //     end

    //   end
    //   else begin
    //     // Detect positive edges on pd
    //     m_pd_negedge = ~cfg.vif.monitor_cb.adc_o.pd & m_pd_prev;
    //     m_pd_prev    = cfg.vif.monitor_cb.adc_o.pd;

    //     // Detect edges on data_valid
    //     m_data_valid_edge = m_data_valid_prev ^ cfg.vif.monitor_cb.adc_i.data_valid;
    //     m_data_valid_prev = cfg.vif.monitor_cb.adc_i.data_valid;

    //     // Detect an active channel select - Only if a valid one hot request
    //     m_channel_active =  ( (|cfg.vif.monitor_cb.adc_o.channel_sel) &
    //       $onehot(cfg.vif.monitor_cb.adc_o.channel_sel) );

    //     // Detect positive edges on m_channel_active
    //     m_channel_active_posedge = m_channel_active &  ~m_channel_active_prev;

    //     // Delay m_channel_active for edge detection
    //     m_channel_active_prev = m_channel_active;

    //     if(m_in_reset) begin // We were in reset
    //       monitor_msg("Exited reset");
    //       m_in_reset=0;
    //     end

    //     if(cfg.vif.monitor_cb.adc_o.pd !== 0) begin // Power down
    //       m_channel_active = 0;
    //       m_channel_active_prev = 0;
    //       m_channel_active_posedge = 0;
    //       monitor_msg("Power Down");
    //     end // Power down
    //     else begin
    //       if(m_pd_negedge === 1) begin
    //         monitor_msg("Power Up");
    //       end

    //       if(m_channel_active_posedge) begin
    //         // Decode channel by taking the log to base 2 which will
    //         // give the index of the most significant asserted bit
    //         m_channel_sel = $clog2(cfg.vif.monitor_cb.adc_o.channel_sel);

    //         // Start transaction when a channel is selected
    //         monitor_item = ITEM_T::type_id::create("monitor_item");
    //         // Record the start time
    //         void'(monitor_item.begin_tr());
    //       end // channel_sel changed

    //       if(m_data_valid_edge === 1) begin
    //         if (cfg.vif.monitor_cb.adc_i.data_valid === 1) begin // Rising edge
    //           if(monitor_item != null) begin
    //             // Sample the data
    //             monitor_item.channel = m_channel_sel;
    //             monitor_item.data    = cfg.vif.monitor_cb.adc_i.data;
    //             monitor_msg($sformatf("Sample data channel %0d", m_channel_sel));
    //           end
    //         end // Rising edge data_valid
    //         else if (cfg.vif.monitor_cb.adc_i.data_valid === 0) begin // Falling edge
    //           if(monitor_item != null) begin
    //             // Record end time
    //             monitor_item.end_tr();
    //             // Send to port
    //             analysis_port.write(monitor_item);

    //             // Set to null so we can detect responses without requests
    //             monitor_item = null;
    //             monitor_msg($sformatf("Transaction complete channel %0d", m_channel_sel));
    //           end // monitor_item not nulll
    //           else begin
    //             // Response without request
    //             `uvm_error(get_full_name(), "Spurious response");
    //             monitor_msg("Spurious response");
    //           end // monitor_item null
    //         end // Falling edge on data_valid
    //       end // Edge on data_valid
    //     end // Not power down
    //   end // Not reset
    // end // forever loop
  endtask
endclass
