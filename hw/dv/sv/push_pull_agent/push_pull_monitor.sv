// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class push_pull_monitor #(parameter int HostDataWidth = 32,
                          parameter int DeviceDataWidth = HostDataWidth)
  extends dv_base_monitor #(
    .ITEM_T (push_pull_item#(HostDataWidth, DeviceDataWidth)),
    .CFG_T  (push_pull_agent_cfg#(HostDataWidth, DeviceDataWidth)),
    .COV_T  (push_pull_agent_cov#(HostDataWidth, DeviceDataWidth))
  );
  `uvm_component_param_utils(push_pull_monitor#(HostDataWidth, DeviceDataWidth))

  // the base class provides the following handles for use:
  // push_pull_agent_cfg: cfg
  // push_pull_agent_cov: cov
  // uvm_analysis_port #(ITEM_T): analysis_port
  // uvm_analysis_port #(ITEM_T): req_analysis_port;

  `uvm_component_new
  bit in_reset;

  task run_phase(uvm_phase phase);
    @(posedge cfg.vif.rst_n);
    fork
      handle_reset();
      collect_valid_trans();
      // We only need to monitor incoming requests if the agent is configured
      // in device mode and is using Pull protocol.
      if (cfg.if_mode == dv_utils_pkg::Device &&
          cfg.agent_type == PullAgent) begin
        collect_request();
      end
    join_none
  endtask

  virtual protected task handle_reset();
    forever begin
      @(negedge cfg.vif.rst_n);
      in_reset = 1;
      // TODO: sample any reset-related covergroups
      @(posedge cfg.vif.rst_n);
      in_reset = 0;
    end
  endtask

  // TODO : sample covergroups
  virtual protected task collect_valid_trans();
    push_pull_item#(HostDataWidth, DeviceDataWidth) item;
    bit valid_txn;
    forever begin
      @(cfg.vif.mon_cb);
      if (cfg.agent_type == PushAgent) begin
        if (cfg.vif.mon_cb.ready && cfg.vif.mon_cb.valid) begin
          valid_txn = 1'b1;
          // TODO: sample covergroups
        end
      end else begin
        if (cfg.vif.mon_cb.req && cfg.vif.mon_cb.ack) begin
          valid_txn = 1'b1;
          // TODO: sample covergroups
        end
      end
      if (valid_txn) begin
        item = push_pull_item#(HostDataWidth, DeviceDataWidth)::type_id::create("item");
        item.d_data = cfg.vif.mon_cb.d_data;
        item.h_data = cfg.vif.mon_cb.h_data;
        `uvm_info(`gfn,
                  $sformatf("[%0s] transaction detected: h_data[0x%0x], d_data[0x%0x]",
                            cfg.agent_type, item.h_data, item.d_data), UVM_HIGH)
        analysis_port.write(item);
        valid_txn = 1'b0;
      end
    end
  endtask

  // This task is only used for device agents using the Pull protocol.
  // It will pick up any incoming requests from the DUT and send a signal to the
  // sequencer (in the form of a sequence item), which will then be forwarded to
  // the sequence, which then generates the appropriate response item.
  //
  // TODO: This assumes no requests can be dropped, and might need to be fixed
  //       if this is not allowed.
  virtual protected task collect_request();
    push_pull_item#(HostDataWidth, DeviceDataWidth) item;
    forever begin
      @(cfg.vif.mon_cb);
      if (cfg.vif.req) begin
        `uvm_info(`gfn, "detected pull request", UVM_HIGH)
        // TODO: sample any covergroups
        item = push_pull_item#(HostDataWidth, DeviceDataWidth)::type_id::create("item");
        req_analysis_port.write(item);
        // After picking up a request, wait until a response is sent before
        // detecting another request, as this is not a pipelined protocol.
        `DV_SPINWAIT_EXIT(while (!cfg.vif.mon_cb.ack) @(cfg.vif.mon_cb);,
                          wait(in_reset))
       end
    end
  endtask

  // update ok_to_end to prevent simulation from finishing when
  // there is any activity on the bus.
  virtual task monitor_ready_to_end();
    forever begin
      @(cfg.vif.mon_cb);
      if (cfg.agent_type == PushAgent) begin
        ok_to_end = (cfg.vif.valid == 0);
      end else begin
        ok_to_end = (cfg.vif.req == 0) && (cfg.vif.ack == 0);
      end
    end
  endtask

endclass
