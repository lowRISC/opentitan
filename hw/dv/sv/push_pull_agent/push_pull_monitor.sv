// Copyright lowRISC contributors (OpenTitan project).
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

  task run_phase(uvm_phase phase);
    @(posedge cfg.vif.rst_n);
    cfg.in_reset = 0;
    fork
      monitor_reset();
      collect_trans();
      // Collect partial pull reqs for the reactive pull device agent.
      collect_pull_req();
      collect_cov();
    join_none
  endtask

  virtual protected task monitor_reset();
    forever begin
      @(negedge cfg.vif.rst_n);
      cfg.in_reset = 1;
      @(posedge cfg.vif.rst_n);
      cfg.in_reset = 0;
    end
  endtask

  // Shorthand for restarting forever loop on reset detection.
  `define WAIT_FOR_RESET    \
    if (cfg.in_reset) begin \
      wait (!cfg.in_reset); \
      continue;             \
    end

  // Collect fully-completed transactions.
  //
  // TODO : sample covergroups
  virtual protected task collect_trans();
    if (cfg.agent_type == PushAgent) begin
      forever begin
        @(cfg.vif.mon_cb);
        `WAIT_FOR_RESET
        if (cfg.vif.mon_cb.ready && cfg.vif.mon_cb.valid) begin
          create_and_write_item();
        end
      end
    end else begin
      forever begin
        @(cfg.vif.mon_cb);
        `WAIT_FOR_RESET
        if (cfg.vif.mon_cb.req && cfg.vif.mon_cb.ack) begin
          create_and_write_item();
          // Wait for req to de-assert in case of four-phase handshake.
          if (cfg.pull_handshake_type == FourPhase) begin
            `uvm_info(`gfn, "Waiting for 4-phase req-ack to de-asssert", UVM_HIGH)
            `DV_SPINWAIT_EXIT(while (cfg.vif.mon_cb.ack) @(cfg.vif.mon_cb);,
                              wait (cfg.in_reset))
          end
        end
      end
    end
  endtask

  // Collects partial pull requests.
  //
  // This task is only used for device agents using the Pull protocol.
  // It will pick up any incoming requests from the DUT and send a signal to the
  // sequencer (in the form of a sequence item), which will then be forwarded to
  // the sequence, which then generates the appropriate response item.
  //
  // TODO: This assumes requests cannot be dropped, and might need to be fixed
  //       if this is allowed.
  virtual protected task collect_pull_req();
    push_pull_item#(HostDataWidth, DeviceDataWidth) item;

    if (!(cfg.agent_type == PullAgent && cfg.if_mode == dv_utils_pkg::Device)) return;
    forever begin
      @(cfg.vif.mon_cb);
      `WAIT_FOR_RESET
      if (cfg.vif.mon_cb.req) begin
        `uvm_info(`gfn, $sformatf("[%0s] pull req detected", cfg.agent_type), UVM_HIGH)
        // TODO: sample any covergroups
        item = push_pull_item#(HostDataWidth, DeviceDataWidth)::type_id::create("item");
        item.h_data = cfg.vif.mon_cb.h_data;
        req_analysis_port.write(item);
        // After picking up a request, wait until a response is sent before
        // detecting another request, as this is not a pipelined protocol.
        `DV_SPINWAIT_EXIT(while (!cfg.vif.mon_cb.ack) @(cfg.vif.mon_cb);,
                          wait (cfg.in_reset))
        if (cfg.pull_handshake_type == FourPhase) begin
          `DV_SPINWAIT_EXIT(while (cfg.vif.mon_cb.ack) @(cfg.vif.mon_cb);,
                            wait (cfg.in_reset))
        end
      end
    end
  endtask

  virtual protected task collect_cov();
    if (cfg.en_cov) begin
      if (cfg.agent_type == PushAgent) begin
        forever @(cfg.vif.mon_cb.ready or cfg.vif.mon_cb.valid) begin
          `WAIT_FOR_RESET
          cov.m_valid_ready_cg.sample(cfg.vif.mon_cb.ready, cfg.vif.mon_cb.valid);
        end // forever
      end else begin // PullAgent
        forever @(cfg.vif.mon_cb.req or cfg.vif.mon_cb.ack) begin
          `WAIT_FOR_RESET
          cov.m_req_ack_cg.sample(cfg.vif.mon_cb.req, cfg.vif.mon_cb.ack);
        end // forever
      end // PushAgent or PullAgent
    end // cfg.en_cov
  endtask

  `undef WAIT_FOR_RESET

  // Creates and writes the item to the analysis_port.
  //
  // The onus is on the caller to invoke this function at the right time -
  // i.e. when the transaction is valid.
  virtual protected function void create_and_write_item();
    push_pull_item#(HostDataWidth, DeviceDataWidth) item;
    item = push_pull_item#(HostDataWidth, DeviceDataWidth)::type_id::create("item");
    item.d_data = cfg.vif.mon_cb.d_data;
    item.h_data = cfg.vif.mon_cb.h_data;
    `uvm_info(`gfn,
              $sformatf("[%0s] transaction detected: h_data[0x%0x], d_data[0x%0x]",
                        cfg.agent_type, item.h_data, item.d_data), UVM_HIGH)
    analysis_port.write(item);
  endfunction

  // Detects periods of inactivity for the ok_to_end watchdog.
  //
  // Set ok_to_end bit to detect inactivity on the bus. Spawned by
  // dv_base_monitor as a thread towards the end of run_phase.
  virtual task monitor_ready_to_end();
    forever begin
      @(cfg.vif.mon_cb);
      if (cfg.agent_type == PushAgent) begin
        ok_to_end = !cfg.vif.mon_cb.valid;
      end else begin
        ok_to_end = !cfg.vif.mon_cb.req && !cfg.vif.mon_cb.ack;
      end
    end
  endtask

endclass
