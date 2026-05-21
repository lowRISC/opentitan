// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This driver sends items that represent responses from KMAC

class kmac_app_device_driver extends dv_base_driver #(.ITEM_T (kmac_app_rsp_item),
                                                      .CFG_T (kmac_app_agent_cfg));
  `uvm_component_utils(kmac_app_device_driver)

  // Port that sends generated request items. This should be connected to an instance of
  // kmac_app_device_sequencer, which can use it to trigger items in a reactive response sequence.
  // Those items will come back to this driver.
  uvm_analysis_port#(kmac_app_req_packet_item) m_req_port;

  extern function new(string name, uvm_component parent);
  extern task run_phase(uvm_phase phase);

  // Consume items from the sequencer and drive them (task from dv_base_driver)
  extern task get_and_drive();

  // Called when entering reset (task from dv_base_driver)
  extern task on_enter_reset();

  // Invalidate all signals (clearing done and setting other values to 'x)
  extern local task invalidate_signals();

  // Drive the ready signal (allowing the agent's emulated device to be given requests)
  extern local task drive_ready();

  // Drive the ready signal when there is not a request being handled.
  //
  // This runs until it sees a request valid & ready where the last signal is true. It may be killed
  // at any time (if a reset is asserted).
  //
  // If there is a request, it is captured and written as an item to m_req_port.
  extern local task drive_ready_until_req();

  // Drive the ready signal to be low and wait to see a response done signal
  //
  // This may be killed at any time (if a reset is asserted).
  extern local task drive_ready_low_until_rsp();
endclass

function kmac_app_device_driver::new(string name, uvm_component parent);
  super.new(name, parent);
  m_req_port = new("m_req_port", this);
endfunction

task kmac_app_device_driver::run_phase(uvm_phase phase);
  fork
    super.run_phase(phase);
    drive_ready();
  join
endtask

task kmac_app_device_driver::get_and_drive();
  forever begin
    seq_item_port.get_next_item(req);
    $cast(rsp, req.clone());
    rsp.set_id_info(req);

    // Wait for m_delay cycles before we respond
    cfg.vif.wait_cycles(rsp.m_delay);

    if (!cfg.in_reset) begin
      cfg.vif.device_cb.done          <= 1;
      cfg.vif.device_cb.digest_share0 <= rsp.m_digest_share0;
      cfg.vif.device_cb.digest_share1 <= rsp.m_digest_share1;
      cfg.vif.device_cb.error         <= rsp.m_error;

      // Wait for the next clock edge (so that the item is sent)
      cfg.vif.wait_cycles(1);
    end

    // We've either sent the response or have seen a reset. Invalidate any response either way
    invalidate_signals();

    seq_item_port.item_done();
  end
endtask

task kmac_app_device_driver::on_enter_reset();
  invalidate_signals();
endtask

task kmac_app_device_driver::invalidate_signals();
  cfg.vif.device_cb.done          <= 0;
  cfg.vif.device_cb.digest_share0 <= 'x;
  cfg.vif.device_cb.digest_share1 <= 'x;
  cfg.vif.device_cb.error         <= 'x;
endtask

task kmac_app_device_driver::drive_ready();
  forever begin
    // Clear the request ready signal at the start of the reset
    cfg.vif.device_cb.ready <= 0;

    wait (!cfg.in_reset);
    fork : isolation_fork begin
      fork
        wait (cfg.in_reset);
        forever begin
          drive_ready_until_req();
          drive_ready_low_until_rsp();
        end
      join_any
      disable fork;
    end join
  end
endtask

task kmac_app_device_driver::drive_ready_until_req();
  bit ready;
  int unsigned low_counter = 0;

  kmac_app_req_packet_item req_pkt = kmac_app_req_packet_item::type_id::create("req_pkt");

  forever begin
    // Did we see a request (valid and ready) on the previous cycle?
    if (cfg.vif.mon_cb.req_valid && cfg.vif.mon_cb.req_ready) begin
      // Create an item to represent the request that we have captured
      kmac_app_req_item req = kmac_app_req_item::type_id::create("req");

      req.m_last = cfg.vif.mon_cb.req_last;
      req.m_data = cfg.vif.mon_cb.req_data;

      // Count the bytes asserted in the request
      for (int unsigned i = 0; i < (AppDigestW + 7) / 8; i++) begin
        if (cfg.vif.mon_cb.req_strb[i]) req.m_num_bytes++;
      end

      req_pkt.m_reqs.push_back(req);

      // If the last flag is set then this is the end of a request. Send the item that we have
      // assembled through m_req_port and finish.
      if (req.m_last) begin
        m_req_port.write(req_pkt);
        break;
      end
    end

    if (low_counter >= cfg.max_idle_time_not_ready) begin
      ready = 1;
    end else begin
      ready = $urandom_range(0, 99) < cfg.idle_ready_pct;
    end

    cfg.vif.device_cb.ready <= ready;

    if (!ready) begin
      low_counter++;
    end else begin
      low_counter = 0;
    end

    @(cfg.vif.device_cb);
  end
endtask

task kmac_app_device_driver::drive_ready_low_until_rsp();
  cfg.vif.device_cb.ready <= 0;
  while (cfg.vif.mon_cb.rsp_done !== 1'b1) @(cfg.vif.mon_cb);
endtask
