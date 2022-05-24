// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Drive the memory <-> icache interface
//
// There are 2 different signals getting driven here:
//
//    (1) GNT:     This toggles randomly, completely ignoring any other signals.
//    (2) RDATA:   This gets set with response data some time after granting a request.

class ibex_icache_mem_driver
  extends dv_base_driver #(.ITEM_T (ibex_icache_mem_resp_item),
                           .CFG_T  (ibex_icache_mem_agent_cfg));

  int unsigned min_grant_delay = 0;
  int unsigned max_grant_delay = 10;

  mailbox #(ibex_icache_mem_resp_item) rdata_queue;

  `uvm_component_utils(ibex_icache_mem_driver)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    rdata_queue   = new("rdata_queue");
  endfunction

  virtual task reset_signals();
    ibex_icache_mem_resp_item resp;
    bit [32:0]                req;

    cfg.vif.reset();

    // Flush mailboxes of pending requests and responses
    while (rdata_queue.try_get(resp)) ;

  endtask

  virtual task get_and_drive();
    // None of these processes terminate
    fork
      drive_grant();
      take_requests();
      drive_responses();
      drive_resets();
    join
  endtask

  // Drive the grant line. This toggles independently of any other signal on the bus.
  task automatic drive_grant();
    int gnt_delay;

    forever begin
      // Pick a number of cycles for the grant line to be low
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(gnt_delay,
                                         gnt_delay dist {
                                           min_grant_delay                         :/ 3,
                                           [min_grant_delay+1 : max_grant_delay-1] :/ 1,
                                           max_grant_delay                         :/ 1
                                         };)
      repeat(gnt_delay) @(cfg.vif.driver_cb);

      // Set the grant line high for a cycle then go around again. Note that the grant line will be
      // high for two consecutive cycles if gnt_delay is 0.
      cfg.vif.driver_cb.gnt <= 1'b1;
      @(cfg.vif.driver_cb);
      cfg.vif.driver_cb.gnt <= 1'b0;
    end
  endtask

  // Take requests from the sequencer.
  task automatic take_requests();
    forever begin
      seq_item_port.get_next_item(req);
      `uvm_info(`gfn, $sformatf("rcvd item:\n%0s", req.sprint()), UVM_HIGH)

      // Is this a request or a grant?
      if (req.is_grant) begin
        // If a grant, we take a copy and add it to the response queue (handled by drive_responses)
        $cast(rsp, req.clone());
        rsp.set_id_info(req);
        rdata_queue.put(rsp);
      end

      seq_item_port.item_done();
    end
  endtask

  // Drive the rdata/valid/err response lines
  task automatic drive_responses();
    int unsigned delay;
    ibex_icache_mem_resp_item item;

    forever begin
      rdata_queue.get(item);
      if (!cfg.vif.rst_n) continue;

      cfg.vif.wait_clks(item.delay);
      if (!cfg.vif.rst_n) continue;

      cfg.vif.send_response(item.err, item.rdata);
    end
  endtask

  // Watch for resets and call reset_signals as needed
  task automatic drive_resets();
    forever @(negedge cfg.vif.rst_n) reset_signals();
  endtask

endclass
