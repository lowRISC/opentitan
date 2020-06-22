// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Drive the memory <-> icache interface
//
// There are 3 different signals getting driven here:
//
//    (1) GNT:     This toggles randomly, completely ignoring any other signals.
//    (2) PMP_ERR: This can be set as a result of taking a bad request.
//    (3) RDATA:   This gets set with response data some time after granting a request.

class ibex_icache_mem_driver
  extends dv_base_driver #(.ITEM_T (ibex_icache_mem_resp_item),
                           .CFG_T  (ibex_icache_mem_agent_cfg));

  int unsigned min_grant_delay = 0;
  int unsigned max_grant_delay = 10;

  mailbox #(ibex_icache_mem_resp_item) rdata_queue;
  mailbox #(bit [32:0])                req_queue;

  `uvm_component_utils(ibex_icache_mem_driver)
  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    rdata_queue   = new("rdata_queue");
    req_queue     = new("req_queue");
  endfunction

  virtual task reset_signals();
    ibex_icache_mem_resp_item resp;
    bit [32:0]                req;

    cfg.vif.reset();

    // Flush mailboxes of pending requests and responses
    while (req_queue.try_get(req)) ;
    while (rdata_queue.try_get(resp)) ;

  endtask

  virtual task get_and_drive();
    // None of these processes terminate
    fork
      drive_grant();
      take_requests();
      drive_pmp();
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
      if (!req.is_grant) begin
        // Push the address onto req_queue (which will be handled by drive_pmp).
        req_queue.put({req.err, req.address});
      end else begin
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

  // Drive the PMP line.
  //
  // This task samples from a "PMP" mailbox, which gets a new item from take_requests each time a
  // new request comes in whose address would be squashed by the PMP.
  //
  // Since this isn't synchronised with a clock edge, it's not really possible to avoid glitches and
  // to only add items when the "right" address has arrived. Instead, this task gets the address
  // that caused the error. As soon as req is low OR the address on the bus doesn't match, this
  // driver clears the address and exits. The idea is that if stuff gets out of sync for a delta
  // cycle or two, drive_pmp can discard items to catch up.
  task automatic drive_pmp();
    bit        err;
    bit [31:0] address;
    bit [32:0] data;

    forever begin
      req_queue.get(data);
      {err, address} = data;

      if (!cfg.vif.rst_n) continue;

      // If err is false, this is a request which shouldn't trigger a PMP error.
      if (!err) continue;

      // Otherwise, the address is the address that we expect to see on the interface.
      // If the req line is low, or the address doesn't match, skip this item.
      if ((!cfg.vif.req) || (cfg.vif.addr != address)) continue;

      // Fork into two processes. The first waits for something else to appear in the queue. The
      // second drives the line until it thinks the request is finished. The driver is stopped if we
      // see a new request come in.
      fork
        req_queue.peek(data);
        begin
          cfg.vif.pmp_err <= 1'b1;
          // Wait for a reset, an address change or req to de-assert
          @(negedge cfg.vif.rst_n or negedge cfg.vif.req or cfg.vif.addr);
        end
      join_any
      disable fork;
      cfg.vif.pmp_err <= 1'b0;
    end
  endtask

  // Watch for resets and call reset_signals as needed
  task automatic drive_resets();
    forever @(negedge cfg.vif.rst_n) reset_signals();
  endtask

endclass
