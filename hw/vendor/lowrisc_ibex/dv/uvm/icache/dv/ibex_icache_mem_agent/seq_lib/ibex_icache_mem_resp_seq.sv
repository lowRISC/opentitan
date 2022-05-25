// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Slave response sequence

class ibex_icache_mem_resp_seq extends ibex_icache_mem_base_seq;

  // Non-null if this is an item after the first in a "combo" run, which runs several of these
  // sequences back-to-back. Must be set before pre_start to have any effect.
  ibex_icache_mem_resp_seq prev_sequence = null;

  protected ibex_icache_mem_model #(.BusWidth (32)) mem_model;

  // We pick new seeds when we spot a request (rather than when we spot a grant) to ensure that
  // any given fetch corresponds to exactly one seed. Unfortunately, there's a race if these two
  // things happen at one clock edge:
  //
  //    - Request for new address which gets a new seed
  //    - Grant of previous request
  //
  // If that happens, and the event scheduler happened to schedule the monitor to spot the request
  // before the grant, we might accidentally handle the grant with the new seed rather than the
  // old one, which would cause confusion in the scoreboard.
  //
  // To avoid this problem, we keep a queue of pending addresses along with their corresponding
  // seeds. When a grant message comes in, we know that we can look up the correct seed there,
  // discarding results until we find it.
  bit [63:0] pending_grants[$];
  bit [31:0] cur_seed = 0;

  `uvm_object_utils(ibex_icache_mem_resp_seq)
  `uvm_object_new

  task pre_start();
    super.pre_start();
    mem_model = new("mem_model", cfg.disable_mem_errs);

    // Take any pending grants and seed from a previous sequence
    if (prev_sequence) begin
      pending_grants = prev_sequence.pending_grants;
      cur_seed = prev_sequence.cur_seed;
    end
  endtask

  task body();
    ibex_icache_mem_req_item  req_item  = new("req_item");
    ibex_icache_mem_req_item  req_item2 = new("req_item2");
    ibex_icache_mem_resp_item resp_item = new("resp_item");

    forever begin
      // Wait for a transaction request. We use peek, handle the request, and then get (and drop)
      // the item. This means that if our sequence is killed in the middle of handling it, the item
      // will still be passed from the monitor to any later sequence.
      p_sequencer.request_fifo.get_peek_export.peek(req_item);

      take_gnt(resp_item, req_item);

      // Get and drop the request item now that we've dealt with it. To check that nothing has gone
      // wrong, make sure that the two items match.
      p_sequencer.request_fifo.get_peek_export.get(req_item2);
      `DV_CHECK_EQ_FATAL(req_item, req_item2)
    end
  endtask

  // Deal with a "req" event (the cache asks the memory system for data at an address, but we might
  // not have granted it yet)
  //
  // Start and randomize the response then take any new seed that comes out. Finally, fill in the
  // err signal based on the current seed.
  //
  task automatic take_req(ibex_icache_mem_resp_item resp_item,
                          ibex_icache_mem_req_item  req_item);


    // Warn the "grant side" to expect this fetch
    pending_grants.push_back({req_item.address, cur_seed});

    resp_item.is_grant = 1'b0;
    resp_item.address  = req_item.address;
    resp_item.rdata    = 'X;
    resp_item.err = 1'b0;

    start_item(resp_item);
    `DV_CHECK_RANDOMIZE_FATAL(resp_item)
    finish_item(resp_item);

  endtask : take_req

  // Deal with a "grant" event (the memory system has granted a memory request from the cache and
  // added the request to its internal pipeline)
  task automatic take_gnt(ibex_icache_mem_resp_item resp_item,
                          ibex_icache_mem_req_item  req_item);

    bit [31:0] tmp_seed;

    // Consume any new seeds. These will have been pushed into the sequencer's seed_fifo by the core
    // agent. Any new seed will apply to this request and all future requests (we need tmp_seed here
    // because otherwise the first failed call to try_get will trash the value we got).
    while(p_sequencer.seed_fifo.try_get(tmp_seed)) begin
      cur_seed = tmp_seed;
      `uvm_info(`gfn, $sformatf("New memory seed: 0x%08h", cur_seed), UVM_HIGH)
    end

    // Using the seed that we saw for the request, check the memory model for an error
    // at this address. On success, look up the memory data too.
    resp_item.is_grant = 1'b1;
    resp_item.err      = mem_model.is_mem_error(cur_seed, req_item.address, cfg.mem_err_shift);
    resp_item.address  = req_item.address;
    resp_item.rdata    = resp_item.err ? 'X : mem_model.read_data(cur_seed, req_item.address);

    // Use the response item as an entry in the sequence, randomising any delay
    start_item(resp_item);
    `DV_CHECK_RANDOMIZE_FATAL(resp_item)
    finish_item(resp_item);
  endtask : take_gnt

endclass
