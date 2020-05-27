// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Slave response sequence

class ibex_icache_mem_resp_seq extends ibex_icache_mem_base_seq;

  // Knobs
  //
  // gap_between_seeds is the expected number of memory fetches between each seed update.
  int unsigned gap_between_seeds = 499;

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
  protected bit [63:0] pending_grants[$];
  protected bit [31:0] cur_seed = 0;

  `uvm_object_utils(ibex_icache_mem_resp_seq)
  `uvm_object_new

  task pre_start();
    super.pre_start();
    mem_model = new("mem_model", cfg.disable_pmp_errs, cfg.disable_mem_errs);
  endtask

  task body();
    ibex_icache_mem_req_item  req_item  = new("req_item");
    ibex_icache_mem_resp_item resp_item = new("resp_item");

    // Set knob to control randomization
    resp_item.gap_between_seeds = gap_between_seeds;

    forever begin
      // Wait for a transaction request.
      p_sequencer.request_fifo.get(req_item);

      if (!req_item.is_grant) begin
        take_req(resp_item, req_item);
      end else begin
        take_gnt(resp_item, req_item);
      end
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

    resp_item.is_grant = 1'b0;
    resp_item.address  = req_item.address;
    resp_item.rdata    = 'X;

    start_item(resp_item);
    `DV_CHECK_RANDOMIZE_FATAL(resp_item)

    // Take any new seed (so it will apply to this request and all future requests)
    if (resp_item.seed != 32'd0) begin
      `uvm_info(`gfn, $sformatf("New memory seed: 0x%08h", resp_item.seed), UVM_HIGH)
      cur_seed = resp_item.seed;
    end

    // Finally, fill in the err signal
    resp_item.err = mem_model.is_pmp_error(cur_seed, req_item.address);

    // Warn the "grant side" to expect this fetch
    pending_grants.push_back({req_item.address, cur_seed});

    // And finish the item
    finish_item(resp_item);

  endtask : take_req

  // Deal with a "grant" event (the memory system has granted a memory request from the cache and
  // added the request to its internal pipeline)
  task automatic take_gnt(ibex_icache_mem_resp_item resp_item,
                          ibex_icache_mem_req_item  req_item);

    bit [63:0] gnt_data;
    bit [31:0] gnt_addr, gnt_seed;

    // Search through the pending_grants queue to find the seed from the request that matched. We
    // search from the back, rather than the front. This avoids problems if there were requests for
    // an address that never got granted: we always want the most recent request for this address.
    int i, N;
    N = pending_grants.size();
    for (i = 0; i < N; i++) begin
      {gnt_addr, gnt_seed} = pending_grants[N - 1 - i];
      if (gnt_addr == req_item.address)
        break;
    end

    // If i == N, we didn't find a hit. That's not supposed to happen.
    `DV_CHECK_FATAL(i < N,
                    $sformatf("No pending grant for address 0x%08h (%0d items in queue).",
                              req_item.address, N))

    // Otherwise, we have a hit at index N - 1 - i. Throw away all previous items in the queue. We
    // don't throw away this item, because it's possible to end up with repeated addresses in the
    // queue (if the cache asked for the same address twice in a row) and if we throw away the hit
    // the first time, we can't find it for the second grant.
    pending_grants = pending_grants[N - 1 - i:$];

    // Using the seed that we saw for the request, check the memory model for a (non-PMP) error
    // at this address. On success, look up the memory data too.
    resp_item.is_grant = 1'b1;
    resp_item.err      = mem_model.is_mem_error(gnt_seed, req_item.address);
    resp_item.address  = req_item.address;
    resp_item.rdata    = resp_item.err ? 'X : mem_model.read_data(gnt_seed, req_item.address);

    // Use the response item as an entry in the sequence, randomising any delay
    start_item(resp_item);
    `DV_CHECK_RANDOMIZE_FATAL(resp_item)
    finish_item(resp_item);
  endtask : take_gnt

endclass
