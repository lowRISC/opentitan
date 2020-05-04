// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Slave response sequence

class ibex_icache_mem_resp_seq extends ibex_icache_mem_base_seq;

  ibex_icache_mem_model #(.BusWidth (32)) mem_model;

  `uvm_object_utils(ibex_icache_mem_resp_seq)
  `uvm_object_new

  task pre_start();
    super.pre_start();
    mem_model = new("mem_model", cfg.disable_pmp_errs, cfg.disable_mem_errs);
  endtask

  task body();
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
    // To avoid this problem, we keep a FIFO of pending addresses along with their corresponding
    // seeds. When a grant message comes in, we know that we can look up the correct seed there.
    mailbox #(bit[63:0]) pending_grants = new("pending_grants");

    ibex_icache_mem_req_item  req_item  = new("req_item");
    ibex_icache_mem_resp_item resp_item = new("resp_item");

    bit [63:0] gnt_data;
    bit [31:0] gnt_addr, gnt_seed;

    bit [31:0] cur_seed = 0;

    forever begin
      // Wait for a transaction request.
      p_sequencer.request_fifo.get(req_item);

      if (!req_item.is_grant) begin
        // If this is a request (not a grant), take any new seed and then check the memory model for
        // a PMP error at this address. Add the address and its corresponding seed to the list of
        // pending grants.
        if (req_item.seed != 32'd0) begin
          `uvm_info(`gfn, $sformatf("New memory seed: 0x%08h", req_item.seed), UVM_HIGH)
          cur_seed = req_item.seed;
        end

        resp_item.is_grant = 1'b0;
        resp_item.err      = mem_model.is_pmp_error(cur_seed, req_item.address);
        resp_item.address  = req_item.address;
        resp_item.rdata    = 'X;

        pending_grants.put({req_item.address, cur_seed});

      end else begin
        // If this is a grant, search through the pending_grants mailbox to find the seed from the
        // request that matched.
        gnt_addr = req_item.address + 1;
        while (pending_grants.num() > 0) begin
          pending_grants.get(gnt_data);
          {gnt_addr, gnt_seed} = gnt_data;
          if (gnt_addr == req_item.address) break;
        end

        // If nothing went wrong, we should have found the right item and gnt_addr should now
        // equal req_item.address
        `DV_CHECK_FATAL(gnt_addr == req_item.address,
                        $sformatf("No pending grant for address 0x%08h.", req_item.address))

        // Using the seed that we saw for the request, check the memory model for a (non-PMP) error
        // at this address. On success, look up the memory data too.
        resp_item.is_grant = 1'b1;
        resp_item.err      = mem_model.is_mem_error(gnt_seed, req_item.address);
        resp_item.address  = req_item.address;
        resp_item.rdata    = resp_item.err ? 'X : mem_model.read_data(gnt_seed, req_item.address);
      end

      // Use the response item as an entry in the sequence, randomising any delay
      start_item(resp_item);
      `DV_CHECK_RANDOMIZE_FATAL(resp_item)
      finish_item(resp_item);
    end
  endtask

endclass
