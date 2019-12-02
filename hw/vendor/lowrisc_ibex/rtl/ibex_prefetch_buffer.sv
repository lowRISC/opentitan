// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Prefetcher Buffer for 32 bit memory interface
 *
 * Prefetch Buffer that caches instructions. This cuts overly long critical
 * paths to the instruction cache.
 */
module ibex_prefetch_buffer (
    input  logic        clk_i,
    input  logic        rst_ni,

    input  logic        req_i,

    input  logic        branch_i,
    input  logic [31:0] addr_i,


    input  logic        ready_i,
    output logic        valid_o,
    output logic [31:0] rdata_o,
    output logic [31:0] addr_o,
    output logic        err_o,


    // goes to instruction memory / instruction cache
    output logic        instr_req_o,
    input  logic        instr_gnt_i,
    output logic [31:0] instr_addr_o,
    input  logic [31:0] instr_rdata_i,
    input  logic        instr_err_i,
    input  logic        instr_pmp_err_i,
    input  logic        instr_rvalid_i,

    // Prefetch Buffer Status
    output logic        busy_o
);

  localparam int unsigned NUM_REQS  = 2;

  logic                valid_new_req, valid_req;
  logic                valid_req_d, valid_req_q;
  logic                discard_req_d, discard_req_q;
  logic                gnt_or_pmp_err, rvalid_or_pmp_err;
  logic [NUM_REQS-1:0] rdata_outstanding_n, rdata_outstanding_s, rdata_outstanding_q;
  logic [NUM_REQS-1:0] branch_discard_n, branch_discard_s, branch_discard_q;
  logic [NUM_REQS-1:0] rdata_pmp_err_n, rdata_pmp_err_s, rdata_pmp_err_q;

  logic [31:0]         stored_addr_d, stored_addr_q;
  logic                stored_addr_en;
  logic [31:0]         fetch_addr_d, fetch_addr_q;
  logic                fetch_addr_en;
  logic [31:0]         instr_addr, instr_addr_w_aligned;
  logic                instr_or_pmp_err;

  logic                fifo_valid;
  logic                fifo_ready;
  logic                fifo_clear;

  ////////////////////////////
  // Prefetch buffer status //
  ////////////////////////////

  assign busy_o = (|rdata_outstanding_q) | instr_req_o;

  //////////////////////////////////////////////
  // Fetch fifo - consumes addresses and data //
  //////////////////////////////////////////////

  // Instruction fetch errors are valid on the data phase of a request
  // PMP errors are generated in the address phase, and registered into a fake data phase
  assign instr_or_pmp_err = instr_err_i | rdata_pmp_err_q[0];

  // A branch will invalidate any previously fetched instructions.
  // Note that the FENCE.I instruction relies on this flushing behaviour on branch. If it is
  // altered the FENCE.I implementation may require changes.
  assign fifo_clear = branch_i;

  ibex_fetch_fifo #(
    .NUM_REQS (NUM_REQS)
  ) fifo_i (
      .clk_i                 ( clk_i             ),
      .rst_ni                ( rst_ni            ),

      .clear_i               ( fifo_clear        ),

      .in_valid_i            ( fifo_valid        ),
      .in_addr_i             ( addr_i            ),
      .in_rdata_i            ( instr_rdata_i     ),
      .in_err_i              ( instr_or_pmp_err  ),
      .in_ready_o            ( fifo_ready        ),


      .out_valid_o           ( valid_o           ),
      .out_ready_i           ( ready_i           ),
      .out_rdata_o           ( rdata_o           ),
      .out_addr_o            ( addr_o            ),
      .out_err_o             ( err_o             )
  );

  //////////////
  // Requests //
  //////////////

  // Make a new request any time there is space in the FIFO, and space in the request queue
  assign valid_new_req = req_i & (fifo_ready | branch_i) & ~rdata_outstanding_q[NUM_REQS-1];
  assign valid_req = valid_req_q | valid_new_req;

  // If a request address triggers a PMP error, the external bus request is suppressed. We might
  // therefore never receive a grant for such a request. The grant is faked in this case to make
  // sure the request proceeds and the error is pushed to the FIFO.
  assign gnt_or_pmp_err = instr_gnt_i | instr_pmp_err_i;

  // As with the grant, the rvalid must be faked for a PMP error, since the request was suppressed.
  assign rvalid_or_pmp_err = rdata_outstanding_q[0] & (instr_rvalid_i | rdata_pmp_err_q[0]);

  // Hold the request stable for requests that didn't get granted
  assign valid_req_d = valid_req & ~gnt_or_pmp_err;

  // Record whether an outstanding bus request is cancelled by a branch
  assign discard_req_d = valid_req_q & (branch_i | discard_req_q);

  ////////////////
  // Fetch addr //
  ////////////////

  // Two addresses are tracked in the prefetch buffer:
  // 1. stored_addr_q - This is the address issued on the bus. It stays stable until
  //                    the request is granted.
  // 2. fetch_addr_q  - This is our next address to fetch from. It is updated on branches to
  //                    capture the new address, and then for each new request issued.
  // A third address is tracked in the fetch FIFO itself:
  // 3. instr_addr_q  - This is the address at the head of the FIFO, efectively our oldest fetched
  //                    address. This address is updated on branches, and does its own increment
  //                    each time the FIFO is popped.

  // 1. stored_addr_q

  // Only update stored_addr_q for new ungranted requests
  assign stored_addr_en = valid_new_req & ~valid_req_q & ~gnt_or_pmp_err;

  // Store whatever address was issued on the bus
  assign stored_addr_d = instr_addr;

  // CPU resets with a branch, so no need to reset these addresses
  always_ff @(posedge clk_i) begin
    if (stored_addr_en) begin
      stored_addr_q <= stored_addr_d;
    end
  end

  // 2. fetch_addr_q

  // Update on a branch or as soon as a request is issued
  assign fetch_addr_en = branch_i | (valid_new_req & ~valid_req_q);

  assign fetch_addr_d = (branch_i ? addr_i : 
                                    {fetch_addr_q[31:2], 2'b00}) +
                        // Current address + 4
                        {{29{1'b0}},(valid_new_req & ~valid_req_q),2'b00};

  always_ff @(posedge clk_i) begin
    if (fetch_addr_en) begin
      fetch_addr_q <= fetch_addr_d;
    end
  end

  // Address mux
  assign instr_addr = valid_req_q ? stored_addr_q :
                      branch_i    ? addr_i :
                                    fetch_addr_q;

  assign instr_addr_w_aligned = {instr_addr[31:2], 2'b00};

  ///////////////////////////////
  // Request outstanding queue //
  ///////////////////////////////

  for (genvar i = 0; i < NUM_REQS; i++) begin : g_outstanding_reqs
    // Request 0 (always the oldest outstanding request)
    if (i == 0) begin : g_req0
      // A request becomes outstanding once granted, and is cleared once the rvalid is received.
      // Outstanding requests shift down the queue towards entry 0.
      assign rdata_outstanding_n[i] = (valid_req & gnt_or_pmp_err) |
                                      rdata_outstanding_q[i];
      // If a branch is received at any point while a request is outstanding, it must be tracked
      // to ensure we discard the data once received
      assign branch_discard_n[i]    = (valid_req & gnt_or_pmp_err & discard_req_d) |
                                      (branch_i & rdata_outstanding_q[i]) | branch_discard_q[i];
      // Record whether this request received a PMP error
      assign rdata_pmp_err_n[i]     = (valid_req & ~rdata_outstanding_q[i] & instr_pmp_err_i) |
                                      rdata_pmp_err_q[i];

    end else begin : g_reqtop
    // Entries > 0 consider the FIFO fill state to calculate their next state (by checking
    // whether the previous entry is valid)

      assign rdata_outstanding_n[i] = (valid_req & gnt_or_pmp_err &
                                       rdata_outstanding_q[i-1]) |
                                      rdata_outstanding_q[i];
      assign branch_discard_n[i]    = (valid_req & gnt_or_pmp_err & discard_req_d &
                                       rdata_outstanding_q[i-1]) |
                                      (branch_i & rdata_outstanding_q[i]) | branch_discard_q[i];
      assign rdata_pmp_err_n[i]     = (valid_req & ~rdata_outstanding_q[i] & instr_pmp_err_i &
                                       rdata_outstanding_q[i-1]) |
                                      rdata_pmp_err_q[i];
    end
  end

  // Shift the entries down on each instr_rvalid_i
  assign rdata_outstanding_s = rvalid_or_pmp_err ? {1'b0,rdata_outstanding_n[NUM_REQS-1:1]} :
                                                   rdata_outstanding_n;
  assign branch_discard_s    = rvalid_or_pmp_err ? {1'b0,branch_discard_n[NUM_REQS-1:1]} :
                                                   branch_discard_n;
  assign rdata_pmp_err_s     = rvalid_or_pmp_err ? {1'b0,rdata_pmp_err_n[NUM_REQS-1:1]} :
                                                   rdata_pmp_err_n;

  // Push a new entry to the FIFO once complete (and not cancelled by a branch)
  assign fifo_valid = rvalid_or_pmp_err & ~branch_discard_q[0];

  ///////////////
  // Registers //
  ///////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid_req_q          <= 1'b0;
      discard_req_q        <= 1'b0;
      rdata_outstanding_q  <= 'b0;
      branch_discard_q     <= 'b0;
      rdata_pmp_err_q      <= 'b0;
    end else begin
      valid_req_q          <= valid_req_d;
      discard_req_q        <= discard_req_d;
      rdata_outstanding_q  <= rdata_outstanding_s;
      branch_discard_q     <= branch_discard_s;
      rdata_pmp_err_q      <= rdata_pmp_err_s;
    end
  end

  /////////////
  // Outputs //
  /////////////

  assign instr_req_o  = valid_req;
  assign instr_addr_o = instr_addr_w_aligned;

endmodule
