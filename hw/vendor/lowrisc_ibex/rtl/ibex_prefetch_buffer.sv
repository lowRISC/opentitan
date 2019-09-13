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

  // Changes to the address flops would be required for > 2 outstanding requests
  localparam int unsigned NUM_REQS = 2;

  logic                valid_req;
  logic                valid_req_d, valid_req_q;
  logic                hold_addr_d, hold_addr_q;
  logic                gnt_or_pmp_err, rvalid_or_pmp_err;
  logic [NUM_REQS-1:0] rdata_outstanding_n, rdata_outstanding_s, rdata_outstanding_q;
  logic [NUM_REQS-1:0] branch_abort_n, branch_abort_s, branch_abort_q;

  logic [31:0]         instr_addr_q, fetch_addr;
  logic [31:0]         instr_addr, instr_addr_w_aligned;
  logic                addr_valid;
  logic                pmp_err_q;
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
  assign instr_or_pmp_err = instr_err_i | pmp_err_q;

  // A branch will invalidate any previously fetched instructions
  assign fifo_clear = branch_i;

  ibex_fetch_fifo fifo_i (
      .clk_i                 ( clk_i             ),
      .rst_ni                ( rst_ni            ),

      .clear_i               ( fifo_clear        ),

      .in_valid_i            ( fifo_valid        ),
      .in_addr_i             ( instr_addr_q      ),
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
  assign valid_req = valid_req_q | (req_i & (fifo_ready | branch_i) & (~&rdata_outstanding_q));

  // If a request address triggers a PMP error, the external bus request is suppressed. We might
  // therefore never receive a grant for such a request. The grant is faked in this case to make
  // sure the request proceeds and the error is pushed to the FIFO.
  // We always use the registered version of the signal since it will be held stable throughout
  // the request, and the penalty of waiting for an extra cycle to consume the error is irrelevant.
  // A branch could update the address (and therefore data_pmp_err_i) on the cycle a request is
  // issued, in which case we must ignore the registered version.
  assign gnt_or_pmp_err = instr_gnt_i | (pmp_err_q & ~branch_i);

  // As with the grant, the rvalid must be faked for a PMP error, since the request was suppressed.
  // Since the pmp_err_q flop is only updated when the address updates, it will always point to the
  // PMP error status of the oldest outstanding request
  assign rvalid_or_pmp_err = rdata_outstanding_q[0] & (instr_rvalid_i | pmp_err_q);

  // Hold the request stable for requests that didn't get granted
  assign valid_req_d = valid_req & ~instr_gnt_i;

  // Hold the address stable for requests that couldn't be issued, or didn't get granted.
  // This is different to valid_req_q since there are cases where we must use addr+4 for
  // an ungranted request rather than addr_q (where addr_q has not been updated).
  assign hold_addr_d = (branch_i | hold_addr_q) & ~(valid_req & instr_gnt_i);

  ////////////////
  // Fetch addr //
  ////////////////

  // The address flop is used to hold the address steady for ungranted requests and also to
  // push the address to the FIFO for completed requests. For this reason, the address is only
  // updated once a request is the oldest outstanding to ensure that newer requests do not
  // overwrite the addresses of older ones. Branches are an exception to this, since all older
  // addresses will be discarded due to the branch.

  // Update the addr_q flop on any branch, or
  assign addr_valid = branch_i |
                      // A new request which will be the oldest, or
                      (valid_req & instr_gnt_i & ~rdata_outstanding_q[0]) |
                      // each time a valid request becomes the oldest
                      (rvalid_or_pmp_err & ~branch_abort_q[0] &
                       ((valid_req & instr_gnt_i) | rdata_outstanding_q[1]));

  // Fetch the next word-aligned instruction address
  assign fetch_addr = {instr_addr_q[31:2], 2'b00} + 32'd4;

  // Address mux
  assign instr_addr = branch_i    ? addr_i :
                      hold_addr_q ? instr_addr_q :
                                    fetch_addr;

  assign instr_addr_w_aligned = {instr_addr[31:2], 2'b00};

  ///////////////////////////////
  // Request outstanding queue //
  ///////////////////////////////

  for (genvar i = 0; i < NUM_REQS; i++) begin : g_outstanding_reqs
    // Request 0 (always the oldest outstanding request)
    if (i == 0) begin : g_req0
      // A request becomes outstanding once granted, and is cleared once the rvalid is received.
      // Outstanding requests shift down the queue towards entry 0. Entry 0 considers the PMP
      // error cases while newer entries do not (pmp_err_q is only valid for entry 0)
      assign rdata_outstanding_n[i] = (valid_req & gnt_or_pmp_err) |
                                      rdata_outstanding_q[i];
      // If a branch is received at any point while a request is outstanding, it must be tracked
      // to ensure we discard the data once received
      assign branch_abort_n[i]      = (branch_i & rdata_outstanding_q[i]) | branch_abort_q[i];

    end else begin : g_reqtop

      assign rdata_outstanding_n[i] = (valid_req & instr_gnt_i &
                                       (&rdata_outstanding_q[i-1:0])) |
                                      rdata_outstanding_q[i];
      assign branch_abort_n[i]      = (branch_i & rdata_outstanding_q[i]) | branch_abort_q[i];
    end
  end

  // Shift the entries down on each instr_rvalid_i
  assign rdata_outstanding_s = rvalid_or_pmp_err ? {1'b0,rdata_outstanding_n[NUM_REQS-1:1]} :
                                                   rdata_outstanding_n;
  assign branch_abort_s      = rvalid_or_pmp_err ? {1'b0,branch_abort_n[NUM_REQS-1:1]} :
                                                   branch_abort_n;

  // Push a new entry to the FIFO once complete (and not aborted by a branch)
  assign fifo_valid = rvalid_or_pmp_err & ~branch_abort_q[0];

  ///////////////
  // Registers //
  ///////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid_req_q          <= 1'b0;
      hold_addr_q          <= 1'b0;
      rdata_outstanding_q  <= 'b0;
      branch_abort_q       <= 'b0;
    end else begin
      valid_req_q          <= valid_req_d;
      hold_addr_q          <= hold_addr_d;
      rdata_outstanding_q  <= rdata_outstanding_s;
      branch_abort_q       <= branch_abort_s;
    end
  end

  // CPU resets with a branch, so no need to reset these
  always_ff @(posedge clk_i) begin
    if (addr_valid) begin
      instr_addr_q <= instr_addr;
      pmp_err_q    <= instr_pmp_err_i;
    end
  end

  /////////////
  // Outputs //
  /////////////

  assign instr_req_o          = valid_req;
  assign instr_addr_o         = instr_addr_w_aligned;

  ////////////////
  // Assertions //
  ////////////////

`ifndef VERILATOR
  // Code changes required to support > 2 outstanding requests
  assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    (NUM_REQS <= 2) );
`endif

endmodule
