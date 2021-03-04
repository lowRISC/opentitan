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
module ibex_prefetch_buffer #(
  parameter bit BranchPredictor = 1'b0
) (
    input  logic        clk_i,
    input  logic        rst_ni,

    input  logic        req_i,

    input  logic        branch_i,
    input  logic        branch_spec_i,
    input  logic        predicted_branch_i,
    input  logic        branch_mispredict_i,
    input  logic [31:0] addr_i,


    input  logic        ready_i,
    output logic        valid_o,
    output logic [31:0] rdata_o,
    output logic [31:0] addr_o,
    output logic        err_o,
    output logic        err_plus2_o,


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

  logic                branch_suppress;
  logic                valid_new_req, valid_req;
  logic                valid_req_d, valid_req_q;
  logic                discard_req_d, discard_req_q;
  logic                gnt_or_pmp_err, rvalid_or_pmp_err;
  logic [NUM_REQS-1:0] rdata_outstanding_n, rdata_outstanding_s, rdata_outstanding_q;
  logic [NUM_REQS-1:0] branch_discard_n, branch_discard_s, branch_discard_q;
  logic [NUM_REQS-1:0] rdata_pmp_err_n, rdata_pmp_err_s, rdata_pmp_err_q;
  logic [NUM_REQS-1:0] rdata_outstanding_rev;

  logic [31:0]         stored_addr_d, stored_addr_q;
  logic                stored_addr_en;
  logic [31:0]         fetch_addr_d, fetch_addr_q;
  logic                fetch_addr_en;
  logic [31:0]         branch_mispredict_addr;
  logic [31:0]         instr_addr, instr_addr_w_aligned;
  logic                instr_or_pmp_err;

  logic                fifo_valid;
  logic [31:0]         fifo_addr;
  logic                fifo_ready;
  logic                fifo_clear;
  logic [NUM_REQS-1:0] fifo_busy;

  logic                valid_raw;

  logic [31:0]         addr_next;

  logic                branch_or_mispredict;

  ////////////////////////////
  // Prefetch buffer status //
  ////////////////////////////

  assign busy_o = (|rdata_outstanding_q) | instr_req_o;

  assign branch_or_mispredict = branch_i | branch_mispredict_i;

  //////////////////////////////////////////////
  // Fetch fifo - consumes addresses and data //
  //////////////////////////////////////////////

  // Instruction fetch errors are valid on the data phase of a request
  // PMP errors are generated in the address phase, and registered into a fake data phase
  assign instr_or_pmp_err = instr_err_i | rdata_pmp_err_q[0];

  // A branch will invalidate any previously fetched instructions.
  // Note that the FENCE.I instruction relies on this flushing behaviour on branch. If it is
  // altered the FENCE.I implementation may require changes.
  assign fifo_clear = branch_or_mispredict;

  // Reversed version of rdata_outstanding_q which can be overlaid with fifo fill state
  for (genvar i = 0; i < NUM_REQS; i++) begin : gen_rd_rev
    assign rdata_outstanding_rev[i] = rdata_outstanding_q[NUM_REQS-1-i];
  end

  // The fifo is ready to accept a new request if it is not full - including space reserved for
  // requests already outstanding.
  // Overlay the fifo fill state with the outstanding requests to see if there is space.
  assign fifo_ready = ~&(fifo_busy | rdata_outstanding_rev);

  ibex_fetch_fifo #(
    .NUM_REQS (NUM_REQS)
  ) fifo_i (
      .clk_i                 ( clk_i             ),
      .rst_ni                ( rst_ni            ),

      .clear_i               ( fifo_clear        ),
      .busy_o                ( fifo_busy         ),

      .in_valid_i            ( fifo_valid        ),
      .in_addr_i             ( fifo_addr         ),
      .in_rdata_i            ( instr_rdata_i     ),
      .in_err_i              ( instr_or_pmp_err  ),

      .out_valid_o           ( valid_raw         ),
      .out_ready_i           ( ready_i           ),
      .out_rdata_o           ( rdata_o           ),
      .out_addr_o            ( addr_o            ),
      .out_addr_next_o       ( addr_next         ),
      .out_err_o             ( err_o             ),
      .out_err_plus2_o       ( err_plus2_o       )
  );

  //////////////
  // Requests //
  //////////////

  // Suppress a new request on a not-taken branch (as the external address will be incorrect)
  assign branch_suppress = branch_spec_i & ~branch_i;

  // Make a new request any time there is space in the FIFO, and space in the request queue
  assign valid_new_req = ~branch_suppress & req_i & (fifo_ready | branch_or_mispredict) &
                         ~rdata_outstanding_q[NUM_REQS-1];

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
  assign discard_req_d = valid_req_q & (branch_or_mispredict | discard_req_q);

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

  if (BranchPredictor) begin : g_branch_predictor
    // Where the branch predictor is present record what address followed a predicted branch.  If
    // that branch is predicted taken but mispredicted (so not-taken) this is used to resume on
    // the not-taken code path.
    logic [31:0] branch_mispredict_addr_q;
    logic        branch_mispredict_addr_en;

    assign branch_mispredict_addr_en = branch_i & predicted_branch_i;

    always_ff @(posedge clk_i) begin
      if (branch_mispredict_addr_en) begin
        branch_mispredict_addr_q <= addr_next;
      end
    end

    assign branch_mispredict_addr = branch_mispredict_addr_q;
  end else begin : g_no_branch_predictor
    logic        unused_predicted_branch;
    logic [31:0] unused_addr_next;

    assign unused_predicted_branch = predicted_branch_i;
    assign unused_addr_next        = addr_next;

    assign branch_mispredict_addr = '0;
  end

  // 2. fetch_addr_q

  // Update on a branch or as soon as a request is issued
  assign fetch_addr_en = branch_or_mispredict | (valid_new_req & ~valid_req_q);

  assign fetch_addr_d = (branch_i            ? addr_i :
                         branch_mispredict_i ? {branch_mispredict_addr[31:2], 2'b00} :
                                               {fetch_addr_q[31:2], 2'b00}) +
                        // Current address + 4
                        {{29{1'b0}},(valid_new_req & ~valid_req_q),2'b00};

  always_ff @(posedge clk_i) begin
    if (fetch_addr_en) begin
      fetch_addr_q <= fetch_addr_d;
    end
  end

  // Address mux
  assign instr_addr = valid_req_q         ? stored_addr_q :
                      branch_spec_i       ? addr_i :
                      branch_mispredict_i ? branch_mispredict_addr :
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
                                      (branch_or_mispredict & rdata_outstanding_q[i]) |
                                      branch_discard_q[i];
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
                                      (branch_or_mispredict & rdata_outstanding_q[i]) |
                                      branch_discard_q[i];
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

  assign fifo_addr = branch_i ? addr_i : branch_mispredict_addr;

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

  assign valid_o = valid_raw & ~branch_mispredict_i;

endmodule
