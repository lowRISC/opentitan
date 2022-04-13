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
  parameter bit ResetAll        = 1'b0
) (
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
  output logic        err_plus2_o,

  // goes to instruction memory / instruction cache
  output logic        instr_req_o,
  input  logic        instr_gnt_i,
  output logic [31:0] instr_addr_o,
  input  logic [31:0] instr_rdata_i,
  input  logic        instr_err_i,
  input  logic        instr_rvalid_i,

  // Prefetch Buffer Status
  output logic        busy_o
);

  localparam int unsigned NUM_REQS  = 2;

  logic                valid_new_req, valid_req;
  logic                valid_req_d, valid_req_q;
  logic                discard_req_d, discard_req_q;
  logic [NUM_REQS-1:0] rdata_outstanding_n, rdata_outstanding_s, rdata_outstanding_q;
  logic [NUM_REQS-1:0] branch_discard_n, branch_discard_s, branch_discard_q;
  logic [NUM_REQS-1:0] rdata_outstanding_rev;

  logic [31:0]         stored_addr_d, stored_addr_q;
  logic                stored_addr_en;
  logic [31:0]         fetch_addr_d, fetch_addr_q;
  logic                fetch_addr_en;
  logic [31:0]         instr_addr, instr_addr_w_aligned;

  logic                fifo_valid;
  logic [31:0]         fifo_addr;
  logic                fifo_ready;
  logic                fifo_clear;
  logic [NUM_REQS-1:0] fifo_busy;

  ////////////////////////////
  // Prefetch buffer status //
  ////////////////////////////

  assign busy_o = (|rdata_outstanding_q) | instr_req_o;

  //////////////////////////////////////////////
  // Fetch fifo - consumes addresses and data //
  //////////////////////////////////////////////

  // A branch will invalidate any previously fetched instructions.
  // Note that the FENCE.I instruction relies on this flushing behaviour on branch. If it is
  // altered the FENCE.I implementation may require changes.
  assign fifo_clear = branch_i;

  // Reversed version of rdata_outstanding_q which can be overlaid with fifo fill state
  for (genvar i = 0; i < NUM_REQS; i++) begin : gen_rd_rev
    assign rdata_outstanding_rev[i] = rdata_outstanding_q[NUM_REQS-1-i];
  end

  // The fifo is ready to accept a new request if it is not full - including space reserved for
  // requests already outstanding.
  // Overlay the fifo fill state with the outstanding requests to see if there is space.
  assign fifo_ready = ~&(fifo_busy | rdata_outstanding_rev);

  ibex_fetch_fifo #(
    .NUM_REQS (NUM_REQS),
    .ResetAll (ResetAll)
  ) fifo_i (
      .clk_i                 ( clk_i             ),
      .rst_ni                ( rst_ni            ),

      .clear_i               ( fifo_clear        ),
      .busy_o                ( fifo_busy         ),

      .in_valid_i            ( fifo_valid        ),
      .in_addr_i             ( fifo_addr         ),
      .in_rdata_i            ( instr_rdata_i     ),
      .in_err_i              ( instr_err_i       ),

      .out_valid_o           ( valid_o           ),
      .out_ready_i           ( ready_i           ),
      .out_rdata_o           ( rdata_o           ),
      .out_addr_o            ( addr_o            ),
      .out_err_o             ( err_o             ),
      .out_err_plus2_o       ( err_plus2_o       )
  );

  //////////////
  // Requests //
  //////////////

  // Make a new request any time there is space in the FIFO, and space in the request queue
  assign valid_new_req = req_i & (fifo_ready | branch_i) &
                         ~rdata_outstanding_q[NUM_REQS-1];

  assign valid_req = valid_req_q | valid_new_req;

  // Hold the request stable for requests that didn't get granted
  assign valid_req_d = valid_req & ~instr_gnt_i;

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
  assign stored_addr_en = valid_new_req & ~valid_req_q & ~instr_gnt_i;

  // Store whatever address was issued on the bus
  assign stored_addr_d = instr_addr;

  // CPU resets with a branch, so no need to reset these addresses
  if (ResetAll) begin : g_stored_addr_ra
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        stored_addr_q <= '0;
      end else if (stored_addr_en) begin
        stored_addr_q <= stored_addr_d;
      end
    end
  end else begin : g_stored_addr_nr
    always_ff @(posedge clk_i) begin
      if (stored_addr_en) begin
        stored_addr_q <= stored_addr_d;
      end
    end
  end
  // 2. fetch_addr_q

  // Update on a branch or as soon as a request is issued
  assign fetch_addr_en = branch_i | (valid_new_req & ~valid_req_q);

  assign fetch_addr_d = (branch_i ? addr_i : {fetch_addr_q[31:2], 2'b00}) +
                        // Current address + 4
                        {{29{1'b0}},(valid_new_req & ~valid_req_q),2'b00};

  if (ResetAll) begin : g_fetch_addr_ra
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        fetch_addr_q <= '0;
      end else if (fetch_addr_en) begin
        fetch_addr_q <= fetch_addr_d;
      end
    end
  end else begin : g_fetch_addr_nr
    always_ff @(posedge clk_i) begin
      if (fetch_addr_en) begin
        fetch_addr_q <= fetch_addr_d;
      end
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
      assign rdata_outstanding_n[i] = (valid_req & instr_gnt_i) |
                                      rdata_outstanding_q[i];
      // If a branch is received at any point while a request is outstanding, it must be tracked
      // to ensure we discard the data once received
      assign branch_discard_n[i]    = (valid_req & instr_gnt_i & discard_req_d) |
                                      (branch_i & rdata_outstanding_q[i]) |
                                      branch_discard_q[i];

    end else begin : g_reqtop
    // Entries > 0 consider the FIFO fill state to calculate their next state (by checking
    // whether the previous entry is valid)

      assign rdata_outstanding_n[i] = (valid_req & instr_gnt_i &
                                       rdata_outstanding_q[i-1]) |
                                      rdata_outstanding_q[i];
      assign branch_discard_n[i]    = (valid_req & instr_gnt_i & discard_req_d &
                                       rdata_outstanding_q[i-1]) |
                                      (branch_i & rdata_outstanding_q[i]) |
                                      branch_discard_q[i];
    end
  end

  // Shift the entries down on each instr_rvalid_i
  assign rdata_outstanding_s = instr_rvalid_i ? {1'b0,rdata_outstanding_n[NUM_REQS-1:1]} :
                                                rdata_outstanding_n;
  assign branch_discard_s    = instr_rvalid_i ? {1'b0,branch_discard_n[NUM_REQS-1:1]} :
                                                branch_discard_n;

  // Push a new entry to the FIFO once complete (and not cancelled by a branch)
  assign fifo_valid = instr_rvalid_i & ~branch_discard_q[0];

  assign fifo_addr = addr_i;

  ///////////////
  // Registers //
  ///////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      valid_req_q          <= 1'b0;
      discard_req_q        <= 1'b0;
      rdata_outstanding_q  <= 'b0;
      branch_discard_q     <= 'b0;
    end else begin
      valid_req_q          <= valid_req_d;
      discard_req_q        <= discard_req_d;
      rdata_outstanding_q  <= rdata_outstanding_s;
      branch_discard_q     <= branch_discard_s;
    end
  end

  /////////////
  // Outputs //
  /////////////

  assign instr_req_o  = valid_req;
  assign instr_addr_o = instr_addr_w_aligned;

endmodule
