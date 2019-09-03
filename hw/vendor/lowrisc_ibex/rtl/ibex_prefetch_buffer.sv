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

  typedef enum logic [1:0] {
    IDLE, WAIT_GNT, WAIT_RVALID, WAIT_ABORTED
  } pf_fsm_e;

  pf_fsm_e pf_fsm_cs, pf_fsm_ns;

  logic [31:0] instr_addr_q, fetch_addr;
  logic [31:0] instr_addr, instr_addr_w_aligned;
  logic        addr_valid;
  logic        pmp_err_q;
  logic        instr_or_pmp_err;

  logic        fifo_valid;
  logic        fifo_ready;
  logic        fifo_clear;

  ////////////////////////////
  // Prefetch buffer status //
  ////////////////////////////

  assign busy_o = (pf_fsm_cs != IDLE) | instr_req_o;

  //////////////////////////////////////////////
  // Fetch fifo - consumes addresses and data //
  //////////////////////////////////////////////

  // Instruction fetch errors are valid on the data phase of a request
  // PMP errors are generated in the address phase, and registered into a fake data phase
  assign instr_or_pmp_err = instr_err_i | pmp_err_q;

  ibex_fetch_fifo fifo_i (
      .clk_i                 ( clk_i             ),
      .rst_ni                ( rst_ni            ),

      .clear_i               ( fifo_clear        ),

      .in_addr_i             ( instr_addr_q      ),
      .in_rdata_i            ( instr_rdata_i     ),
      .in_err_i              ( instr_or_pmp_err  ),
      .in_valid_i            ( fifo_valid        ),
      .in_ready_o            ( fifo_ready        ),


      .out_valid_o           ( valid_o           ),
      .out_ready_i           ( ready_i           ),
      .out_rdata_o           ( rdata_o           ),
      .out_addr_o            ( addr_o            ),
      .out_err_o             ( err_o             ),

      .out_valid_stored_o    (                   )
  );


  ////////////////
  // Fetch addr //
  ////////////////

  assign fetch_addr = {instr_addr_q[31:2], 2'b00} + 32'd4;
  assign fifo_clear = branch_i;

  //////////////////////////////////////////////////////////////////////////////
  // Instruction fetch FSM -deals with instruction memory / instruction cache //
  //////////////////////////////////////////////////////////////////////////////

  always_comb begin
    instr_req_o = 1'b0;
    instr_addr  = fetch_addr;
    fifo_valid  = 1'b0;
    addr_valid  = 1'b0;
    pf_fsm_ns   = pf_fsm_cs;

    unique case(pf_fsm_cs)
      // default state, not waiting for requested data
      IDLE: begin
        instr_addr  = fetch_addr;
        instr_req_o = 1'b0;

        if (branch_i) begin
          instr_addr = addr_i;
        end

        if (req_i && (fifo_ready || branch_i )) begin
          instr_req_o = 1'b1;
          addr_valid  = 1'b1;


          //~> granted request or not
          pf_fsm_ns = instr_gnt_i ? WAIT_RVALID : WAIT_GNT;
        end
      end // case: IDLE

      // we sent a request but did not yet get a grant
      WAIT_GNT: begin
        instr_addr  = instr_addr_q;
        instr_req_o = 1'b1;

        if (branch_i) begin
          instr_addr = addr_i;
          addr_valid = 1'b1;
        end

        //~> granted request or not
        // If the instruction generated a PMP error, we may or may not
        // get granted (the external valid is suppressed by the error)
        // but we proceed to WAIT_RVALID to push the error to the fifo
        pf_fsm_ns = (instr_gnt_i || pmp_err_q) ? WAIT_RVALID : WAIT_GNT;
      end // case: WAIT_GNT

      // we wait for rvalid, after that we are ready to serve a new request
      WAIT_RVALID: begin
        instr_addr = fetch_addr;

        if (branch_i) begin
          instr_addr = addr_i;
        end

        if (req_i && (fifo_ready || branch_i)) begin
          // prepare for next request

          // Fake the rvalid for PMP errors to push the error to the fifo
          if (instr_rvalid_i || pmp_err_q) begin
            instr_req_o = 1'b1;
            fifo_valid  = 1'b1;
            addr_valid  = 1'b1;

            //~> granted request or not
            pf_fsm_ns = instr_gnt_i ? WAIT_RVALID : WAIT_GNT;
          end else begin
            // we are requested to abort our current request
            // we didn't get an rvalid yet, so wait for it
            if (branch_i) begin
              addr_valid = 1'b1;
              pf_fsm_ns  = WAIT_ABORTED;
            end
          end
        end else begin
          // just wait for rvalid and go back to IDLE, no new request

          // Fake the rvalid for PMP errors to push the error to the fifo
          if (instr_rvalid_i || pmp_err_q) begin
            fifo_valid = 1'b1;
            pf_fsm_ns  = IDLE;
          end
        end
      end // case: WAIT_RVALID

      // our last request was aborted, but we didn't yet get a rvalid and
      // there was no new request sent yet
      // we assume that req_i is set to high
      WAIT_ABORTED: begin
        instr_addr = instr_addr_q;

        if (branch_i) begin
          instr_addr = addr_i;
          addr_valid = 1'b1;
        end

        if (instr_rvalid_i) begin
          instr_req_o = 1'b1;
          // no need to send address, already done in WAIT_RVALID

          //~> granted request or not
          pf_fsm_ns = instr_gnt_i ? WAIT_RVALID : WAIT_GNT;
        end
      end

      default: begin
        pf_fsm_ns = pf_fsm_e'(1'bX);
      end
    endcase
  end

  ///////////////
  // Registers //
  ///////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pf_fsm_cs      <= IDLE;
      instr_addr_q   <= '0;
      pmp_err_q      <= '0;
    end else begin
      pf_fsm_cs      <= pf_fsm_ns;

      if (addr_valid) begin
        instr_addr_q <= instr_addr;
        pmp_err_q    <= instr_pmp_err_i;
      end
    end
  end

  /////////////////
  // Output Addr //
  /////////////////
  assign instr_addr_w_aligned = {instr_addr[31:2], 2'b00};
  assign instr_addr_o         =  instr_addr_w_aligned;

endmodule
