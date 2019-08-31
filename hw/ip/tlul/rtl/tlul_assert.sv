// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Protocol checker for TL-UL ports using assertions

module tlul_assert (
  input clk_i,
  input rst_ni,

  // tile link ports
  input tlul_pkg::tl_h2d_t h2d,
  input tlul_pkg::tl_d2h_t d2h
);

  import tlul_pkg::*;
  import top_pkg::*;

  //------------------------------------------------------------------------------------
  // check requests and responses
  //------------------------------------------------------------------------------------

  // There are up to 2**TL_AIW possible source-IDs. Below array "pend_req" has one entry
  // for each source-ID. Each entry has the following fields:
  //  - pend   : is set to 1 to indicate up to 1 pending request for the source ID
  //  - opcode : "Get" requires "AccessAckData" response, "Put*" require "AccessAck"
  //  - size   : d_size of response must match a_size of request
  //  - mask   : is used to allow X for bytes whose mask bit is 0
  typedef struct packed {
    bit                         pend; // set to 1 to indicate a pending request
    tl_a_op_e                   opcode;
    logic [top_pkg::TL_SZW-1:0] size;
    logic [top_pkg::TL_DBW-1:0] mask;
  } pend_req_t;

  pend_req_t [2**TL_AIW-1:0] pend_req;

  bit saw_one, not_contig;

  // use negedge clk to avoid possible race conditions
  always_ff @(negedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      for (int ii = 0; ii < 2**TL_AIW; ii++) begin
        pend_req[ii].pend = 0;
      end
    end else begin

      //--------------------------------------------------------------------------------
      // check requests
      //--------------------------------------------------------------------------------
      if (h2d.a_valid) begin

        // a_opcode: only 3 opcodes are legal for requests
        `ASSERT_I(legalAOpcode, (h2d.a_opcode === PutFullData) || (h2d.a_opcode === Get)
            || (h2d.a_opcode === PutPartialData))

        // a_param is reserved
        `ASSERT_I(legalAParam, h2d.a_param === '0)

        // a_size: 2**a_size must equal $countones(a_mask)
        `ASSERT_I(sizeMatchesMask, (1 << h2d.a_size) === $countones(h2d.a_mask))

        // a_source: there should be no more than one pending request per each source ID
        `ASSERT_I(onlyOnePendingReqPerSourceID, pend_req[h2d.a_source].pend == 0)

        // a_address must be aligned to a_size: a_address & ((1 << a_size) - 1) == 0
        `ASSERT_I(addressAlignedToSize, (h2d.a_address & ((1 << h2d.a_size)-1)) == '0)

        // a_mask must be contiguous for Get and PutFullData requests
        // TODO: the spec talks about "naturally aligned". Does this mean that bit [0] of
        // mask is always 1? If that's true, then below code could be much simpler.
        // However, the spec shows a timing diagram where bit 0 of mask is 0.
        if (h2d.a_opcode != PutPartialData) begin
          // Below loop traverses mask[TL_DBW-1:0] from bit [1] to [TL_DBW-1].
          // It sets bit "not_contig" whenever it sees pattern "10" and it has seen a
          // "1" in the previous bits. So e.g. patterns like 10..1.. will be flagged.
          saw_one = h2d.a_mask[0];
          not_contig = 0; // below loop sets not_contig once it detects non-contiguous
          for (int ii = 1; ii < TL_DBW; ii++) begin
            if (saw_one && h2d.a_mask[ii] && (!h2d.a_mask[ii-1])) not_contig = 1;
            if (h2d.a_mask[ii]) saw_one = 1;
          end
          `ASSERT_I(maskMustBeContiguous, !not_contig)
        end

        // a_data must be known for opcode == Put*(depending on mask bits)
        for (int ii = 0; ii < TL_DBW; ii++) begin
          if (h2d.a_mask[ii] && (h2d.a_opcode != Get)) begin
            `ASSERT_I(aDataKnown, !$isunknown(h2d.a_data[8*ii +: 8]))
          end
        end

        // store each request in pend_req array (we use blocking statements below so
        // that we can handle the case where request and response for the same
        // source-ID happen in the same cycle)
        if (d2h.a_ready) begin
          pend_req[h2d.a_source].pend   = 1;
          pend_req[h2d.a_source].opcode = h2d.a_opcode;
          pend_req[h2d.a_source].size   = h2d.a_size;
          pend_req[h2d.a_source].mask   = h2d.a_mask;
        end
      end

      //--------------------------------------------------------------------------------
      // check responses
      //--------------------------------------------------------------------------------
      if (d2h.d_valid) begin

        // d_opcode: if request was Get, then response must be AccessAckData
        `ASSERT_I(checkResponseOpcode, d2h.d_opcode ===
            ((pend_req[d2h.d_source].opcode == Get) ? AccessAckData : AccessAck))

        // d_param is reserved
        `ASSERT_I(legalDParam, d2h.d_param === '0)

        // d_size must equal the a_size of the corresponding request
        `ASSERT_I(responseSizeMustEqualReqSize, d2h.d_size === pend_req[d2h.d_source].size)

        // d_source: each response should have a pending request using same source ID
        `ASSERT_I(responseMustHaveReq, pend_req[d2h.d_source].pend)

        // d_data must be known for AccessAckData (depending on mask bits)
        for (int ii = 0; ii < TL_DBW; ii++) begin
          if (pend_req[d2h.d_source].mask[ii] && (d2h.d_opcode == AccessAckData)) begin
            `ASSERT_I(dDataKnown, !$isunknown(d2h.d_data[8*ii +: 8]))
          end
        end

        // update pend_req array
        if (h2d.d_ready) begin
          pend_req[d2h.d_source].pend = 0;
        end
      end
    end
  end

  // make sure all "pending" bits are 0 at the end of the sim
  for (genvar ii = 0; ii < 2**TL_AIW; ii++) begin : gen_assert_final
    `ASSERT_FINAL(noOutstandingReqsAtEndOfSim, (pend_req[ii].pend == 0))
  end

  //------------------------------------------------------------------------------------
  // additional checks for X values
  //------------------------------------------------------------------------------------

  // a_* should be known when a_valid == 1 (a_opcode and a_param are already covered above)
  `ASSERT_VALID_DATA(aKnown, h2d.a_valid, {h2d.a_size, h2d.a_source, h2d.a_address,
      h2d.a_mask, h2d.a_user}, clk_i, !rst_ni)

  // d_* should be known when d_valid == 1 (d_opcode, d_param, d_size already covered above)
  `ASSERT_VALID_DATA(dKnown, d2h.d_valid, {d2h.d_source, d2h.d_sink, d2h.d_error, d2h.d_user},
      clk_i, !rst_ni)

  //  make sure ready is not X after reset
  `ASSERT_KNOWN(aReadyKnown, d2h.a_ready, clk_i, !rst_ni)
  `ASSERT_KNOWN(dReadyKnown, h2d.d_ready, clk_i, !rst_ni)

endmodule
