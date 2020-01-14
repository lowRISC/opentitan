// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Protocol checker for TL-UL ports using assertions. Supports interface-widths
// up to 64bit.

`include "prim_assert.sv"

module tlul_assert #(
  parameter EndpointType = "Device" // can be either "Host" or "Device"
) (
  input clk_i,
  input rst_ni,

  // tile link ports
  input tlul_pkg::tl_h2d_t h2d,
  input tlul_pkg::tl_d2h_t d2h
);

`ifndef VERILATOR
`ifndef SYNTHESIS

  import tlul_pkg::*;
  import top_pkg::*;

  //////////////////////////////////
  // check requests and responses //
  //////////////////////////////////

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

  // this interfaces allows the testbench to disable some assertions
  // by driving the corresponding pin to 1'b0
  wire tlul_assert_ctrl, disable_sva;
  pins_if #(1) tlul_assert_ctrl_if(tlul_assert_ctrl);
  // the interface may be uninitialized, in which case the assertions
  // shall be enabled, hence the explicit check for 1'b0
  assign disable_sva = (tlul_assert_ctrl === 1'b0);

  logic [7:0]  a_mask, d_mask;
  logic [63:0] a_data, d_data;
  assign a_mask = 8'(h2d.a_mask);
  assign a_data = 64'(h2d.a_data);
  assign d_mask = 8'(pend_req[d2h.d_source].mask);
  assign d_data = 64'(d2h.d_data);

  ////////////////////////////////////
  // keep track of pending requests //
  ////////////////////////////////////

  // use negedge clk to avoid possible race conditions
  always_ff @(negedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pend_req <= '0;
    end else begin
      if (h2d.a_valid) begin
        // store each request in pend_req array (we use blocking statements below so
        // that we can handle the case where request and response for the same
        // source-ID happen in the same cycle)
        if (d2h.a_ready) begin
          pend_req[h2d.a_source].pend    <= 1;
          pend_req[h2d.a_source].opcode  <= h2d.a_opcode;
          pend_req[h2d.a_source].size    <= h2d.a_size;
          pend_req[h2d.a_source].mask    <= h2d.a_mask;
        end
      end // h2d.a_valid

      if (d2h.d_valid) begin
        // update pend_req array
        if (h2d.d_ready) begin
          pend_req[d2h.d_source].pend <= 0;
        end
      end //d2h.d_valid
    end
  end

  /////////////////////////////////////////
  // define sequences for request checks //
  /////////////////////////////////////////

  sequence h2d_pre_S;
    h2d.a_valid;
  endsequence

  // a_opcode: only 3 opcodes are legal for requests
  sequence legalAOpcode_S;
    (h2d.a_opcode === PutFullData) ||
    (h2d.a_opcode === Get) ||
    (h2d.a_opcode === PutPartialData);
  endsequence

  // a_param is reserved
  sequence legalAParam_S;
    h2d.a_param === '0;
  endsequence

  // a_size: Size shouldn't be greater than the bus width in TL-UL (not in TL-UH)
  //         This assertion can be covered by below
  //         (a_size must less than or equal to ones of a_mask)

  // a_size: 2**a_size must greater than or equal to $countones(a_mask) for PutPartial and Get
  sequence sizeGTEMask_S;
    (h2d.a_opcode == PutFullData) || ((1 << h2d.a_size) >= $countones(h2d.a_mask));
  endsequence

  // a_size: 2**a_size must equal to $countones(a_mask) for PutFull
  sequence sizeMatchesMask_S;
    (h2d.a_opcode inside {PutPartialData, Get}) ||
    ((1 << h2d.a_size) === $countones(h2d.a_mask));
  endsequence

  // a_source: there should be no more than one pending request per each source ID
  sequence pendingReqPerSrc_S;
    pend_req[h2d.a_source].pend == 0;
  endsequence

  // a_address must be aligned to a_size: a_address & ((1 << a_size) - 1) == 0
  sequence addrSizeAligned_S;
    (h2d.a_address & ((1 << h2d.a_size)-1)) == '0;
  endsequence

  // a_mask must be contiguous for Get and PutFullData requests
  //    the spec talks about "naturally aligned". Does this mean that bit [0] of
  //    mask is always 1? If that's true, then below code could be much simpler.
  //    However, the spec shows a timing diagram where bit 0 of mask is 0.
  sequence contigMask_pre_S;
    h2d.a_opcode != PutPartialData;
  endsequence

  sequence contigMask_S;
    $countones(h2d.a_mask ^ {h2d.a_mask[$bits(h2d.a_mask)-2:0], 1'b0}) <= 2;
  endsequence

  // a_data must be known for opcode == Put*(depending on mask bits)
  sequence aDataKnown_pre_S;
    (h2d.a_opcode != Get);
  endsequence

  sequence aDataKnown_S;
    // no check if this lane mask is inactive
    ((!a_mask[0]) || (a_mask[0] && !$isunknown(a_data[8*0 +: 8]))) &&
    ((!a_mask[1]) || (a_mask[1] && !$isunknown(a_data[8*1 +: 8]))) &&
    ((!a_mask[2]) || (a_mask[2] && !$isunknown(a_data[8*2 +: 8]))) &&
    ((!a_mask[3]) || (a_mask[3] && !$isunknown(a_data[8*3 +: 8]))) &&
    ((!a_mask[4]) || (a_mask[4] && !$isunknown(a_data[8*4 +: 8]))) &&
    ((!a_mask[5]) || (a_mask[5] && !$isunknown(a_data[8*5 +: 8]))) &&
    ((!a_mask[6]) || (a_mask[6] && !$isunknown(a_data[8*6 +: 8]))) &&
    ((!a_mask[7]) || (a_mask[7] && !$isunknown(a_data[8*7 +: 8])));
  endsequence

  /////////////////////////////////////////
  // define sequences for request checks //
  /////////////////////////////////////////

  sequence d2h_pre_S;
    d2h.d_valid;
  endsequence

  // d_opcode: if request was Get, then response must be AccessAckData
  sequence respOpcode_S;
    d2h.d_opcode === ((pend_req[d2h.d_source].opcode == Get) ? AccessAckData : AccessAck);
  endsequence

  // d_param is reserved
  sequence legalDParam_S;
    d2h.d_param === '0;
  endsequence

  // d_size must equal the a_size of the corresponding request
  sequence respSzEqReqSz_S;
    d2h.d_size === pend_req[d2h.d_source].size;
  endsequence

  // d_source: each response should have a pending request using same source ID
  sequence respMustHaveReq_S;
    pend_req[d2h.d_source].pend;
  endsequence

// d_data must be known for AccessAckData (depending on mask bits)
  sequence dDataKnown_pre_S;
    d2h.d_opcode == AccessAckData;
  endsequence

  sequence dDataKnown_S;
    // no check if this lane mask is inactive
    ((!d_mask[0]) || (d_mask[0] && !$isunknown(d_data[8*0 +: 8]))) &&
    ((!d_mask[1]) || (d_mask[1] && !$isunknown(d_data[8*1 +: 8]))) &&
    ((!d_mask[2]) || (d_mask[2] && !$isunknown(d_data[8*2 +: 8]))) &&
    ((!d_mask[3]) || (d_mask[3] && !$isunknown(d_data[8*3 +: 8]))) &&
    ((!d_mask[4]) || (d_mask[4] && !$isunknown(d_data[8*4 +: 8]))) &&
    ((!d_mask[5]) || (d_mask[5] && !$isunknown(d_data[8*5 +: 8]))) &&
    ((!d_mask[6]) || (d_mask[6] && !$isunknown(d_data[8*6 +: 8]))) &&
    ((!d_mask[7]) || (d_mask[7] && !$isunknown(d_data[8*7 +: 8])));
  endsequence

  ///////////////////////////////////
  // assemble properties and check //
  ///////////////////////////////////

  // note: use negedge clk to avoid possible race conditions
  // in this case all signals coming from the device side have an assumed property
  if (EndpointType == "Host") begin : gen_host
    // h2d
    `ASSERT(legalAOpcode_A,     h2d_pre_S |-> legalAOpcode_S,     !clk_i, !rst_ni || disable_sva)
    `ASSERT(legalAParam_A,      h2d_pre_S |-> legalAParam_S,      !clk_i, !rst_ni)
    `ASSERT(sizeGTEMask_A,      h2d_pre_S |-> sizeGTEMask_S,      !clk_i, !rst_ni || disable_sva)
    `ASSERT(sizeMatchesMask_A,  h2d_pre_S |-> sizeMatchesMask_S,  !clk_i, !rst_ni || disable_sva)
    `ASSERT(pendingReqPerSrc_A, h2d_pre_S |-> pendingReqPerSrc_S, !clk_i, !rst_ni)
    `ASSERT(addrSizeAligned_A,  h2d_pre_S |-> addrSizeAligned_S,  !clk_i, !rst_ni || disable_sva)
    `ASSERT(contigMask_A,       h2d_pre_S and contigMask_pre_S |-> contigMask_S,
          !clk_i, !rst_ni || disable_sva)
    `ASSERT(aDataKnown_A,       h2d_pre_S and aDataKnown_pre_S |-> aDataKnown_S, !clk_i, !rst_ni)
    // d2h
    `ASSUME(respOpcode_M,       d2h_pre_S |-> respOpcode_S,       !clk_i, !rst_ni)
    `ASSUME(legalDParam_M,      d2h_pre_S |-> legalDParam_S,      !clk_i, !rst_ni)
    `ASSUME(respSzEqReqSz_M,    d2h_pre_S |-> respSzEqReqSz_S,    !clk_i, !rst_ni)
    `ASSUME(respMustHaveReq_M,  d2h_pre_S |-> respMustHaveReq_S,  !clk_i, !rst_ni)
    `ASSUME(dDataKnown_M,       d2h_pre_S and dDataKnown_pre_S |-> dDataKnown_S,
          !clk_i, !rst_ni || disable_sva)
  // in this case all signals coming from the host side have an assumed property
  end else if (EndpointType == "Device") begin : gen_device
    // h2d
    `ASSUME(legalAOpcode_M,      h2d_pre_S |-> legalAOpcode_S,     !clk_i, !rst_ni || disable_sva)
    `ASSUME(legalAParam_M,       h2d_pre_S |-> legalAParam_S,      !clk_i, !rst_ni)
    `ASSUME(sizeGTEMask_M,       h2d_pre_S |-> sizeGTEMask_S,      !clk_i, !rst_ni || disable_sva)
    `ASSUME(sizeMatchesMask_M,   h2d_pre_S |-> sizeMatchesMask_S,  !clk_i, !rst_ni || disable_sva)
    `ASSUME(pendingReqPerSrc_M,  h2d_pre_S |-> pendingReqPerSrc_S, !clk_i, !rst_ni)
    `ASSUME(addrSizeAligned_M,   h2d_pre_S |-> addrSizeAligned_S,  !clk_i, !rst_ni || disable_sva)
    `ASSUME(contigMask_M,        h2d_pre_S and contigMask_pre_S |-> contigMask_S,
          !clk_i, !rst_ni || disable_sva)
    `ASSUME(aDataKnown_M,        h2d_pre_S and aDataKnown_pre_S |-> aDataKnown_S, !clk_i, !rst_ni)
    // d2h
    `ASSERT(respOpcode_A,        d2h_pre_S |-> respOpcode_S,       !clk_i, !rst_ni)
    `ASSERT(legalDParam_A,       d2h_pre_S |-> legalDParam_S,      !clk_i, !rst_ni)
    `ASSERT(respSzEqReqSz_A,     d2h_pre_S |-> respSzEqReqSz_S,    !clk_i, !rst_ni)
    `ASSERT(respMustHaveReq_A,   d2h_pre_S |-> respMustHaveReq_S,  !clk_i, !rst_ni)
    `ASSERT(dDataKnown_A,        d2h_pre_S and dDataKnown_pre_S |-> dDataKnown_S,
          !clk_i, !rst_ni || disable_sva)
  end else begin : gen_unknown
    initial begin : p_unknonw
      `ASSERT_I(unknownConfig_A, 0 == 1)
    end
  end

  initial begin : p_dbw
    // widths up to 64bit / 8 Byte are supported
    `ASSERT_I(TlDbw_A, TL_DBW <= 8);
  end

  // make sure all "pending" bits are 0 at the end of the sim
  for (genvar ii = 0; ii < 2**TL_AIW; ii++) begin : gen_assert_final
    `ASSERT_FINAL(noOutstandingReqsAtEndOfSim_A, (pend_req[ii].pend == 0))
  end

  ////////////////////////////////////
  // additional checks for X values //
  ////////////////////////////////////

  // a_* should be known when a_valid == 1 (a_opcode and a_param are already covered above)
  // This also covers ASSERT_KNOWN of a_valid
  `ASSERT_VALID_DATA(aKnown_A, h2d.a_valid, {h2d.a_size, h2d.a_source, h2d.a_address,
      h2d.a_mask, h2d.a_user})

  // d_* should be known when d_valid == 1 (d_opcode, d_param, d_size already covered above)
  // This also covers ASSERT_KNOWN of d_valid
  `ASSERT_VALID_DATA(dKnown_A, d2h.d_valid, {d2h.d_source, d2h.d_sink, d2h.d_error, d2h.d_user})

  //  make sure ready is not X after reset
  `ASSERT_KNOWN(aReadyKnown_A, d2h.a_ready)
  `ASSERT_KNOWN(dReadyKnown_A, h2d.d_ready)
`endif
`endif
endmodule : tlul_assert
