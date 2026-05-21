// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface kmac_app_if
  import kmac_pkg::app_req_t, kmac_pkg::app_rsp_t;
(
 input      clk_i,
 input      rst_ni,
 inout wire app_req_t req,
 inout wire app_rsp_t rsp
);

  import kmac_pkg::MsgWidth, kmac_pkg::MsgStrbW, kmac_pkg::AppDigestW;
  import dv_utils_pkg::if_mode_e, dv_utils_pkg::Host, dv_utils_pkg::Device;

  // Do the clocking blocks control req, rsp or neither?
  if_mode_e if_mode;

  // The request signals, as driven by host_cb (only used if if_mode == Host)
  logic                valid_driven, valid_internal;
  logic [MsgWidth-1:0] data_driven, data_internal;
  logic [MsgStrbW-1:0] strb_driven, strb_internal;
  logic                last_driven, last_internal;

  // A view of the req signals that are driven by host_cb, but structured as an app_req_t (matching
  // the format of req). Only used if if_mode == Host.
  wire app_req_t req_internal;
  assign req_internal = {valid_internal, data_internal, strb_internal, last_internal};

  assign req = (if_mode == Host) ? req_internal : 'z;

  // The response signals, as driven by device_cb (only used if if_mode == Device)
  logic                  ready_driven, ready_internal;
  logic                  done_driven, done_internal;
  logic [AppDigestW-1:0] digest_share0_driven, digest_share0_internal;
  logic [AppDigestW-1:0] digest_share1_driven, digest_share1_internal;
  logic                  rsp_error_driven, rsp_error_internal;

  // A view of the rsp signals that are driven by device_cb, but structured as an app_rsp_t
  // (matching the format of kmac_data_rsp). Only used if if_mode == Device.
  wire app_rsp_t rsp_internal;
  assign rsp_internal = {ready_internal, done_internal,
                         digest_share0_internal, digest_share1_internal,
                         rsp_error_internal};

  assign rsp = (if_mode == Device) ? rsp_internal : 'z;

  // Unpack various signals from req and rsp intor wires in order to use them in clocking blocks.
  // Not all EDA tools allow references into structures in clocking blocks (which would use syntax
  // like "input foo = my_struct.foo")
  wire                req_valid;
  wire [MsgWidth-1:0] req_data;
  wire [MsgStrbW-1:0] req_strb;
  wire                req_last;
  wire                req_ready;

  assign req_valid = req.valid;
  assign req_data  = req.data;
  assign req_strb  = req.strb;
  assign req_last  = req.last;
  assign req_ready = rsp.ready;

  wire                  rsp_done;
  wire [AppDigestW-1:0] rsp_digest_share0;
  wire [AppDigestW-1:0] rsp_digest_share1;
  wire                  rsp_error;

  assign rsp_done          = rsp.done;
  assign rsp_digest_share0 = rsp.digest_share0;
  assign rsp_digest_share1 = rsp.digest_share1;
  assign rsp_error         = rsp.error;

  clocking host_cb @(posedge clk_i);
    output valid = valid_driven;
    output data  = data_driven;
    output strb  = strb_driven;
    output last  = last_driven;

    input  ready = req_ready;
  endclocking

  clocking device_cb @(posedge clk_i);
    // Requests (The ready signal shows that the device can consume one)
    output ready         = ready_driven;

    // Responses (The "done" signal shows there is a response. It gates the other three signals)
    output done          = done_driven;
    output digest_share0 = digest_share0_driven;
    output digest_share1 = digest_share1_driven;
    output error         = rsp_error_driven;
  endclocking

  clocking mon_cb @(posedge clk_i);
    input req_valid;
    input req_data;
    input req_strb;
    input req_last;
    input req_ready;

    input rsp_done;
    input rsp_digest_share0;
    input rsp_digest_share1;
    input rsp_error;
  endclocking

  // Take signals from host_cb and device_cb, but clear on reset. Splitting things like this means
  // that a driver just has to clear the signal in the clocking block when reset is asserted,
  // meaning the signal gets cleared immediately in both the interface signal and the internal
  // clocking block signal.
  always_comb begin
    if (!rst_ni) begin
      valid_internal         = '0;
      data_internal          = '0;
      strb_internal          = '0;
      last_internal          = '0;
      ready_internal         = '0;
      done_internal          = '0;
      digest_share0_internal = '0;
      digest_share1_internal = '0;
      rsp_error_internal     = '0;
    end else begin
      valid_internal         = valid_driven;
      data_internal          = data_driven;
      strb_internal          = strb_driven;
      last_internal          = last_driven;
      ready_internal         = ready_driven;
      done_internal          = done_driven;
      digest_share0_internal = digest_share0_driven;
      digest_share1_internal = digest_share1_driven;
      rsp_error_internal     = rsp_error_driven;
    end
  end

  default clocking @(posedge clk_i); endclocking
  default disable iff (!rst_ni);

  // A request should never contain a zero strobe
  StrbNotZero_A:
    assert property (mon_cb.req_valid |-> |mon_cb.req_strb)
    else `ASSERT_ERROR(StrbNotZero_A)

  // The strb signal should be aligned to the LSB.
  //
  // Interpreted as an integer, this means it should be of the form 2^k - 1 for some k. As such,
  // strb & (strb + 1) should be zero.
  StrbAlignLSB_A:
    assert property (mon_cb.req_valid |-> ~|(mon_cb.req_strb & (mon_cb.req_strb + 1)))
    else `ASSERT_ERROR(StrbAlignLSB_A)

  // Overlapping requests are not allowed: rsp.done must be asserted after a request with the last
  // field set before any more requests are sent.
  DoneAssertAfterLast_A:
    assert property ((mon_cb.req_last && mon_cb.req_valid && mon_cb.req_ready) |=>
                     !mon_cb.req_valid throughout mon_cb.rsp_done[->1])
    else `ASSERT_ERROR(DoneAssertAfterLast_A)

  // Utility task that waits num_cycles clock cycles and then returns. Returns instantly on reset.
  task automatic wait_cycles(int unsigned num_cycles);
    fork : isolation_fork begin
      fork
        repeat (num_cycles) @mon_cb;
        wait (!rst_ni);
      join_any
      disable fork;
    end join
  endtask

endinterface
