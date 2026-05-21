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
  logic                req_valid_driven, req_valid_internal;
  logic [MsgWidth-1:0] data_s0_driven, data_s0_internal;
  logic [MsgWidth-1:0] data_s1_driven, data_s1_internal;
  logic [MsgStrbW-1:0] strb_driven, strb_internal;
  logic                req_last_driven, req_last_internal;
  logic                rsp_ready_driven, rsp_ready_internal;

  // A view of the req signals that are driven by host_cb, but structured as an app_req_t (matching
  // the format of req). Only used if if_mode == Host.
  wire app_req_t req_internal;
  assign req_internal = {req_valid_internal,
                         data_s0_internal,
                         data_s1_internal,
                         strb_internal,
                         req_last_internal,
                         rsp_ready_internal};

  assign req = (if_mode == Host) ? req_internal : 'z;

  // The response signals, as driven by device_cb (only used if if_mode == Device)
  logic                  req_ready_driven, req_ready_internal;
  logic                  rsp_valid_driven, rsp_valid_internal;
  logic [AppDigestW-1:0] digest_s0_driven, digest_s0_internal;
  logic [AppDigestW-1:0] digest_s1_driven, digest_s1_internal;
  logic                  rsp_error_driven, rsp_error_internal;
  logic                  rsp_finish_driven, rsp_finish_internal;

  // A view of the rsp signals that are driven by device_cb, but structured as an app_rsp_t
  // (matching the format of kmac_data_rsp). Only used if if_mode == Device.
  wire app_rsp_t rsp_internal;
  assign rsp_internal = {req_ready_internal,
                         rsp_valid_internal,
                         digest_s0_internal,
                         digest_s1_internal,
                         rsp_error_internal,
                         rsp_finish_internal};

  assign rsp = (if_mode == Device) ? rsp_internal : 'z;

  // Unpack various signals from req and rsp into wires in order to use them in clocking blocks.
  // Not all EDA tools allow references into structures in clocking blocks (which would use syntax
  // like "input foo = my_struct.foo")
  wire                req_valid;
  wire [MsgWidth-1:0] req_data_s0;
  wire [MsgWidth-1:0] req_data_s1;
  wire [MsgStrbW-1:0] req_strb;
  wire                req_last;
  wire                req_ready;

  assign req_valid    = req.req_valid;
  assign req_data_s0  = req.data_s0;
  assign req_data_s1  = req.data_s1;
  assign req_strb     = req.strb;
  assign req_last     = req.req_last;
  assign req_ready    = rsp.req_ready;

  wire                  rsp_valid;
  wire [AppDigestW-1:0] rsp_digest_s0;
  wire [AppDigestW-1:0] rsp_digest_s1;
  wire                  rsp_error;
  wire                  rsp_finish;
  wire                  rsp_ready;

  assign rsp_valid     = rsp.rsp_valid;
  assign rsp_digest_s0 = rsp.digest_s0;
  assign rsp_digest_s1 = rsp.digest_s1;
  assign rsp_error     = rsp.error;
  assign rsp_finish    = rsp.rsp_finish;
  assign rsp_ready     = req.rsp_ready;

  clocking host_cb @(posedge clk_i);
    output req_valid = req_valid_driven;
    output data_s0   = data_s0_driven;
    output data_s1   = data_s1_driven;
    output strb      = strb_driven;
    output req_last  = req_last_driven;

    output rsp_ready = rsp_ready_driven;

    input  req_ready;
  endclocking

  clocking device_cb @(posedge clk_i);
    // Requests (The ready signal shows that the device can consume one)
    output req_ready     = req_ready_driven;

    // Responses
    output rsp_valid = rsp_valid_driven;
    output digest_s0 = digest_s0_driven;
    output digest_s1 = digest_s1_driven;
    output error     = rsp_error_driven;
    output finish    = rsp_finish_driven;

    input  rsp_ready;
  endclocking

  clocking mon_cb @(posedge clk_i);
    input req_valid;
    input req_data_s0;
    input req_data_s1;
    input req_strb;
    input req_last;
    input req_ready;

    input rsp_valid;
    input rsp_digest_s0;
    input rsp_digest_s1;
    input rsp_error;
    input rsp_finish;
    input rsp_ready;
  endclocking

  // Take signals from host_cb and device_cb, but clear on reset. Splitting things like this means
  // that a driver just has to clear the signal in the clocking block when reset is asserted,
  // meaning the signal gets cleared immediately in both the interface signal and the internal
  // clocking block signal.
  always_comb begin
    if (!rst_ni) begin
      req_valid_internal  = '0;
      data_s0_internal    = '0;
      data_s1_internal    = '0;
      strb_internal       = '0;
      req_last_internal   = '0;
      rsp_ready_internal  = '0;

      req_ready_internal  = '0;
      rsp_valid_internal  = '0;
      digest_s0_internal  = '0;
      digest_s1_internal  = '0;
      rsp_error_internal  = '0;
      rsp_finish_internal = '0;
    end else begin
      req_valid_internal  = req_valid_driven;
      data_s0_internal    = data_s0_driven;
      data_s1_internal    = data_s1_driven;
      strb_internal       = strb_driven;
      req_last_internal   = req_last_driven;
      rsp_ready_internal  = rsp_ready_driven;

      req_ready_internal  = req_ready_driven;
      rsp_valid_internal  = rsp_valid_driven;
      digest_s0_internal  = digest_s0_driven;
      digest_s1_internal  = digest_s1_driven;
      rsp_error_internal  = rsp_error_driven;
      rsp_finish_internal = rsp_finish_driven;
    end
  end

  default clocking @(posedge clk_i); endclocking
  default disable iff (!rst_ni);

  // The strb signal should be aligned to the LSB.
  //
  // Interpreted as an integer, this means it should be of the form 2^k - 1 for some k. As such,
  // strb & (strb + 1) should be zero.
  StrbAlignLSB_A:
    assert property (mon_cb.req_valid |-> ~|(mon_cb.req_strb & (mon_cb.req_strb + 1)))
    else `ASSERT_ERROR(StrbAlignLSB_A)

  // Overlapping requests are not allowed: rsp_valid must be asserted after a request with the last
  // field set before any more requests are sent.
  NoReqBeforeLastResponse_A:
    assert property ((mon_cb.req_last && mon_cb.req_valid && mon_cb.req_ready) |=>
                     !mon_cb.req_valid throughout mon_cb.rsp_valid[->1])
    else `ASSERT_ERROR(NoReqBeforeLastResponse_A)

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
