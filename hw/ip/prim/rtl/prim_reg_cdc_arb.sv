// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Component handling register CDC

`include "prim_assert.sv"

// There are three handling scenarios.
// 1. The register can only be updated by software.
// 2. The register can be updated by both software and hardware.
// 3. The register can only be updated by hardware.
//
// For the first scenario, hardware updates are completely ignored.
// The software facing register (`src_q` in prim_reg_cdc) simply reflects
// the value affected by software.  Since there is no possibility the
// register value can change otherwise, there is no need to sample or
// do any other coordination between the two domains. In this case,
// we use the gen_passthru block below.
//
// For the second scenario, one of 4 things can happen:
// 1. A software update without conflict
// 2. A hardware update without conflict
// 3. A software update is initiated when a hardware update is in-flight
// 4. A hardware update is initiated when a software update is in-flight
//
// For the first case, it behaves similarly to the gen_passthru scenario.
//
// For the second case, the hardware update indication and update value are
// captured, and the intent to change is synchronized back to the software
// domain. While this happens, other hardware updates are ignored. Any hardware
// change during the update is then detected as a difference between the
// transit register `dst_qs_o` and the current hardware register value `dst_qs_i`.
// When this change is observed after the current handshake completes, another
// handshake event is generated to bring the latest hardware value over to the
// software domain.
//
// For the third case, if a hardware update event is already in progress, the
// software event is held and not acknowledged.  Once the hardware event completes,
// then the software event proceeds through its normal updating process.
//
// For the forth case, if a hardware update event is received while a software
// update is in progress, the hardware update is ignored, and the logic behaves
// similarly to the second case. Specifically, after the software update completes,
// a delta is observed between the transit register and the current hardware value,
// and a new handshake event is generated.
//
// The thrid scenario can be folded into the second scenario. The only difference
// is that of the 4 cases identified, only case 2 can happen since there is never a
// software initiated update.

module prim_reg_cdc_arb #(
  parameter int DataWidth = 32,
  parameter logic [DataWidth-1:0] ResetVal = 32'h0,
  parameter bit DstWrReq = 0
) (
  input clk_src_i,
  input rst_src_ni,
  input clk_dst_i,
  input rst_dst_ni,
  // destination side acknowledging a software transaction
  output logic src_ack_o,
  // destination side requesting a source side update after
  // after hw update
  output logic src_update_o,
  // input request from prim_reg_cdc
  input dst_req_i,
  // output request to prim_subreg
  output logic dst_req_o,
  input dst_update_i,
  // ds allows us to sample the destination domain register
  // one cycle earlier instead of waiting for it to be reflected
  // in the qs.
  // This is important because a genearl use case is that interrupts
  // are captured alongside payloads from the destination domain into
  // the source domain. If we rely on `qs` only, then it is very likely
  // that the software observed value will be behind the interrupt
  // assertion.  If the destination clock is very slow, this can seem
  // an error on the part of the hardware.
  input [DataWidth-1:0] dst_ds_i,
  input [DataWidth-1:0] dst_qs_i,
  output logic [DataWidth-1:0] dst_qs_o
);

  typedef enum logic {
    SelSwReq,
    SelHwReq
  } req_sel_e;

  typedef enum logic [1:0] {
    StIdle,
    StWait
  } state_e;

  if (DstWrReq) begin : gen_wr_req
    logic dst_lat_q;
    logic dst_lat_d;
    logic dst_update_req;
    logic dst_update_ack;
    req_sel_e id_q;

    state_e state_q, state_d;
    // Make sure to indent the following later
    always_ff @(posedge clk_dst_i or negedge rst_dst_ni) begin
      if (!rst_dst_ni) begin
        state_q <= StIdle;
      end else begin
        state_q <= state_d;
      end
    end

    logic busy;
    logic dst_req_q, dst_req;
    always_ff @(posedge clk_dst_i or negedge rst_dst_ni) begin
      if (!rst_dst_ni) begin
        dst_req_q <= '0;
      end else if (dst_req_q && dst_lat_d) begin
        // if request is held, when the transaction starts,
        // automatically clear.
        // dst_lat_d is safe to used here because dst_req_q, if set,
        // always has priority over other hardware based events.
        dst_req_q <= '0;
      end else if (dst_req_i && !dst_req_q && busy) begin
        // if destination request arrives when a handshake event
        // is already ongoing, hold on to request and send later
        dst_req_q <= 1'b1;
      end
    end
    assign dst_req = dst_req_q | dst_req_i;

    // Hold data at the beginning of a transaction
    always_ff @(posedge clk_dst_i or negedge rst_dst_ni) begin
      if (!rst_dst_ni) begin
        dst_qs_o <= ResetVal;
      end else if (dst_lat_d) begin
        dst_qs_o <= dst_ds_i;
      end else if (dst_lat_q) begin
        dst_qs_o <= dst_qs_i;
      end
    end

    // Which type of transaction is being ack'd back?
    // 0 - software initiated request
    // 1 - hardware initiated request
    // The id information is used by prim_reg_cdc to disambiguate
    // simultaneous updates from software and hardware.
    // See scenario 2 case 3 for an example of how this is handled.
    always_ff @(posedge clk_dst_i or negedge rst_dst_ni) begin
      if (!rst_dst_ni) begin
        id_q <= SelSwReq;
      end else if (dst_update_req && dst_update_ack) begin
        id_q <= SelSwReq;
      end else if (dst_req && dst_lat_d) begin
        id_q <= SelSwReq;
      end else if (!dst_req && dst_lat_d) begin
        id_q <= SelHwReq;
      end else if (dst_lat_q) begin
        id_q <= SelHwReq;
      end
    end

    // if a destination update is received when the system is idle and there is no
    // software side request, hw update must be selected.
    `ASSERT(DstUpdateReqCheck_A, ##1 dst_update_i & !dst_req & !busy |=> id_q == SelHwReq,
      clk_dst_i, !rst_dst_ni)

    // if hw select was chosen, then it must be the case there was a destination update
    // indication or there was a difference between the transit register and the
    // latest incoming value.
    `ASSERT(HwIdSelCheck_A, $rose(id_q == SelHwReq) |-> $past(dst_update_i, 1) ||
      $past(dst_lat_q, 1),
      clk_dst_i, !rst_dst_ni)


    // send out prim_subreg request only when proceeding
    // with software request
    assign dst_req_o = ~busy & dst_req;

    logic dst_hold_req;
    always_comb begin
      state_d = state_q;
      dst_hold_req = '0;

      // depending on when the request is received, we
      // may latch d or q.
      dst_lat_q = '0;
      dst_lat_d = '0;

      busy = 1'b1;

      unique case (state_q)
        StIdle: begin
          busy = '0;
          if (dst_req) begin
            // there's a software issued request for change
            state_d = StWait;
            dst_lat_d = 1'b1;
          end else if (dst_update_i) begin
            state_d = StWait;
            dst_lat_d = 1'b1;
          end else if (dst_qs_o != dst_qs_i) begin
            // there's a direct destination update
            // that was blocked by an ongoing transaction
            state_d = StWait;
            dst_lat_q = 1'b1;
          end
        end

        StWait: begin
          dst_hold_req = 1'b1;
          if (dst_update_ack) begin
            state_d = StIdle;
          end
        end

        default: begin
          state_d = StIdle;
        end
      endcase // unique case (state_q)
    end // always_comb

    assign dst_update_req = dst_hold_req | dst_lat_d | dst_lat_q;
    logic src_req;
    prim_sync_reqack u_dst_update_sync (
      .clk_src_i(clk_dst_i),
      .rst_src_ni(rst_dst_ni),
      .clk_dst_i(clk_src_i),
      .rst_dst_ni(rst_src_ni),
      .req_chk_i(1'b1),
      .src_req_i(dst_update_req),
      .src_ack_o(dst_update_ack),
      .dst_req_o(src_req),
      // immediate ack
      .dst_ack_i(src_req)
    );

    assign src_ack_o = src_req & (id_q == SelSwReq);
    assign src_update_o = src_req & (id_q == SelHwReq);

    // once hardware makes an update request, we must eventually see an update pulse
    `ASSERT(ReqTimeout_A, $rose(id_q == SelHwReq) |-> s_eventually(src_update_o),
      clk_src_i, !rst_src_ni)

    `ifdef INC_ASSERT
      logic async_flag;
      always_ff @(posedge clk_dst_i or negedge rst_dst_ni or posedge src_update_o) begin
        if (!rst_dst_ni) begin
          async_flag <= '0;
        end else if (src_update_o) begin
          async_flag <= '0;
        end else if (dst_update_i && !dst_req_o && !busy) begin
          async_flag <= 1'b1;
        end
      end

     // once hardware makes an update request, we must eventually see an update pulse
     `ASSERT(UpdateTimeout_A, $rose(async_flag) |-> s_eventually(src_update_o),
       clk_src_i, !rst_src_ni)
    `endif

  end else begin : gen_passthru
    // when there is no possibility of conflicting HW transactions,
    // we can assume that dst_qs_i will only ever take on the value
    // that is directly related to the transaction. As a result,
    // there is no need to latch further, and the end destination
    // can in fact be used as the holding register.
    assign dst_qs_o = dst_qs_i;
    assign dst_req_o = dst_req_i;

    // since there are no hw transactions, src_update_o is always '0
    assign src_update_o = '0;

    prim_pulse_sync u_dst_to_src_ack (
      .clk_src_i(clk_dst_i),
      .rst_src_ni(rst_dst_ni),
      .clk_dst_i(clk_src_i),
      .rst_dst_ni(rst_src_ni),
      .src_pulse_i(dst_req_i),
      .dst_pulse_o(src_ack_o)
    );

    logic unused_sigs;
    assign unused_sigs = |{dst_ds_i, dst_update_i};
  end



endmodule
