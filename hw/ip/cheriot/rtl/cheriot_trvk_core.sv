// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

// Protocol-independent core of the TRVK revocation filter.
module cheriot_trvk_core #(
  // The number of outstanding transaction the IP supports
  parameter int unsigned NumOutstanding     = 32'd4,
  // The width of the meta memory byte address space used to store the revocation bits
  parameter int unsigned RevBitmapAddrWidth = 32'd11,
  // The size of the revocation bitmap in bytes; bases beyond it have no revocation bit
  parameter int unsigned RevBitmapSizeBytes = 32'd1 << RevBitmapAddrWidth,
  // The base byte address of the meta SRAM holding the revocation bitmap
  parameter int unsigned RevBitmapBaseAddr  = 32'h0000_0000,
  // Enable ECC checking on the revocation bitmap memory data
  parameter bit          MemECC             = 1'b1
)(
  input  logic clk_i,
  input  logic rst_ni,

  // The base address of the (heap) memory where to be revocable capabilities point to
  input  logic [31:0] heap_base_addr_i,

  // Upstream request
  input  logic        upstream_req_valid_i,
  output logic        upstream_req_ready_o,
  input  logic        upstream_req_misalign_i,
  input  logic        upstream_tag_i,

  // Upstream response
  output logic        upstream_rsp_valid_o,
  input  logic        upstream_rsp_ready_i,
  output logic        upstream_tag_o,

  // Downstream request
  output logic        downstream_req_valid_o,
  input  logic        downstream_req_ready_i,
  output logic        downstream_tag_o,

  // Downstream response
  input  logic        downstream_rsp_valid_i,
  output logic        downstream_rsp_ready_o,
  input  logic [31:0] downstream_rsp_data_i,
  input  logic        downstream_tag_i,

  // Revocation bitmap request
  output logic        revbm_req_valid_o,
  input  logic        revbm_req_ready_i,
  output logic [31:0] revbm_req_addr_o,

  // Revocation bitmap response; an error counts as revoked
  input  logic        revbm_rsp_valid_i,
  output logic        revbm_rsp_ready_o,
  input  logic [31:0] revbm_rsp_data_i,
  input  logic [6:0]  revbm_rsp_data_intg_i,
  input  logic        revbm_rsp_err_i,

  // Error signals
  output logic revbm_data_intg_error_o
);

  import ibex_cheriot_pkg::*;

  ///////////
  // Types //
  ///////////

  localparam int unsigned RevBitmapWordAddrWidth = RevBitmapAddrWidth - 32'd2;

  // Revocation bitmap word address type
  typedef logic [RevBitmapWordAddrWidth-1:0] revbm_addr_t;

  // Local capability metadata type to facilitate parsing of the fields.
  typedef struct packed {
    exp_t    exponent;
    cbound_t base;
    otype_t  otype;
    cperms_t cperms;
  } cap_meta_t;


  /////////////
  // Signals //
  /////////////

  // Signals connecting the upstream-to-downstream (request) fork to the alignment store.
  logic align_fork_valid;
  logic align_fork_ready;

  // Alignment store output
  logic misalign_flag_out;
  logic misalign_flag_out_valid;
  logic misalign_flag_out_ready;

  // Pointer store signals
  logic [31:0] ptr_storage_q;
  logic        ptr_storage_valid_q;
  logic        ptr_storage_enable;

  // Base (address) calculation
  cap_meta_t    cap_meta;
  logic         unused_cap_meta;
  logic         is_sealing_cap;
  logic [32:0]  cap_base_33;
  logic         unused_cap_base_33;
  logic [31:0]  cap_base;
  cbound_t      addr_mid;
  cap_cor_t     cap_correction;
  logic         unused_cap_correction;

  // Revocation bitmap addressing
  logic [31:0] revbm_cap_addr;
  logic [31:0] revbm_bit_addr;
  logic [ 4:0] revbm_bit_select;
  revbm_addr_t revbm_addr;
  logic        revbm_out_of_range;

  // Revocation bitmap signals
  logic revbm_req_required;
  logic revbm_outstanding_q;
  logic revbm_revoked;

  // Bitmap response ECC signals
  logic [1:0] revbm_rsp_data_intg_error;


  //////////////////////////////////////
  // Upstream to Downstream Intercept //
  //////////////////////////////////////

  // Both the downstream port and the alignment store need to handshake for
  // the stream to advance.
  stream_fork #(
    .N_OUP(32'd2)
  ) u_stream_fork_us2ds (
    .clk_i,
    .rst_ni,
    .valid_i(upstream_req_valid_i),
    .ready_o(upstream_req_ready_o),
    .valid_o({align_fork_valid, downstream_req_valid_o}),
    .ready_i({align_fork_ready, downstream_req_ready_i})
  );

  // The upstream port and on lookup the revocation bitmap must handshake to advance the stream
  // We use `revbm_req_required` as a section signal here. If there is a bitmap lookup required,
  // this signal gets asserted beyond the request handshake completion until the response arrives.
  stream_join_dynamic #(
    .N_INP(32'd2)
  ) u_stream_join_dynamic_ds2us (
    .inp_valid_i({revbm_rsp_valid_i,   downstream_rsp_valid_i}),
    .inp_ready_o({revbm_rsp_ready_o,   downstream_rsp_ready_o}),
    .sel_i      ({revbm_req_required,  1'b1                  }),
    .oup_valid_o(upstream_rsp_valid_o),
    .oup_ready_i(upstream_rsp_ready_i)
  );

  // Forward upstream to downstream CHERIoT tag without changes
  assign downstream_tag_o = upstream_tag_i;

  // Tag handling; always return tag except if we do a revocation bitmap lookup
  assign upstream_tag_o = (revbm_rsp_valid_i ? !revbm_revoked : 1'b1) & downstream_tag_i;

  // 64-bit alignment store
  prim_fifo_sync #(
    .Width(32'd1),
    .Pass(1'b0),
    .Depth(NumOutstanding),
    .NeverClears(1'b1),
    .Secure(1'b0)
  ) u_prim_fifo_sync_align (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(align_fork_valid),
    .wready_o(align_fork_ready),
    .wdata_i (upstream_req_misalign_i),
    .rvalid_o(misalign_flag_out_valid),
    .rready_i(misalign_flag_out_ready),
    .rdata_o (misalign_flag_out),
    .full_o  (),
    .depth_o (),
    .err_o   ()
  );

  // Element is consumed, if upstream handshakes response
  assign misalign_flag_out_ready = upstream_rsp_valid_o && upstream_rsp_ready_i;


  ///////////////////
  // Pointer Store //
  ///////////////////

  // Pointer valid store. Pointer, `ptr` refers here to the lower word of a capability, which
  // corresponds to the C pointer. The 32-bit interconnect first passes the pointer, which
  // is stored in `ptr_storage_q` with a valid signal in `ptr_storage_valid_q`.

  // Pointer buffer could be filled iff tag valid & 64-bit aligned.
  assign ptr_storage_enable = downstream_tag_i && !misalign_flag_out && misalign_flag_out_valid;

  // Pointer store
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_pointer_store
    if(!rst_ni) begin
      ptr_storage_q <= '0;
    end else begin
      if (misalign_flag_out_ready && ptr_storage_enable) begin
        ptr_storage_q <= downstream_rsp_data_i;
      end
    end
  end

  // Pointer valid store
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_pointer_valid_store
    if(!rst_ni) begin
      ptr_storage_valid_q <= 1'b0;
    end else begin
      if (misalign_flag_out_ready) begin
        ptr_storage_valid_q <= ptr_storage_enable;
      end
    end
  end


  ////////////////////////////////
  // Bitmap Address Calculation //
  ////////////////////////////////

  assign cap_meta = '{
    base:     downstream_rsp_data_i[8:0],
    exponent: cheriot_expand_exp(downstream_rsp_data_i[21:18]),
    otype:    downstream_rsp_data_i[24:22],
    cperms:   downstream_rsp_data_i[30:25]
  };

  // Only base, exponent and the sealing-relevant permission bits are used
  assign unused_cap_meta = ^{cap_meta.otype, cap_meta.cperms[5]};

  // Check if cap is sealing cap
  assign is_sealing_cap = cheriot_is_sealing_cap(cap_meta.cperms);

  // Extract the middle field from the pointer, bounds depend on exponent, width fixed
  assign addr_mid = cbound_t'(ptr_storage_q >> cap_meta.exponent);

  // Fetch the correction values, we are only interested in the base correction value (1 bit)
  // top-related inputs are set to zero, top-related outputs ignored
  assign cap_correction = cheriot_compute_corrections('0, cap_meta.base, addr_mid);

  // Calculate the base address of the capability as a 33-bit value
  assign cap_base_33 = cheriot_expand_bound33(cap_meta.base,
                                              cheriot_get_base_correction(cap_correction),
                                              cap_meta.exponent, ptr_storage_q);

  // We don't need the correction bits corresponding to the top address
  assign unused_cap_correction = ^cap_correction;

  // The MSB is unused in our case
  assign {unused_cap_base_33, cap_base} = cap_base_33;

  // Byte offset of the capability base into the revocable heap
  assign revbm_cap_addr = cap_base - heap_base_addr_i;

  // Bit address in the revocation bitmap (every bit corresponds to one 64-bit capability)
  assign revbm_bit_addr = revbm_cap_addr >> $clog2(64/8);

  // Word address of the revocation bitmap
  assign revbm_addr = revbm_bit_addr[RevBitmapWordAddrWidth+$clog2(32)-1:$clog2(32)];

  // Bit select
  assign revbm_bit_select = revbm_bit_addr[$clog2(32)-1:0];

  // Capability base is outside of the bitmap range
  assign revbm_out_of_range = revbm_bit_addr >= RevBitmapSizeBytes * 32'd8;


  //////////////////////
  // Bitmap Interface //
  //////////////////////

  // We have loaded valid capability pointer, now we see valid metadata, not a sealing cap,
  // and are pointing into the revocation bitmap
  assign revbm_req_required = !is_sealing_cap          && // Not sealing cap
                              ptr_storage_valid_q      && // The pointer stored is valid
                              downstream_tag_i         && // We are looking at a capability
                              downstream_rsp_valid_i   && // The downstream response is valid
                              misalign_flag_out        && // We are on the second word of the cap
                              misalign_flag_out_valid  && // The latched alignment bits are valid
                              !revbm_out_of_range;        // We hit the heap range

  // Assemble read-only request
  assign revbm_req_valid_o = revbm_req_required && !revbm_outstanding_q;
  assign revbm_req_addr_o  = RevBitmapBaseAddr +
                             {{32 - RevBitmapWordAddrWidth - 2{1'b0}}, revbm_addr, 2'b00};

  // Is the current capability marked as revoked? Any error on the bitmap response is treated as
  // revoked, so a corrupted or failed lookup can never let a revoked capability through.
  assign revbm_revoked = revbm_rsp_data_i[revbm_bit_select] || revbm_rsp_err_i ||
                         (|revbm_rsp_data_intg_error);

  // Check the bitmap response data integrity
  if (MemECC) begin : gen_revbm_intg_check
    prim_secded_inv_39_32_dec u_prim_secded_inv_39_32_dec_revbm_rsp_data (
      .data_i    ({revbm_rsp_data_intg_i, revbm_rsp_data_i}),
      .data_o    (),
      .syndrome_o(),
      .err_o     (revbm_rsp_data_intg_error)
    );

    // Mask response integrity error if response is not being handshaked
    assign revbm_data_intg_error_o = revbm_rsp_valid_i && revbm_rsp_ready_o &&
                                     (|revbm_rsp_data_intg_error);
  end else begin : gen_no_revbm_intg_check
    logic unused_revbm_rdata_intg;
    assign unused_revbm_rdata_intg = ^revbm_rsp_data_intg_i;

    assign revbm_rsp_data_intg_error = 2'b00;
    assign revbm_data_intg_error_o   = 1'b0;
  end

  // One outstanding request
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_rev_req_store
    if(!rst_ni) begin
      revbm_outstanding_q <= 1'b0;
    end else begin
      if (revbm_rsp_valid_i && revbm_rsp_ready_o) begin
        revbm_outstanding_q <= 1'b0;
      end else if (revbm_req_valid_o && revbm_req_ready_i) begin
        revbm_outstanding_q <= 1'b1;
      end
    end
  end


  ////////////////
  // Assertions //
  ////////////////

  // Every delivered response has its alignment information available.
  `ASSERT(AlignValidOnRsp_A, upstream_rsp_valid_o |-> misalign_flag_out_valid)
  // No unsolicited bitmap response; this is what keeps `upstream_tag_o` safe. The response may
  // arrive in the same cycle as its request.
  `ASSERT(RevbmRspOnlyWhenOutstanding_A, revbm_rsp_valid_i |->
                                         revbm_outstanding_q ||
                                         (revbm_req_valid_o && revbm_req_ready_i))
  // Request stability on the bitmap port. The request is derived from the downstream response, so
  // this holds as long as the downstream device holds a response it has presented.
  `ASSERT(RevbmReqStable_A, revbm_req_valid_o && !revbm_req_ready_i |=>
                            revbm_req_valid_o && $stable(revbm_req_addr_o))
  `ASSERT_INIT(RevBitmapWordAddrWidthRange_A, RevBitmapWordAddrWidth inside {[1:26]})
  `ASSERT_INIT(RevBitmapBaseAddrAligned_A, RevBitmapBaseAddr[1:0] == 2'b00)
  `ASSERT_INIT(RevBitmapSizeFits_A, RevBitmapSizeBytes <= (32'd1 << RevBitmapAddrWidth))
  `ASSERT(HeapBaseAligned_A, heap_base_addr_i[2:0] == 3'b0)

endmodule
