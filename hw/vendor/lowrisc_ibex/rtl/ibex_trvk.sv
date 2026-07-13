// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module ibex_trvk #(
  // The number of outstanding transaction the IP supports
  parameter int unsigned NumOutstanding     = 32'd4,
  // The width of the meta memory address space used to store the revocation bits
  parameter int unsigned RevBitmapAddrWidth = 32'd9,
  // The base address of the meta SRAM holding the revocation bitmap
  parameter int unsigned RevBitmapBaseAddr  = 32'h0000_0000
)(
  input clk_i,
  input rst_ni,

  // The base address of the (heap) memory where to be revocable capabilities point to
  input logic [31:0] heap_base_addr_i,

  // Upstream port
  input  logic        upstream_req_i,
  output logic        upstream_gnt_o,
  output logic        upstream_rvalid_o,
  input  logic        upstream_we_i,
  input  logic [3:0]  upstream_be_i,
  input  logic [31:0] upstream_addr_i,
  input  logic [31:0] upstream_wdata_i,
  input  logic [6:0]  upstream_wdata_intg_i,
  output logic [31:0] upstream_rdata_o,
  output logic [6:0]  upstream_rdata_intg_o,
  output logic        upstream_err_o,
  input  logic        upstream_tag_i,
  output logic        upstream_tag_o,

  // Downstream port
  output logic        downstream_req_o,
  input  logic        downstream_gnt_i,
  input  logic        downstream_rvalid_i,
  output logic        downstream_we_o,
  output logic [3:0]  downstream_be_o,
  output logic [31:0] downstream_addr_o,
  output logic [31:0] downstream_wdata_o,
  output logic [6:0]  downstream_wdata_intg_o,
  input  logic [31:0] downstream_rdata_i,
  input  logic [6:0]  downstream_rdata_intg_i,
  input  logic        downstream_err_i,
  output logic        downstream_tag_o,
  input  logic        downstream_tag_i,

  // Revocation bitmap memory port
  output logic        revbm_req_o,
  input  logic        revbm_gnt_i,
  input  logic        revbm_rvalid_i,
  output logic [31:0] revbm_addr_o,
  input  logic [31:0] revbm_rdata_i,
  input  logic [6:0]  revbm_rdata_intg_i,
  input  logic        revbm_err_i,

  // Error signals
  output logic revbm_data_intg_error_o,
  output logic revbm_device_error_o
);


  ///////////
  // Types //
  ///////////

  // Expanded exponent (5 bit). Exponent 'd15 stored in memory is mapped to 'd24.
  typedef logic [ibex_cheriot_pkg::EXP_W-1:0]    cheriot_exp_t;
  typedef logic [ibex_cheriot_pkg::BOT_W-1:0]    cheriot_bot_t;
  typedef logic [ibex_cheriot_pkg::OTYPE_W-1:0]  cheriot_otype_t;
  typedef logic [ibex_cheriot_pkg::CPERMS_W-1:0] cheriot_cperms_t;

  // Revocation bitmap word address type
  typedef logic [RevBitmapAddrWidth-1:0] revbm_addr_t;

  // Local capability metadata type to facilitate parsing of the fields.
  typedef struct packed {
    cheriot_exp_t    exponent;
    cheriot_bot_t    base;
    cheriot_otype_t  otype;
    cheriot_cperms_t cperms;
  } cap_meta_t;

  // Local downstream response type
  typedef struct packed {
    logic [31:0] data;
    logic [6:0]  intg;
    logic        tag;
    logic        err;
  } ds_rsp_t;


  /////////////
  // Signals //
  /////////////

  // Signals connecting the request to the alignment store.
  logic align_fork_valid;
  logic align_fork_ready;

  // Alignment store output
  logic align_out;
  logic align_out_valid;
  logic align_out_ready;

  // Pointer store signals
  logic [31:0] ptr_store_q;
  logic        ptr_store_valid_q;
  logic        ptr_store_enable;

  // Downstream response store output
  ds_rsp_t downstream_rsp_in;
  ds_rsp_t downstream_rsp_out;
  logic    downstream_rsp_out_valid;
  logic    downstream_rsp_out_ready;

  // Base (address) calculation
  cap_meta_t    cap_meta;
  logic         unused_cap_meta;
  logic         is_sealing_cap;
  logic [32:0]  cap_base_33;
  logic         unused_cap_base_33;
  logic [31:0]  cap_base;
  cheriot_bot_t addr_mid;
  logic [ 2:0]  cap_correction;
  logic         unused_cap_correction;

  // Revocation bitmap addressing
  logic [31:0] revbm_cap_addr;
  logic [31:0] revbm_bit_addr;
  logic [ 4:0] revbm_bit_select;
  revbm_addr_t revbm_addr;
  logic        revbm_out_of_range;

  // Revocation bitmap signals
  logic revbm_req_required;
  logic revbm_rsp_ready;
  logic revbm_outstanding_q;
  logic revbm_revoked;

  // Bitmap response ECC signals
  logic [1:0] revbm_rsp_data_intg_error;


  //////////////////////////////
  // Host to Device Intercept //
  //////////////////////////////

  // Both the device and the alignment store need to handshake for
  // the stream to advance.
  stream_fork #(
    .N_OUP(32'd2)
  ) u_stream_fork_h2d (
    .clk_i,
    .rst_ni,
    .valid_i(upstream_req_i),
    .ready_o(upstream_gnt_o),
    .valid_o({align_fork_valid, downstream_req_o}),
    .ready_i({align_fork_ready, downstream_gnt_i})
  );

  // The host and on lookup the revocation bitmap must handshake to advance the stream
  // We use `revbm_req_required` as a section signal here. If there is a bitmap lookup required,
  // this signal gets asserted beyond the request handshake completion until the response arrives.
  stream_join_dynamic #(
    .N_INP(32'd2)
  ) u_stream_join_dynamic_d2h (
    .inp_valid_i({revbm_rvalid_i,     downstream_rsp_out_valid}),
    .inp_ready_o({revbm_rsp_ready,    downstream_rsp_out_ready}),
    .sel_i      ({revbm_req_required, 1'b1                    }),
    .oup_valid_o(upstream_rvalid_o),
    .oup_ready_i(1'b1)
  );

  // Forward OBI payload between host and device
  assign downstream_we_o         = upstream_we_i;
  assign downstream_be_o         = upstream_be_i;
  assign downstream_addr_o       = upstream_addr_i;
  assign downstream_wdata_o      = upstream_wdata_i;
  assign downstream_wdata_intg_o = upstream_wdata_intg_i;
  assign upstream_rdata_o        = downstream_rsp_out.data;
  assign upstream_rdata_intg_o   = downstream_rsp_out.intg;
  assign upstream_err_o          = downstream_rsp_out.err;

  // Forward host to device CHERIoT tag w/o changes
  assign downstream_tag_o = upstream_tag_i;

  // Tag handling; always return tag except if we do a revocation bitmap lookup
  assign upstream_tag_o = revbm_rvalid_i ? !revbm_revoked : downstream_rsp_out.tag;

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
    .wdata_i (upstream_addr_i[2]),
    .rvalid_o(align_out_valid),
    .rready_i(align_out_ready),
    .rdata_o (align_out),
    .full_o  (),
    .depth_o (),
    .err_o   ()
  );

  // Element is consumed, if host handshakes response
  assign align_out_ready = upstream_rvalid_o;


  ///////////////////
  // Pointer Store //
  ///////////////////

  // Pointer buffer is filled iff tag valid & 64-bit aligned
  assign ptr_store_enable = downstream_rsp_out.tag && !align_out && align_out_valid &&
                            align_out_ready;

  // Pointer store
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_pointer_store
    if(!rst_ni) begin
      ptr_store_q <= '0;
    end else begin
      if (ptr_store_enable) begin
        ptr_store_q <= downstream_rsp_out.data;
      end
    end
  end

  // Pointer valid store
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_pointer_vaild_store
    if(!rst_ni) begin
      ptr_store_valid_q <= 1'b0;
    end else begin
      if (align_out_ready) begin
        ptr_store_valid_q <= ptr_store_enable;
      end
    end
  end


  //////////////////////////////////
  // Downstream Response Latching //
  //////////////////////////////////

  // downstream response store
  prim_fifo_sync #(
    .Width($bits(ds_rsp_t)),
    .Pass(1'b1),
    .Depth(NumOutstanding),
    .NeverClears(1'b1),
    .Secure(1'b0)
  ) u_prim_fifo_ds_rsp_store (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(downstream_rvalid_i),
    .wready_o(), // Not connected as OBI is not configured to use rready
    .wdata_i (downstream_rsp_in),
    .rvalid_o(downstream_rsp_out_valid),
    .rready_i(downstream_rsp_out_ready),
    .rdata_o (downstream_rsp_out),
    .full_o  (),
    .depth_o (),
    .err_o   ()
  );

  assign downstream_rsp_in = '{
    data: downstream_rdata_i,
    intg: downstream_rdata_intg_i,
    tag:  downstream_tag_i,
    err:  downstream_err_i
  };


  ////////////////////////////////
  // Bitmap Address Calculation //
  ////////////////////////////////

  // Exponent is expanded (page 70, CHERIoT Architecture specification, Version 1.0)
  assign cap_meta = '{
    base:     downstream_rsp_out.data[8:0],
    exponent: downstream_rsp_out.data[21:18] != 4'hf ? {1'b0, downstream_rsp_out.data[21:18]} :
                                                       5'd24,
    otype:    downstream_rsp_out.data[24:22],
    cperms:   downstream_rsp_out.data[30:25]
  };

  // Not all fields are used
  assign unused_cap_meta = ^{cap_meta.otype, cap_meta.cperms[5]};

  // Check if cap is sealing cap
  assign is_sealing_cap = (cap_meta.cperms[4:3] == 2'b00) && (|cap_meta.cperms[2:0]);

  // Extract the middle field from the pointer, bounds depend on exponent, width fixed
  assign addr_mid = ptr_store_q[cap_meta.exponent +: ibex_cheriot_pkg::BOT_W];

  // Fetch the correction values, we are only interested in the base correction value (1 bit)
  // top-related inputs are set to zero, top-related outputs ignored
  assign cap_correction = ibex_cheriot_pkg::update_temp_fields('0, cap_meta.base, addr_mid);

  // Calculate the base address of the capability as a 33-bit value
  assign cap_base_33 = ibex_cheriot_pkg::get_bound33(cap_meta.base, {2{cap_correction[0]}},
                                                     cap_meta.exponent, ptr_store_q);

  // We don't need the correction bits corresponding to the top address
  assign unused_cap_correction = ^cap_correction[2:1];

  // The MSB is unused in our case
  assign {unused_cap_base_33, cap_base} = cap_base_33;

  // Address in the revocation bitmap
  assign revbm_cap_addr = cap_base - heap_base_addr_i;

  // Bit address in the revocation bitmap (every bit corresponds to one 64-bit capability)
  assign revbm_bit_addr = revbm_cap_addr >> 32'd3;

  // Word address of the revocation bitmap
  assign revbm_addr = revbm_bit_addr[RevBitmapAddrWidth+5-1:5];

  // Bit select
  assign revbm_bit_select = revbm_bit_addr[4:0];

  // Capability base is outside of the bitmap range
  assign revbm_out_of_range = |(revbm_bit_addr[31:RevBitmapAddrWidth+5]);


  //////////////////////
  // Bitmap Interface //
  //////////////////////

  // We have loaded valid capability pointer, now we see valid metadata, not a sealing cap,
  // and are pointing into the revocation bitmap
  assign revbm_req_required = !is_sealing_cap          && // Not sealing cap
                              ptr_store_valid_q        && // The base pointer stored is valid
                              downstream_rsp_out.tag   && // We are looking at a capability
                              downstream_rsp_out_valid && // The stored response is valid
                              align_out                && // We are on the second word of the cap
                              align_out_valid          && // The alignment store is valid
                              !revbm_out_of_range;        // We hit the heap range

  // Assemble read-only request
  assign revbm_req_o  = revbm_req_required && !revbm_outstanding_q;
  assign revbm_addr_o = RevBitmapBaseAddr + {{32 - RevBitmapAddrWidth{1'b0}}, revbm_addr};

  // Is the current capability marked as revoked?
  assign revbm_revoked = revbm_rdata_i[revbm_bit_select] || revbm_err_i;

  // Did we receive a device error?
  assign revbm_device_error_o = revbm_rvalid_i && revbm_err_i;

  // Check the bitmap response data integrity
  prim_secded_inv_39_32_dec u_prim_secded_inv_39_32_dec_bm_rsp_data (
    .data_i    ({revbm_rdata_intg_i, revbm_rdata_i}),
    .data_o    (),
    .syndrome_o(),
    .err_o     (revbm_rsp_data_intg_error)
  );

  // Mask response integrity error if response is not being handshaked
  assign revbm_data_intg_error_o = revbm_rvalid_i && (|revbm_rsp_data_intg_error);

  // One outstanding request
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_rev_req_store
    if(!rst_ni) begin
      revbm_outstanding_q <= 1'b0;
    end else begin
      if (revbm_rvalid_i && revbm_rsp_ready) begin
        revbm_outstanding_q <= 1'b0;
      end else if (revbm_req_o && revbm_gnt_i) begin
        revbm_outstanding_q <= 1'b1;
      end
    end
  end

endmodule
