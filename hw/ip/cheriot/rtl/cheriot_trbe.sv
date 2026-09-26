// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module cheriot_trbe #(
  parameter type         addr_t              = logic [top_pkg::TL_AW-1:0],
  parameter addr_t       MainSramBaseAddr    = 'h1000_0000,
  parameter addr_t       MainSramTopAddr     = 'h1003_0000,
  parameter addr_t       NvmBaseAddr         = 'h3000_0000,
  parameter addr_t       NvmTopAddr          = 'h3020_0000,
  parameter addr_t       MetaMainSramTagBase = 'h1100_8C00,
  parameter addr_t       MetaNvmTagBase      = 'h1100_0C00,
  parameter int unsigned RevBitmapAddrWidth  = 32'd12,
  parameter int unsigned RevBitmapSizeBytes  = 32'd3072,
  parameter int unsigned RevBitmapBaseAddr   = 32'h1100_0000,
  parameter bit          MemECC              = 1'b1
)(
  input  logic clk_i,
  input  logic rst_ni,

  input  prim_mubi_pkg::mubi4_t cheriot_ena_i,
  input  logic [31:0]           heap_base_addr_i,

  // Copy port
  input  addr_t start_addr_i,
  input  addr_t num_words_i,
  input  logic  valid_i,
  output logic  ready_o,
  output logic  busy_o,

  // Revocation bitmap port
  output tlul_pkg::tl_h2d_t revbm_tl_o,
  input  tlul_pkg::tl_d2h_t revbm_tl_i,

  // Meta port
  output tlul_pkg::tl_h2d_t tl_m_o,
  output logic              tag_m_o,
  output logic [4:0]        bit_sel_m_o,
  input  tlul_pkg::tl_d2h_t tl_m_i,
  input  logic              tag_m_i,

  // Host port
  output tlul_pkg::tl_h2d_t tl_h_o,
  input  tlul_pkg::tl_d2h_t tl_h_i,

  // Errors
  output logic mover_err_o,
  output logic revbm_data_intg_error_o,
  output logic revbm_rsp_intg_error_o,
  output logic revbm_device_error_o
);

  tlul_pkg::tl_h2d_t mover_tl_h2d [2];
  tlul_pkg::tl_d2h_t mover_tl_d2h [2];
  logic              mover_tag_h2d [2];
  logic              mover_tag_d2h [2];
  logic [4:0]        mover_bit_sel [2];

  tlul_pkg::tl_h2d_t trvk_tl_h2d;
  logic              trvk_tag_h2d;
  tlul_pkg::tl_d2h_t trvk_tl_d2h;
  logic              trvk_tag_d2h;

  tlul_pkg::tl_h2d_t filter_tl_h2d;
  logic              filter_tag_h2d;
  tlul_pkg::tl_d2h_t filter_tl_d2h;
  logic              filter_tag_d2h;

  logic unused_mover_w_tag_d2h;

  cheriot_trbe_mover #(
    .addr_t        (addr_t),
    .WaddrFifoDepth(32'd1),
    .MaxInflight   (32'd1)
  ) u_cheriot_trbe_mover (
    .clk_i,
    .rst_ni,
    .start_addr_i,
    .num_words_i,
    .valid_i,
    .ready_o,
    .busy_o,
    .tl_r_o (mover_tl_h2d[0]),
    .r_tag_i(mover_tag_d2h[0]),
    .tl_r_i (mover_tl_d2h[0]),
    .w_tag_o(mover_tag_h2d[1]),
    .tl_w_o (mover_tl_h2d[1]),
    .tl_w_i (mover_tl_d2h[1]),
    .err_o  (mover_err_o)
  );

  // Every read is hinted as a capability load, so the tag filter looks up its tag.
  assign mover_tag_h2d[0] = 1'b1;
  assign mover_bit_sel    = '{default: '0};

  cheriot_socket_m1 #(
    .M        (32'd2),
    .HReqPass ({2{1'b1}}),
    .HRspPass ({2{1'b1}}),
    .HReqDepth('0),
    .HRspDepth('0),
    .DReqPass (1'b1),
    .DRspPass (1'b1),
    .DReqDepth('0),
    .DRspDepth('0)
  ) u_cheriot_socket_m1 (
    .clk_i,
    .rst_ni,
    .tl_h_i     (mover_tl_h2d),
    .tag_h_i    (mover_tag_h2d),
    .bit_sel_h_i(mover_bit_sel),
    .tl_h_o     (mover_tl_d2h),
    .tag_h_o    (mover_tag_d2h),
    .tl_d_o     (trvk_tl_h2d),
    .tag_d_o    (trvk_tag_h2d),
    .bit_sel_d_o(),
    .tl_d_i     (trvk_tl_d2h),
    .tag_d_i    (trvk_tag_d2h)
  );

  assign unused_mover_w_tag_d2h = mover_tag_d2h[1];

  cheriot_trvk_tlul #(
    .NumOutstanding    (32'd1),
    .RevBitmapAddrWidth(RevBitmapAddrWidth),
    .RevBitmapSizeBytes(RevBitmapSizeBytes),
    .RevBitmapBaseAddr (RevBitmapBaseAddr),
    .MemECC            (MemECC)
  ) u_cheriot_trvk_tlul (
    .clk_i,
    .rst_ni,
    .heap_base_addr_i,
    .upstream_tl_i    (trvk_tl_h2d),
    .upstream_tag_i   (trvk_tag_h2d),
    .upstream_tl_o    (trvk_tl_d2h),
    .upstream_tag_o   (trvk_tag_d2h),
    .downstream_tl_o  (filter_tl_h2d),
    .downstream_tag_o (filter_tag_h2d),
    .downstream_tl_i  (filter_tl_d2h),
    .downstream_tag_i (filter_tag_d2h),
    .revbm_tl_o,
    .revbm_tl_i,
    .revbm_data_intg_error_o,
    .revbm_rsp_intg_error_o,
    .revbm_device_error_o
  );

  cheriot_tag_filter #(
    .NumOutstanding     (32'd1),
    .addr_t             (addr_t),
    .MainSramBaseAddr   (MainSramBaseAddr),
    .MainSramTopAddr    (MainSramTopAddr),
    .NvmBaseAddr        (NvmBaseAddr),
    .NvmTopAddr         (NvmTopAddr),
    .MetaMainSramTagBase(MetaMainSramTagBase),
    .MetaNvmTagBase     (MetaNvmTagBase),
    .TagOnlyWrites      (1'b1)
  ) u_cheriot_tag_filter (
    .clk_i,
    .rst_ni,
    .cheriot_ena_i,
    .tl_d_i     (filter_tl_h2d),
    .tag_d_i    (filter_tag_h2d),
    .tl_d_o     (filter_tl_d2h),
    .tag_d_o    (filter_tag_d2h),
    .tl_m_o,
    .tag_m_o,
    .bit_sel_m_o,
    .tl_m_i,
    .tag_m_i,
    .tl_h_o,
    .tl_h_i
  );

endmodule
