// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module cheriot_tbre #(
  parameter type         addr_t              = logic [top_pkg::TL_AW-1:0],
  parameter addr_t       MainSramBaseAddr    = 32'h1000_0000,
  parameter addr_t       MainSramTopAddr     = 32'h1003_0000,
  parameter addr_t       NvmBaseAddr         = 32'h3000_0000,
  parameter addr_t       NvmTopAddr          = 32'h3020_0000,
  parameter addr_t       MetaMainSramTagBase = 32'h1100_8C00,
  parameter addr_t       MetaNvmTagBase      = 32'h1100_0C00,
  parameter int unsigned RevBitmapSizeBytes  = 32'd3072,
  parameter addr_t       RevBitmapBaseAddr   = 32'h1100_0000,
  // Words in flight and core writes watched at once, see cheriot_tbre_mover
  parameter int unsigned MaxInflight         = 32'd2,
  parameter int unsigned NumSnoop            = 32'd1
) (
  input  logic clk_i,
  input  logic rst_ni,

  input  prim_mubi_pkg::mubi4_t cheriot_ena_i,

  // Sweep request
  input  addr_t start_addr_i,
  input  addr_t num_words_i,
  input  logic  valid_i,
  output logic  ready_o,
  output logic  busy_o,

  // Core writes the engine watches
  input  logic  [NumSnoop-1:0] snoop_valid_i,
  input  addr_t [NumSnoop-1:0] snoop_addr_i,

  // Tag clear presented towards the tag filter, until its handshake
  output logic  clear_valid_o,
  output logic  clear_done_o,
  output addr_t clear_addr_o,

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
  output logic mover_read_err_o,
  output logic mover_err_o,
  output logic revbm_data_intg_error_o,
  output logic revbm_rsp_intg_error_o,
  output logic revbm_device_error_o
);

  /////////////
  // Signals //
  /////////////

  // The TRVK filter only sees the reads: the socket merges its downstream port and the mover's
  // write port in front of the tag filter, so no clear answer passes between the two words of a
  // capability it looks at.
  tlul_pkg::tl_h2d_t sock_tl_h2d[2];
  tlul_pkg::tl_d2h_t sock_tl_d2h[2];
  logic              sock_tag_h2d[2];
  logic              sock_tag_d2h[2];
  logic [4:0]        sock_bit_sel[2];

  tlul_pkg::tl_h2d_t mover_r_tl_h2d;
  tlul_pkg::tl_d2h_t mover_r_tl_d2h;
  logic              mover_r_tag_d2h;

  tlul_pkg::tl_h2d_t filter_tl_h2d;
  logic              filter_tag_h2d;
  tlul_pkg::tl_d2h_t filter_tl_d2h;
  logic              filter_tag_d2h;

  logic unused_sock_w_tag_d2h;

  ///////////
  // Mover //
  ///////////

  cheriot_tbre_mover #(
    .addr_t     (addr_t),
    .MaxInflight(MaxInflight),
    .NumSnoop   (NumSnoop)
  ) u_cheriot_tbre_mover (
    .clk_i,
    .rst_ni,
    .start_addr_i,
    .num_words_i,
    .valid_i,
    .ready_o,
    .busy_o,
    .tl_r_o (mover_r_tl_h2d),
    .r_tag_i(mover_r_tag_d2h),
    .tl_r_i (mover_r_tl_d2h),
    .w_tag_o(sock_tag_h2d[1]),
    .tl_w_o (sock_tl_h2d[1]),
    .tl_w_i (sock_tl_d2h[1]),
    .snoop_valid_i,
    .snoop_addr_i,
    .clear_valid_o,
    .clear_done_o,
    .clear_addr_o,
    .read_err_o(mover_read_err_o),
    .err_o     (mover_err_o)
  );

  /////////////////
  // TRVK Filter //
  /////////////////

  // Every read is hinted as a capability load, so the tag filter looks up its tag. The revocation
  // bitmap covers the main SRAM region.
  cheriot_trvk_tlul #(
    .NumOutstanding    (MaxInflight),
    .RevBitmapSizeBytes(RevBitmapSizeBytes),
    .RevBitmapBaseAddr (RevBitmapBaseAddr)
  ) u_cheriot_trvk_tlul (
    .clk_i,
    .rst_ni,
    .heap_base_addr_i(MainSramBaseAddr),
    .upstream_tl_i   (mover_r_tl_h2d),
    .upstream_tag_i  (1'b1),
    .upstream_tl_o   (mover_r_tl_d2h),
    .upstream_tag_o  (mover_r_tag_d2h),
    .downstream_tl_o (sock_tl_h2d[0]),
    .downstream_tag_o(sock_tag_h2d[0]),
    .downstream_tl_i (sock_tl_d2h[0]),
    .downstream_tag_i(sock_tag_d2h[0]),
    .revbm_tl_o,
    .revbm_tl_i,
    .revbm_data_intg_error_o,
    .revbm_rsp_intg_error_o,
    .revbm_device_error_o
  );

  ////////////
  // Socket //
  ////////////

  assign sock_bit_sel = '{default: '0};

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
    .tl_h_i     (sock_tl_h2d),
    .tag_h_i    (sock_tag_h2d),
    .bit_sel_h_i(sock_bit_sel),
    .tl_h_o     (sock_tl_d2h),
    .tag_h_o    (sock_tag_d2h),
    .tl_d_o     (filter_tl_h2d),
    .tag_d_o    (filter_tag_h2d),
    .bit_sel_d_o(),
    .tl_d_i     (filter_tl_d2h),
    .tag_d_i    (filter_tag_d2h)
  );

  assign unused_sock_w_tag_d2h = sock_tag_d2h[1];

  ////////////////
  // Tag Filter //
  ////////////////

  cheriot_tag_filter #(
    .NumOutstanding     (MaxInflight),
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
    .tl_d_i (filter_tl_h2d),
    .tag_d_i(filter_tag_h2d),
    .tl_d_o (filter_tl_d2h),
    .tag_d_o(filter_tag_d2h),
    .tl_m_o,
    .tag_m_o,
    .bit_sel_m_o,
    .tl_m_i,
    .tag_m_i,
    .tl_h_o,
    .tl_h_i,
    .wtrc_err_o()
  );

endmodule
