// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module clkmgr_bind;

  // Everything that these assertions check is in the primary partition of the clkmgr. So the
  // assertions bind to clkmgr_part_primary, wherever a top or the block-level testbench
  // instantiates it. They see the power manager's requests and the statuses in the intra-IP
  // structs, and the clocks it outputs (clocks_o).
`ifndef GATE_LEVEL
  bind clkmgr_part_primary tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (.clk_i, .rst_ni, .h2d(tl_i), .d2h(tl_o));

  // In top-level testbench, do not bind the csr_assert_fpv to reduce simulation time.
`ifndef TOP_LEVEL_DV
  bind clkmgr_part_primary clkmgr_csr_assert_fpv clkmgr_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d(tl_i),
    .d2h(tl_o)
  );
`endif

  bind clkmgr_part_primary clkmgr_pwrmgr_sva_if #(.IS_USB(0)) clkmgr_pwrmgr_main_sva_if (
    .clk_i,
    .rst_ni,
    .clk_en(intraip_s2p_i.main_ip_clk_en),
    .status(intraip_p2s_o.main_status)
  );

  bind clkmgr_part_primary clkmgr_pwrmgr_sva_if #(.IS_USB(0)) clkmgr_pwrmgr_io_sva_if (
    .clk_i,
    .rst_ni,
    .clk_en(intraip_s2p_i.io_ip_clk_en),
    .status(intraip_p2s_o.io_status)
  );

  bind clkmgr_part_primary clkmgr_pwrmgr_sva_if #(.IS_USB(1)) clkmgr_pwrmgr_usb_sva_if (
    .clk_i,
    .rst_ni,
    .clk_en(intraip_s2p_i.usb_ip_clk_en),
    .status(intraip_p2s_o.usb_status)
  );

  bind clkmgr_part_primary clkmgr_gated_clock_sva_if clkmgr_io_div4_peri_sva_if (
    .clk(clocks_o.clk_io_div4_powerup),
    .rst_n(rst_io_div4_ni),
    .ip_clk_en(intraip_s2p_i.io_ip_clk_en),
    .sw_clk_en(clk_io_div4_peri_sw_en),
    .scanmode(intraip_s2p_i.scanmode == prim_mubi_pkg::MuBi4True),
    .gated_clk(clocks_o.clk_io_div4_peri)
  );

  bind clkmgr_part_primary clkmgr_gated_clock_sva_if clkmgr_io_peri_sva_if (
    .clk(clocks_o.clk_io_powerup),
    .rst_n(rst_io_ni),
    .ip_clk_en(intraip_s2p_i.io_ip_clk_en),
    .sw_clk_en(clk_io_peri_sw_en),
    .scanmode(intraip_s2p_i.scanmode == prim_mubi_pkg::MuBi4True),
    .gated_clk(clocks_o.clk_io_peri)
  );

  bind clkmgr_part_primary clkmgr_gated_clock_sva_if clkmgr_usb_peri_sva_if (
    .clk(clocks_o.clk_usb_powerup),
    .rst_n(rst_usb_ni),
    .ip_clk_en(intraip_s2p_i.usb_ip_clk_en),
    .sw_clk_en(clk_usb_peri_sw_en),
    .scanmode(intraip_s2p_i.scanmode == prim_mubi_pkg::MuBi4True),
    .gated_clk(clocks_o.clk_usb_peri)
  );

  bind clkmgr_part_primary clkmgr_gated_clock_sva_if clkmgr_io_spi_host1_sva_if (
    .clk(clocks_o.clk_io_powerup),
    .rst_n(rst_io_ni),
    .ip_clk_en(intraip_s2p_i.io_ip_clk_en),
    .sw_clk_en(clk_io_spi_host1_sw_en),
    .scanmode(intraip_s2p_i.scanmode == prim_mubi_pkg::MuBi4True),
    .gated_clk(clocks_o.clk_io_spi_host1)
  );

  // Assertions for transactional clocks.
  bind clkmgr_part_primary clkmgr_trans_sva_if clkmgr_aes_trans_sva_if (
    .clk(clk_main_i),
    .rst_n(rst_main_ni),
    // A single hint makes each hint register a single field.
    .hint(reg2hw.clk_hints.clk_main_aes_hint.q),
    .idle(idle_i[clkmgr_pkg::HintMainAes] == prim_mubi_pkg::MuBi4True),
    .scanmode(intraip_s2p_i.scanmode == prim_mubi_pkg::MuBi4True),
    .status(hw2reg.clk_hints_status.clk_main_aes_val.d),
    .trans_clk(clocks_o.clk_main_aes)
  );

  bind clkmgr_part_primary clkmgr_trans_sva_if clkmgr_hmac_trans_sva_if (
    .clk(clk_main_i),
    .rst_n(rst_main_ni),
    // A single hint makes each hint register a single field.
    .hint(reg2hw.clk_hints.clk_main_hmac_hint.q),
    .idle(idle_i[clkmgr_pkg::HintMainHmac] == prim_mubi_pkg::MuBi4True),
    .scanmode(intraip_s2p_i.scanmode == prim_mubi_pkg::MuBi4True),
    .status(hw2reg.clk_hints_status.clk_main_hmac_val.d),
    .trans_clk(clocks_o.clk_main_hmac)
  );

  bind clkmgr_part_primary clkmgr_trans_sva_if clkmgr_kmac_trans_sva_if (
    .clk(clk_main_i),
    .rst_n(rst_main_ni),
    // A single hint makes each hint register a single field.
    .hint(reg2hw.clk_hints.clk_main_kmac_hint.q),
    .idle(idle_i[clkmgr_pkg::HintMainKmac] == prim_mubi_pkg::MuBi4True),
    .scanmode(intraip_s2p_i.scanmode == prim_mubi_pkg::MuBi4True),
    .status(hw2reg.clk_hints_status.clk_main_kmac_val.d),
    .trans_clk(clocks_o.clk_main_kmac)
  );

  bind clkmgr_part_primary clkmgr_trans_sva_if clkmgr_otbn_trans_sva_if (
    .clk(clk_main_i),
    .rst_n(rst_main_ni),
    // A single hint makes each hint register a single field.
    .hint(reg2hw.clk_hints.clk_main_otbn_hint.q),
    .idle(idle_i[clkmgr_pkg::HintMainOtbn] == prim_mubi_pkg::MuBi4True),
    .scanmode(intraip_s2p_i.scanmode == prim_mubi_pkg::MuBi4True),
    .status(hw2reg.clk_hints_status.clk_main_otbn_val.d),
    .trans_clk(clocks_o.clk_main_otbn)
  );

  bind clkmgr_part_primary clkmgr_extclk_sva_if clkmgr_extclk_sva_if (
    .clk_i,
    .rst_ni,
    .extclk_ctrl_sel(extclk_ctrl_sel),
    .extclk_ctrl_hi_speed_sel(extclk_ctrl_hi_speed_sel),
    .lc_hw_debug_en_i,
    .lc_clk_byp_req_i,
    .io_clk_byp_req_o,
    .all_clk_byp_req_o,
    .hi_speed_sel_o
  );

  bind clkmgr_part_primary clkmgr_div_sva_if #(
    .DIV(4)
  ) clkmgr_div4_sva_if (
    .clk(clocks_o.clk_io_powerup),
    .rst_n(rst_ni),
    .maybe_divided_clk(clocks_o.clk_io_div4_powerup),
    .div_step_down_req_i(div_step_down_req_i == prim_mubi_pkg::MuBi4True),
    .scanmode(intraip_s2p_i.scanmode == prim_mubi_pkg::MuBi4True)
  );

  // AON clock gating enables.
  bind clkmgr_part_primary clkmgr_aon_cg_en_sva_if clkmgr_aon_cg_aon_gated_peri (
    .cg_en(cg_en_o.aon_gated_peri == prim_mubi_pkg::MuBi4True)
  );

  bind clkmgr_part_primary clkmgr_aon_cg_en_sva_if clkmgr_aon_cg_aon_gated_powerup (
    .cg_en(cg_en_o.aon_gated_powerup == prim_mubi_pkg::MuBi4True)
  );

  bind clkmgr_part_primary clkmgr_aon_cg_en_sva_if clkmgr_aon_cg_aon_peri (
    .cg_en(cg_en_o.aon_peri == prim_mubi_pkg::MuBi4True)
  );

  bind clkmgr_part_primary clkmgr_aon_cg_en_sva_if clkmgr_aon_cg_aon_powerup (
    .cg_en(cg_en_o.aon_powerup == prim_mubi_pkg::MuBi4True)
  );

  bind clkmgr_part_primary clkmgr_aon_cg_en_sva_if clkmgr_aon_cg_aon_secure (
    .cg_en(cg_en_o.aon_secure == prim_mubi_pkg::MuBi4True)
  );

  bind clkmgr_part_primary clkmgr_aon_cg_en_sva_if clkmgr_aon_cg_aon_timers (
    .cg_en(cg_en_o.aon_timers == prim_mubi_pkg::MuBi4True)
  );

  bind clkmgr_part_primary clkmgr_aon_cg_en_sva_if clkmgr_aon_cg_io_div4_powerup (
    .cg_en(cg_en_o.io_div4_powerup == prim_mubi_pkg::MuBi4True)
  );

  bind clkmgr_part_primary clkmgr_aon_cg_en_sva_if clkmgr_aon_cg_io_powerup (
    .cg_en(cg_en_o.io_powerup == prim_mubi_pkg::MuBi4True)
  );

  bind clkmgr_part_primary clkmgr_aon_cg_en_sva_if clkmgr_aon_cg_main_powerup (
    .cg_en(cg_en_o.main_powerup == prim_mubi_pkg::MuBi4True)
  );

  bind clkmgr_part_primary clkmgr_aon_cg_en_sva_if clkmgr_aon_cg_usb_powerup (
    .cg_en(cg_en_o.usb_powerup == prim_mubi_pkg::MuBi4True)
  );

  // Non-AON clock gating enables with no software control.
  bind clkmgr_part_primary clkmgr_cg_en_sva_if clkmgr_cg_io_div4_infra (
    .clk(clk_io_div4),
    .rst_n(rst_io_div4_ni),
    .ip_clk_en(clk_io_div4_en),
    .sw_clk_en(1'b1),
    .scanmode(prim_mubi_pkg::MuBi4False),
    .cg_en(cg_en_o.io_div4_infra == prim_mubi_pkg::MuBi4True)
  );

  bind clkmgr_part_primary clkmgr_cg_en_sva_if clkmgr_cg_io_div4_secure (
    .clk(clk_io_div4),
    .rst_n(rst_io_div4_ni),
    .ip_clk_en(clk_io_div4_en),
    .sw_clk_en(1'b1),
    .scanmode(prim_mubi_pkg::MuBi4False),
    .cg_en(cg_en_o.io_div4_secure == prim_mubi_pkg::MuBi4True)
  );

  bind clkmgr_part_primary clkmgr_cg_en_sva_if clkmgr_cg_io_div4_timers (
    .clk(clk_io_div4),
    .rst_n(rst_io_div4_ni),
    .ip_clk_en(clk_io_div4_en),
    .sw_clk_en(1'b1),
    .scanmode(prim_mubi_pkg::MuBi4False),
    .cg_en(cg_en_o.io_div4_timers == prim_mubi_pkg::MuBi4True)
  );

  bind clkmgr_part_primary clkmgr_cg_en_sva_if clkmgr_cg_io_infra (
    .clk(clk_io),
    .rst_n(rst_io_ni),
    .ip_clk_en(clk_io_en),
    .sw_clk_en(1'b1),
    .scanmode(prim_mubi_pkg::MuBi4False),
    .cg_en(cg_en_o.io_infra == prim_mubi_pkg::MuBi4True)
  );

  bind clkmgr_part_primary clkmgr_cg_en_sva_if clkmgr_cg_main_infra (
    .clk(clk_main),
    .rst_n(rst_main_ni),
    .ip_clk_en(clk_main_en),
    .sw_clk_en(1'b1),
    .scanmode(prim_mubi_pkg::MuBi4False),
    .cg_en(cg_en_o.main_infra == prim_mubi_pkg::MuBi4True)
  );

  bind clkmgr_part_primary clkmgr_cg_en_sva_if clkmgr_cg_main_secure (
    .clk(clk_main),
    .rst_n(rst_main_ni),
    .ip_clk_en(clk_main_en),
    .sw_clk_en(1'b1),
    .scanmode(prim_mubi_pkg::MuBi4False),
    .cg_en(cg_en_o.main_secure == prim_mubi_pkg::MuBi4True)
  );

  bind clkmgr_part_primary clkmgr_cg_en_sva_if clkmgr_cg_usb_infra (
    .clk(clk_usb),
    .rst_n(rst_usb_ni),
    .ip_clk_en(clk_usb_en),
    .sw_clk_en(1'b1),
    .scanmode(prim_mubi_pkg::MuBi4False),
    .cg_en(cg_en_o.usb_infra == prim_mubi_pkg::MuBi4True)
  );

  // Software controlled gating enables.
  bind clkmgr_part_primary clkmgr_cg_en_sva_if clkmgr_cg_io_div4_peri (
    .clk(clk_io_div4),
    .rst_n(rst_io_div4_ni),
    .ip_clk_en(clk_io_div4_en),
    .sw_clk_en(clk_io_div4_peri_sw_en),
    .scanmode(prim_mubi_pkg::MuBi4False),
    .cg_en(cg_en_o.io_div4_peri == prim_mubi_pkg::MuBi4True)
  );

  bind clkmgr_part_primary clkmgr_cg_en_sva_if clkmgr_cg_io_peri (
    .clk(clk_io),
    .rst_n(rst_io_ni),
    .ip_clk_en(clk_io_en),
    .sw_clk_en(clk_io_peri_sw_en),
    .scanmode(prim_mubi_pkg::MuBi4False),
    .cg_en(cg_en_o.io_peri == prim_mubi_pkg::MuBi4True)
  );

  bind clkmgr_part_primary clkmgr_cg_en_sva_if clkmgr_cg_usb_peri (
    .clk(clk_usb),
    .rst_n(rst_usb_ni),
    .ip_clk_en(clk_usb_en),
    .sw_clk_en(clk_usb_peri_sw_en),
    .scanmode(prim_mubi_pkg::MuBi4False),
    .cg_en(cg_en_o.usb_peri == prim_mubi_pkg::MuBi4True)
  );

  bind clkmgr_part_primary clkmgr_cg_en_sva_if clkmgr_cg_io_spi_host1 (
    .clk(clk_io),
    .rst_n(rst_io_ni),
    .ip_clk_en(clk_io_en),
    .sw_clk_en(clk_io_spi_host1_sw_en),
    .scanmode(prim_mubi_pkg::MuBi4False),
    .cg_en(cg_en_o.io_spi_host1 == prim_mubi_pkg::MuBi4True)
  );

  // Hint controlled gating enables.
  bind clkmgr_part_primary clkmgr_cg_en_sva_if clkmgr_cg_main_aes (
    .clk(clk_main_i),
    .rst_n(rst_main_ni),
    .ip_clk_en(clk_main_en),
    .sw_clk_en(u_clk_main_aes_trans.sw_hint_synced || !u_clk_main_aes_trans.idle_valid),
    .scanmode(prim_mubi_pkg::MuBi4False),
    .cg_en(cg_en_o.main_aes == prim_mubi_pkg::MuBi4True)
  );

  bind clkmgr_part_primary clkmgr_cg_en_sva_if clkmgr_cg_main_hmac (
    .clk(clk_main_i),
    .rst_n(rst_main_ni),
    .ip_clk_en(clk_main_en),
    .sw_clk_en(u_clk_main_hmac_trans.sw_hint_synced || !u_clk_main_hmac_trans.idle_valid),
    .scanmode(prim_mubi_pkg::MuBi4False),
    .cg_en(cg_en_o.main_hmac == prim_mubi_pkg::MuBi4True)
  );

  bind clkmgr_part_primary clkmgr_cg_en_sva_if clkmgr_cg_main_kmac (
    .clk(clk_main_i),
    .rst_n(rst_main_ni),
    .ip_clk_en(clk_main_en),
    .sw_clk_en(u_clk_main_kmac_trans.sw_hint_synced || !u_clk_main_kmac_trans.idle_valid),
    .scanmode(prim_mubi_pkg::MuBi4False),
    .cg_en(cg_en_o.main_kmac == prim_mubi_pkg::MuBi4True)
  );

  bind clkmgr_part_primary clkmgr_cg_en_sva_if clkmgr_cg_main_otbn (
    .clk(clk_main_i),
    .rst_n(rst_main_ni),
    .ip_clk_en(clk_main_en),
    .sw_clk_en(u_clk_main_otbn_trans.sw_hint_synced || !u_clk_main_otbn_trans.idle_valid),
    .scanmode(prim_mubi_pkg::MuBi4False),
    .cg_en(cg_en_o.main_otbn == prim_mubi_pkg::MuBi4True)
  );

  // Calibration assertions.
  bind clkmgr_part_primary clkmgr_lost_calib_regwen_sva_if clkmgr_lost_calib_regwen_sva_if (
    .clk(clk_i),
    .rst_n(rst_ni),
    .calib_rdy(calib_rdy_i),
    .meas_ctrl_regwen(u_reg.measure_ctrl_regwen_qs)
  );

  bind clkmgr_part_primary clkmgr_lost_calib_ctrl_en_sva_if
    clkmgr_lost_calib_io_ctrl_en_sva_if (
    .clk(clk_i),
    .rst_n(rst_ni),
    .calib_rdy(calib_rdy_i),
    .meas_ctrl_en(u_reg.io_meas_ctrl_en_qs)
  );

  bind clkmgr_part_primary clkmgr_lost_calib_ctrl_en_sva_if
    clkmgr_lost_calib_io_div4_ctrl_en_sva_if (
    .clk(clk_i),
    .rst_n(rst_ni),
    .calib_rdy(calib_rdy_i),
    .meas_ctrl_en(u_reg.io_div4_meas_ctrl_en_qs)
  );

  bind clkmgr_part_primary clkmgr_lost_calib_ctrl_en_sva_if
    clkmgr_lost_calib_main_ctrl_en_sva_if (
    .clk(clk_i),
    .rst_n(rst_ni),
    .calib_rdy(calib_rdy_i),
    .meas_ctrl_en(u_reg.main_meas_ctrl_en_qs)
  );

  bind clkmgr_part_primary clkmgr_lost_calib_ctrl_en_sva_if
    clkmgr_lost_calib_usb_ctrl_en_sva_if (
    .clk(clk_i),
    .rst_n(rst_ni),
    .calib_rdy(calib_rdy_i),
    .meas_ctrl_en(u_reg.usb_meas_ctrl_en_qs)
  );

  bind clkmgr_part_primary clkmgr_sec_cm_checker_assert #(
    .NumDivClks(1)
  ) clkmgr_sec_cm_checker_assert (
    .clk_i,
    .rst_ni,
    .all_clk_byp_req_o,
    .lc_hw_debug_en_i,
    .lc_clk_byp_req_i,
    .lc_clk_byp_ack_o,
    .io_clk_byp_req_o,
    // internal signal is picked due to inconsistent t->f, f->t delay
    .io_clk_byp_ack(u_clkmgr_byp.io_clk_byp_ack),
    // internal signal is picked due to inconsistent input to signal delay
    .step_down_acks_sync(u_clkmgr_byp.step_down_acks_sync),
    .extclk_ctrl_sel(extclk_ctrl_sel)
  );

`endif
endmodule : clkmgr_bind
