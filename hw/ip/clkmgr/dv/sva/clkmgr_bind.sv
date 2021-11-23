// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module clkmgr_bind;

  bind clkmgr tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (.clk_i, .rst_ni, .h2d(tl_i), .d2h(tl_o));

  bind clkmgr clkmgr_csr_assert_fpv clkmgr_csr_assert (.clk_i, .rst_ni, .h2d(tl_i), .d2h(tl_o));

  bind clkmgr clkmgr_pwrmgr_sva_if clkmgr_pwrmgr_sva_if (
    .clk_i,
    .rst_ni,
    .io_clk_en(pwr_i.io_ip_clk_en),
    .io_status(pwr_o.io_status),
    .main_clk_en(pwr_i.main_ip_clk_en),
    .main_status(pwr_o.main_status),
    .usb_clk_en(pwr_i.usb_ip_clk_en),
    .usb_status(pwr_o.usb_status)
  );

  bind clkmgr clkmgr_gated_clock_sva_if clkmgr_io_div4_peri_sva_if (
    .clk(clocks_o.clk_io_div4_powerup),
    .rst_n(rst_io_div4_ni),
    .ip_clk_en(pwr_i.io_ip_clk_en),
    .sw_clk_en(reg2hw.clk_enables.clk_io_div4_peri_en.q),
    .scanmode(scanmode_i == lc_ctrl_pkg::On),
    .gated_clk(clocks_o.clk_io_div4_peri)
  );

  bind clkmgr clkmgr_gated_clock_sva_if clkmgr_io_div2_peri_sva_if (
    .clk(clocks_o.clk_io_div2_powerup),
    .rst_n(rst_io_div2_ni),
    .ip_clk_en(pwr_i.io_ip_clk_en),
    .sw_clk_en(reg2hw.clk_enables.clk_io_div2_peri_en.q),
    .scanmode(scanmode_i == lc_ctrl_pkg::On),
    .gated_clk(clocks_o.clk_io_div2_peri)
  );

  bind clkmgr clkmgr_gated_clock_sva_if clkmgr_io_peri_sva_if (
    .clk(clocks_o.clk_io_powerup),
    .rst_n(rst_io_ni),
    .ip_clk_en(pwr_i.io_ip_clk_en),
    .sw_clk_en(reg2hw.clk_enables.clk_io_peri_en.q),
    .scanmode(scanmode_i == lc_ctrl_pkg::On),
    .gated_clk(clocks_o.clk_io_peri)
  );

  bind clkmgr clkmgr_gated_clock_sva_if clkmgr_usb_peri_sva_if (
    .clk(clocks_o.clk_usb_powerup),
    .rst_n(rst_usb_ni),
    .ip_clk_en(pwr_i.usb_ip_clk_en),
    .sw_clk_en(reg2hw.clk_enables.clk_usb_peri_en.q),
    .scanmode(scanmode_i == lc_ctrl_pkg::On),
    .gated_clk(clocks_o.clk_usb_peri)
  );

  bind clkmgr clkmgr_gated_clock_sva_if clkmgr_aes_hintable_sva_if (
    .clk(clocks_o.clk_main_powerup),
    .rst_n(rst_main_ni),
    .ip_clk_en(pwr_i.main_ip_clk_en),
    .sw_clk_en(reg2hw.clk_hints.clk_main_aes_hint.q || !idle_i[0]),
    .scanmode(scanmode_i == lc_ctrl_pkg::On),
    .gated_clk(clocks_o.clk_main_aes)
  );

  bind clkmgr clkmgr_gated_clock_sva_if clkmgr_hmac_hintable_sva_if (
    .clk(clocks_o.clk_main_powerup),
    .rst_n(rst_main_ni),
    .ip_clk_en(pwr_i.main_ip_clk_en),
    .sw_clk_en(reg2hw.clk_hints.clk_main_hmac_hint.q || !idle_i[1]),
    .scanmode(scanmode_i == lc_ctrl_pkg::On),
    .gated_clk(clocks_o.clk_main_hmac)
  );

  bind clkmgr clkmgr_gated_clock_sva_if clkmgr_kmac_hintable_sva_if (
    .clk(clocks_o.clk_main_powerup),
    .rst_n(rst_main_ni),
    .ip_clk_en(pwr_i.main_ip_clk_en),
    .sw_clk_en(reg2hw.clk_hints.clk_main_kmac_hint.q || !idle_i[2]),
    .scanmode(scanmode_i == lc_ctrl_pkg::On),
    .gated_clk(clocks_o.clk_main_kmac)
  );

  bind clkmgr clkmgr_gated_clock_sva_if clkmgr_io_div4_otbn_hintable_sva_if (
    .clk(clocks_o.clk_io_div4_powerup),
    .rst_n(rst_io_div4_ni),
    .ip_clk_en(pwr_i.io_ip_clk_en),
    .sw_clk_en(reg2hw.clk_hints.clk_io_div4_otbn_hint.q || !idle_i[3]),
    .scanmode(scanmode_i == lc_ctrl_pkg::On),
    .gated_clk(clocks_o.clk_io_div4_otbn)
  );

  bind clkmgr clkmgr_gated_clock_sva_if clkmgr_otbn_hintable_sva_if (
    .clk(clocks_o.clk_main_powerup),
    .rst_n(rst_main_ni),
    .ip_clk_en(pwr_i.main_ip_clk_en),
    .sw_clk_en(reg2hw.clk_hints.clk_main_otbn_hint.q || !idle_i[4]),
    .scanmode(scanmode_i == lc_ctrl_pkg::On),
    .gated_clk(clocks_o.clk_main_otbn)
  );

  bind clkmgr clkmgr_div_sva_if #(
    .DIV(2)
  ) clkmgr_div2_sva_if (
    .clk(clocks_o.clk_io_powerup),
    .rst_n(rst_ni),
    .maybe_divided_clk(clocks_o.clk_io_div2_powerup),
    .lc_step_down_ctrl(lc_clk_byp_req_i == lc_ctrl_pkg::On),
    .lc_step_down_ack(io_clk_byp_ack_i == prim_mubi_pkg::MuBi4True),
    .sw_step_down_ctrl(lc_hw_debug_en_i == lc_ctrl_pkg::On &&
                       reg2hw.extclk_ctrl.sel.q == prim_mubi_pkg::MuBi4True &&
                       reg2hw.extclk_ctrl.low_speed_sel.q == prim_mubi_pkg::MuBi4True),
    .sw_step_down_ack(all_clk_byp_ack_i == prim_mubi_pkg::MuBi4True),
    .sw_step_up_ack(all_clk_byp_ack_i == prim_mubi_pkg::MuBi4False),
    .scanmode(scanmode_i == lc_ctrl_pkg::On)
  );

  // The div2 clk also steps, so not a good reference. Instead, check it always tracks io_div2.
  bind clkmgr clkmgr_div_sva_if #(
    .DIV(4)
  ) clkmgr_div4_sva_if (
    .clk(clocks_o.clk_io_div2_powerup),
    .rst_n(rst_ni),
    .maybe_divided_clk(clocks_o.clk_io_div4_powerup),
    .lc_step_down_ctrl(lc_clk_byp_req_i == lc_ctrl_pkg::On),
    .lc_step_down_ack(io_clk_byp_ack_i == prim_mubi_pkg::MuBi4True),
    .sw_step_down_ctrl(lc_hw_debug_en_i == lc_ctrl_pkg::On &&
                       reg2hw.extclk_ctrl.sel.q == prim_mubi_pkg::MuBi4True &&
                       reg2hw.extclk_ctrl.low_speed_sel.q == prim_mubi_pkg::MuBi4True),
    .sw_step_down_ack(all_clk_byp_ack_i == prim_mubi_pkg::MuBi4True),
    .sw_step_up_ack(all_clk_byp_ack_i == prim_mubi_pkg::MuBi4False),
    .scanmode(scanmode_i == lc_ctrl_pkg::On)
  );

endmodule
