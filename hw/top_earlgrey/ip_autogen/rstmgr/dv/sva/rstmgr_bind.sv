// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module rstmgr_bind;

  // Each check binds to the partition that has the signals it checks, wherever a top or the
  // block-level testbench instantiates that partition. The cascading and indication checks read the
  // resets of both partitions, so each comes in two parts, one bound to each partition.
`ifndef GATE_LEVEL
  bind rstmgr_part_primary tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (.clk_i, .rst_ni, .h2d(tl_i), .d2h(tl_o));

  // In top-level testbench, do not bind the csr_assert_fpv to reduce simulation time.
`ifndef TOP_LEVEL_DV
  bind rstmgr_part_primary rstmgr_csr_assert_fpv rstmgr_csr_assert (
    .clk_i,
    .rst_ni,
    .h2d(tl_i),
    .d2h(tl_o)
  );
`endif

  bind rstmgr_part_primary rstmgr_attrs_sva_if rstmgr_attrs_sva_if (
    .rst_ni,
    .actual_alert_info_attr(int'(hw2reg.alert_info_attr)),
    .actual_cpu_info_attr(int'(hw2reg.cpu_info_attr)),
    .expected_alert_info_attr(($bits(alert_dump_i) + 31) / 32),
    .expected_cpu_info_attr(($bits(cpu_dump_i) + 31) / 32)
  );

  bind rstmgr_part_secondary pwrmgr_rstmgr_sva_if #(
    .PowerDomains(rstmgr_pkg::PowerDomains)
  ) pwrmgr_rstmgr_sva_if (
    // The reset controllers that answer the power manager run on the POR clock.
    .clk_i(clk_por),
    .rst_ni(rst_ni),
    .clk_slow_i(clk_aon_i),
    .rst_slow_ni(&rst_por_aon_n),
    // These are actually used for checks.
    .rst_lc_req(pwr_i.rst_lc_req),
    .rst_sys_req(pwr_i.rst_sys_req),
    // The inputs from rstmgr.
    .rst_lc_src_n(pwr_o.rst_lc_src_n),
    .rst_sys_src_n(pwr_o.rst_sys_src_n)
  );

  bind rstmgr_part_primary rstmgr_sw_rst_sva_if rstmgr_sw_rst_sva_if (
    .clk_i({
      clk_io_i,
      clk_io_i,
      clk_io_div4_i,
      clk_io_div4_i,
      clk_io_div4_i,
      clk_aon_i,
      clk_usb_i,
      clk_io_i,
      clk_io_i,
      clk_io_div4_i
    }),
    .rst_ni,
    .parent_rst_n(intraip_s2p_i.rst_sys_src_n_main),
    .ctrl_ns(reg2hw.sw_rst_ctrl_n),
    .rst_ens({
      rst_en_o.i3c1 == prim_mubi_pkg::MuBi4True,
      rst_en_o.i3c0 == prim_mubi_pkg::MuBi4True,
      rst_en_o.i2c2 == prim_mubi_pkg::MuBi4True,
      rst_en_o.i2c1 == prim_mubi_pkg::MuBi4True,
      rst_en_o.i2c0 == prim_mubi_pkg::MuBi4True,
      rst_en_o.usb_aon == prim_mubi_pkg::MuBi4True,
      rst_en_o.usb == prim_mubi_pkg::MuBi4True,
      rst_en_o.spi_host1 == prim_mubi_pkg::MuBi4True,
      rst_en_o.spi_host0 == prim_mubi_pkg::MuBi4True,
      rst_en_o.spi_device == prim_mubi_pkg::MuBi4True
    }),
    .rst_ns({
      resets_o.rst_i3c1_n,
      resets_o.rst_i3c0_n,
      resets_o.rst_i2c2_n,
      resets_o.rst_i2c1_n,
      resets_o.rst_i2c0_n,
      resets_o.rst_usb_aon_n,
      resets_o.rst_usb_n,
      resets_o.rst_spi_host1_n,
      resets_o.rst_spi_host0_n,
      resets_o.rst_spi_device_n
    })
  );

  // The primary partition's scan signals come from the secondary partition.
  bind rstmgr_part_primary rstmgr_cascading_primary_sva_if rstmgr_cascading_primary_sva_if (
    .clk_aon_i,
    .clk_io_div4_i,
    .clk_main_i,
    .clk_io_i,
    .clk_usb_i,
    .scan_rst_ni(scan_rst_n),
    .scanmode_i(intraip_s2p_i.scanmode),
    .intraip_s2p_i,
    .resets_o
  );

  // The secondary partition's clocks other than the always-on one come from the primary partition.
  bind rstmgr_part_secondary rstmgr_cascading_secondary_sva_if rstmgr_cascading_secondary_sva_if (
    .clk_i(intraip_p2s_i.clk),
    .clk_aon_i,
    .clk_io_div4_i(intraip_p2s_i.clk_io_div4),
    .por_n_i,
    .pwr_i,
    .pwr_o,
    .scan_rst_ni,
    .scanmode_i,
    .resets_secondary_o,
    .rst_por_aon_n
  );

  bind rstmgr_part_primary rstmgr_rst_en_track_primary_sva_if rstmgr_rst_en_track_primary_sva_if (
    .clk_aon_i,
    .clk_io_div4_i,
    .clk_main_i,
    .clk_io_i,
    .clk_usb_i,
    .rst_por_ni,
    .resets_o,
    .rst_en_o
  );

  bind rstmgr_part_secondary rstmgr_rst_en_track_secondary_sva_if
      rstmgr_rst_en_track_secondary_sva_if (
    .clk_aon_i,
    .clk_io_div4_i(intraip_p2s_i.clk_io_div4),
    .rst_por_ni,
    .resets_secondary_o,
    .intraip_s2p_o
  );

`endif
endmodule
