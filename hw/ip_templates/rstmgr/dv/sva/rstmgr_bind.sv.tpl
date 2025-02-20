// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module rstmgr_bind;
`ifndef GATE_LEVEL
  bind rstmgr tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (.clk_i, .rst_ni, .h2d(tl_i), .d2h(tl_o));

  // In top-level testbench, do not bind the csr_assert_fpv to reduce simulation time.
`ifndef TOP_LEVEL_DV
  bind rstmgr rstmgr_csr_assert_fpv rstmgr_csr_assert (.clk_i, .rst_ni, .h2d(tl_i), .d2h(tl_o));
`endif

  bind rstmgr rstmgr_cascading_sva_if rstmgr_cascading_sva_if (
    .clk_i,
% for clk in sorted(list(clk_freqs.keys())):
    .clk_${clk}_i,
% endfor
    .por_n_i,
    .scan_rst_ni,
    .scanmode_i,
    .resets_o,
    .rst_lc_req(pwr_i.rst_lc_req),
    .rst_sys_req(pwr_i.rst_sys_req),
    .rst_lc_src_n(pwr_o.rst_lc_src_n),
    .rst_sys_src_n(pwr_o.rst_sys_src_n)
  );

  bind rstmgr rstmgr_attrs_sva_if rstmgr_attrs_sva_if (
    .rst_ni,
    .actual_alert_info_attr(int'(hw2reg.alert_info_attr)),
    .actual_cpu_info_attr(int'(hw2reg.cpu_info_attr)),
    .expected_alert_info_attr(($bits(alert_dump_i) + 31) / 32),
    .expected_cpu_info_attr(($bits(cpu_dump_i) + 31) / 32)
  );

  bind rstmgr pwrmgr_rstmgr_sva_if #(
    .PowerDomains(rstmgr_pkg::PowerDomains)
  ) pwrmgr_rstmgr_sva_if (
    .clk_i(clk_i),
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

  bind rstmgr rstmgr_sw_rst_sva_if rstmgr_sw_rst_sva_if (
    .clk_i({
% for clk in list(reversed(sw_rsts.values())):
<% sep = '' if loop.last else ',' %>\
      clk_${clk}_i${sep}
% endfor
    }),
    .rst_ni,
    .parent_rst_n(rst_sys_src_n[1]),
    .ctrl_ns(reg2hw.sw_rst_ctrl_n),
    .rst_ens({
% for device in list(reversed(sw_rsts.keys())):
<% sep = '' if loop.last else ',' %>\
      rst_en_o.${device}[1] == prim_mubi_pkg::MuBi4True${sep}
% endfor
    }),
    .rst_ns({
% for device in list(reversed(sw_rsts.keys())):
<% sep = '' if loop.last else ',' %>\
      resets_o.rst_${device}_n[1]${sep}
% endfor
    })
  );

  bind rstmgr rstmgr_rst_en_track_sva_if rstmgr_rst_en_track_sva_if (
    .resets_i(resets_o),
    .reset_en_i(rst_en_o),
% for clk in sorted(list(clk_freqs.keys())):
    .clk_${clk}_i,
% endfor
    .rst_por_ni(rst_por_ni)
  );

`endif
endmodule
