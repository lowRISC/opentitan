# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Verix CDC waiver file

set_rule_status -rule {RST_SYNC} -expression {(ReceivingFlop =~ "top_earlgrey.*.u_sync_1.gen_generic.u_impl_generic.q_o*") && (ResetSignal =~ "top_earlgrey.u_pinmux_aon.mio_pad_attr_q*.invert")} -status {Waived} -comment {Reviewed : reset source to reset synchronizer}
set_rule_status -rule {RST_SYNC} -expression {(ReceivingFlop =~ "top_earlgrey.*.u_sync_1.gen_generic.u_impl_generic.q_o*") && (ResetSignal =~ "IO*")} -status {Waived} -comment {Reviewed : reset source to reset synchronizer}
#set_rule_status -rule {RST_SYNC} -expression {(ReceivingFlop =~ "top_earlgrey.*.u_sync_1.gen_generic.u_impl_generic.q_o*") && (ResetSignal =~ "u_ast.dft_scan_md_o*")} -status {Waived} -comment {Reviewed : reset source to reset synchronizer}
set_rule_status -rule {RST_SYNC} -expression {(ReceivingFlop =~ "top_earlgrey.*_o*") && (ResetSignal =~ "u_ast.dft_scan_md_o*")} -status {Waived} -comment {Reviewed : reset source to reset synchronizer}
#set_rule_status -rule {RST_SYNC} -expression {(ReceivingFlop =~ "top_earlgrey.*.u_sync_1.gen_generic.u_impl_generic.q_o*") && (ResetSignal == "u_ast.scan_reset_no")} -status {Waived} -comment {Reviewed : reset source to reset synchronizer}
set_rule_status -rule {RST_SYNC} -expression {(ReceivingFlop =~ "top_earlgrey.*_o*") && (ResetSignal == "u_ast.scan_reset_no")} -status {Waived} -comment {Reviewed : reset source to reset synchronizer}
set_rule_status -rule {RST_SYNC} -expression {(ReceivingFlop =~ "top_earlgrey.*.u_sync_1.gen_generic.u_impl_generic.q_o*") && (ResetSignal =~ "top_earlgrey.u_pinmux_aon.u_reg.u_mio_periph_insel_46.q*")} -status {Waived} -comment {Reviewed : reset source to reset synchronizer}
set_rule_status -rule {RST_SYNC} -expression {(ReceivingFlop =~ "top_earlgrey.*.u_sync_1.gen_generic.u_impl_generic.q_o*") && (ResetSignal == "top_earlgrey.u_rstmgr_aon.u_d0_spi_device.u_rst_sync.u_sync_2.gen_generic.u_impl_generic.q_o[0]")} -status {Waived} -comment {Reviewed : reset source to reset synchronizer}
set_rule_status -rule {RST_SYNC} -expression {(ReceivingFlop =~ "top_earlgrey.*.u_sync_1.gen_generic.u_impl_generic.q_o*") && (ResetSignal == "top_earlgrey.u_rstmgr_aon.u_daon_lc_io_div4.u_rst_sync.u_sync_2.gen_generic.u_impl_generic.q_o[0]")} -status {Waived} -comment {Reviewed : reset source to reset synchronizer}
set_rule_status -rule {RST_SYNC} -expression {(ReceivingFlop =~ "top_earlgrey.*.u_sync_1.gen_generic.u_impl_generic.q_o*") && (ResetSignal == "top_earlgrey.u_rstmgr_aon.u_lc_src.gen_rst_pd_n[0].u_pd_rst.u_sync_2.gen_generic.u_impl_generic.q_o[0]")} -status {Waived} -comment {Reviewed : reset source to reset synchronizer}
set_rule_status -rule {RST_SYNC} -expression {(ReceivingFlop =~ "top_earlgrey.*.u_sync_1.gen_generic.u_impl_generic.q_o*") && (ResetSignal == "top_earlgrey.u_pinmux_aon.u_pinmux_strap_sampling.u_prim_lc_sync_lc_dft_en.gen_flops.u_prim_flop_2sync.u_sync_2.gen_generic.u_impl_generic.q_o[1]")} -status {Waived} -comment {Reviewed : reset source to reset synchronizer}
set_rule_status -rule {RST_SYNC} -expression {(ReceivingFlop =~ "top_earlgrey.*.u_sync_1.gen_generic.u_impl_generic.q_o*") && (ResetSignal == "top_earlgrey.u_pinmux_aon.u_pinmux_strap_sampling.tap_strap_q[0]")} -status {Waived} -comment {Reviewed : reset source to reset synchronizer}
