# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Verix CDC waiver file

set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_rv_core_ibex*.*rdata*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_rv_core_ibex*.*gen_alert_senders*.*alert_test_seq_q*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*gen_alert_tx*.u_prim_alert_sender*.*q*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_sram_ctrl_main.u_prim_alert_sender*.*q*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_flash_ctrl*.*u_state_flop*.*impl_generic*.q_o*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_flash_ctrl*.*gen_alert_senders*.*alert_test_seq_q*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_keymgr.u_ctrl.key_state_ecc_q*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_keymgr.u_falut_alert.state_q*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_keymgr.*.lfsr_q*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_keymgr.*.u_fault_alert_state_q*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_alert_handler.gen_classes*.u_accu.*impl_generic*.q_o*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*.u_reg.*.src_busy_q*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*.u_reg.*.u_intr_state.q*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_alert_sender.alert_test_seq_q*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_reg.u_reg_if.rdata*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_sysrst_ctrl_aon.u_reg.*.u_intr_state.q*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_aon_timer_aon.u_reg.*.src_busy_q*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_pinmux_aon.u_reg.*.src_busy_q*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_pinmux_aon.u_reg.*.u_dio_pad_sleep_statue_en_0.q*")} -comment {multiple sources with mux}

set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_clkmgr_aon.u_reg.*.*meas_ctrl_en_cdc*.id_q*")} -comment {Intended reconvergence in clkmgr}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_clkmgr_aon.u_reg.*.*u_io_meas.src_err_req")} -comment {Intended reconvergence in clkmgr}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_alert_handler.gen_alerts**.u_alert_receiver*.*impl_generic*.q_o*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_kmac.gen_entropy.*.u_lfsr_chunk.lfsr_q*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_pwrmgr_aon.u_reg.u_intr_state.q*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_pwrmgr_aon.u_reg.u_reg_if.rdata*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_pwrmgr_aon.i_wake_info.info*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_rstmgr_aon.u_reg.u_reg_if.rdata*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_adc_ctrl_aon.u_reg.u_intr_state.q*")} -comment {multiple sources with mux}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_adc_ctrl_aon.u_reg.*.src_busy_q*")} -comment {multiple sources with mux}

set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_sync_1.gen_generic.u_impl_generic.q_o**") && (ReconSignal=~"*u_ast_clks_byp.*io_clk*src*")} -comment {Intended reconvergence in clkmgr}
