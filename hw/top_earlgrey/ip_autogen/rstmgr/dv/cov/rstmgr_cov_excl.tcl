# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# The exclusions of hw/dv/tools/xcelium/common_cov_excl.tcl, for the primary partition, which has
# the TL-UL ports and the alert senders. The shared script names the instance $::env(DUT_TOP), the
# module named by the dut variable, which no longer exists.
exclude -inst tb.dut_primary -toggle '*tl_i.a_user.rsvd' -comment "\[UNSUPPORTED\] Based on our Comportability Spec."
exclude -inst tb.dut_primary -toggle '*tl_i.a_param' -comment "\[UNSUPPORTED\] Based on our Comportability Spec."
exclude -inst tb.dut_primary -toggle '*tl_o.d_param' -comment "\[UNR\] Follows tl_i.a_param which is unsupported."
exclude -inst tb.dut_primary -toggle '*tl_o.d_sink' -comment "\[UNR\] Based on our Comportability Spec."
exclude -inst tb.dut_primary -toggle '*tl_o.d_user.rsp_intg'\[6\] -comment "\[UNR\] Due to the ECC logics"
exclude -inst tb.dut_primary.gen_alert_tx*.u_prim_alert_sender -toggle '*alert*.ping_*' -comment "\[LOW_RISK\] Verified in prim_alert_sender/receiver TB."
