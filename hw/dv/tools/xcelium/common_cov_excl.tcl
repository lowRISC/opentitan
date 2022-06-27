# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

exclude -inst $::env(DUT_TOP) -toggle '*tl_i.a_user.rsvd' -comment "\[UNSUPPORTED\] Based on our Comportability Spec. Exercising this will result in assertion errors thrown."
exclude -inst $::env(DUT_TOP) -toggle '*tl_i.a_param' -comment "\[UNSUPPORTED\] Based on our Comportability Spec. Exercising this will result in assertion errors thrown."
exclude -inst $::env(DUT_TOP) -toggle '*tl_o.d_param' -comment "\[UNR\] Follows tl_i.a_param which is unsupported."
exclude -inst $::env(DUT_TOP) -toggle '*tl_o.d_sink' -comment "\[UNR\] Based on our Comportability Spec."
exclude -inst $::env(DUT_TOP) -toggle '*tl_o.d_user.rsp_intg'\[6\] -comment "\[UNR\] Due to the ECC logics"
exclude -inst $::env(DUT_TOP) -toggle '*alert_rx_*.ping_*' -comment "\[LOW_RISK\] Verified in prim_alert_receiver TB."
exclude -inst $::env(DUT_TOP).gen_alert_tx*.u_prim_alert_sender -toggle '*alert*.ping_*' -comment "\[LOW_RISK\] Verified in prim_alert_receiver TB."
