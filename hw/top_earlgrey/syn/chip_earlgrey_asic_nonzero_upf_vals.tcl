# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Defines paths to signals that require non-zero isolation values in UPF.

# The LC OFF value is set to 0x1010 in RTL. Note that changing this encoding has
# implications on isolation cell values in RTL. Do not change this unless
# absolutely needed. See #4244 for the audit / discussion about which ports
# should have nonzero values.
set UPF_ISO_LC_OFF_PORTS_CLAMP1 {
  top_earlgrey/u_aon_timer_aon/lc_escalate_en_i[3] \
  top_earlgrey/u_aon_timer_aon/lc_escalate_en_i[1] \
  top_earlgrey/u_pinmux_aon/lc_escalate_en_i[3]    \
  top_earlgrey/u_pinmux_aon/lc_escalate_en_i[1]    \
  top_earlgrey/u_pinmux_aon/lc_check_byp_en_i[3]   \
  top_earlgrey/u_pinmux_aon/lc_check_byp_en_i[1]   }
