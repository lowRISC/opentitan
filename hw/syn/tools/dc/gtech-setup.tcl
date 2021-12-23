# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# GTECH library setup for DC.

set_app_var target_library "gtech.db"
set_app_var synthetic_library "dw_foundation.sldb"
set_app_var synlib_wait_for_design_license "DesignWare-Foundation"
set_app_var link_library "* ${target_library} ${synthetic_library}"
set_app_var symbol_library "generic.sdb"
set NAND2_GATE_EQUIVALENT 1.0
