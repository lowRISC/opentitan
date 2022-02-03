# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Verix CDC waiver file

set_rule_status -rule { W_RECON_GROUPS } -status { Waived } \
   -expression {u_gpio.gen_filter} \
   -comment {filters are reconverged into registers. But it's OK.}