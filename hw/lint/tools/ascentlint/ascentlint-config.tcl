# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# get installation path of ascentlint
set RI_INSTALL [file dirname [exec which ascentlint]]

# source the policy file containing the lowrisc lint rules
source "$RI_INSTALL/../Ascent/Lint/lib/policies/lowRISC/LRLR-v1.0.policy"

# increase this from 8k (default) to 32k such that large arrays like
# regfiles can be analyzed and linted.
set ri_max_total_range_bits 32768
set ri_max_single_range_bits 32768

