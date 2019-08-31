# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

foreach script_file [glob -nocomplain ascentlint.policy *.waiver] {
  source $script_file
}

analyze +define+ASIC_SYNTHESIS+SYNTHESIS -F [glob build/formal_0/sim-icarus/*.scr] -sv

elaborate $env(LINT_TOP)

report_policy -skip_empty_summary_status -compat -output lint.rpt NEW

exit
