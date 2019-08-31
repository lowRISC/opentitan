# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

analyze +define+ASIC_SYNTHESIS+SYNTHESIS -F [glob build/formal_0/sim-icarus/*.scr] -sv

elaborate $env(LINT_TOP)

# read_sdc design.sdc
# TODO: add SDC file above

analyze_intent
verify_rdc

report_policy ALL -all_runs -verbose -output rdc.rpt

exit
