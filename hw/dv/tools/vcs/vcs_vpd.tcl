# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# TCL file invoked from VCS's simv at run-time using this: -ucli -do <this file>

if {[info exists ::env(WAVES)]} {
  if {$::env(WAVES) == 1} {
    dump -file $::env(DUMP_FILE)
    dump -add $::env(TB_TOP) -depth 0 -aggregates -scope "."
  }
}

run
quit
