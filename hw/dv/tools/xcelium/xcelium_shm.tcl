# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

if {[info exists ::env(WAVES)]} {
  if {$::env(WAVES) == 1} {
    database -open -default -shm $::env(DUMP_FILE)
    probe $::env(TB_TOP) -all -depth all -shm
  }
}

run
quit
