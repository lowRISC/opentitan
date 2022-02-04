# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0


# Remove leading "# " from the front of log file lines and run the test if not in gui mode.
# This provides compatibility for log file error checking with other supported simulators within Opentitan.
set gui 0
if {[info exists ::env(GUI)]} {
  set gui "$::env(GUI)"
}

if {$gui == 0} {
  set PrefMain(LinePrefix) ""
  run -all
} else {
  set PrefMain(LinePrefix) ""
}
