# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Meridian RDC Waivers

# Assumes modules defined in run-rdc.tcl
if {[info exists modules] == 0} {
  error "modules variable does not exist!" 99
}

foreach mod $modules {
  if {[file exists $RDC_WAIVER_DIR/rdc_waivers.$mod.tcl]} {
    source $RDC_WAIVER_DIR/rdc_waivers.$mod.tcl
  }
}
