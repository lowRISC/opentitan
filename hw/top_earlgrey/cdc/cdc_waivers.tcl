# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Verix CDC waiver file

# TODO: need to add more common waivers here. We may have to break this into
# multiple files.
#
# set_rule_status -rule { S_CONF_ENV } -status { Waived } -expression { } \
#   -comment {}
# set_rule_status -rule { S_CONF_ENV } -status { Waived } -all_rule_data \
#   -comment {}


# Assumes modules defined in run-cdc.tcl

if {[info exists modules] == 0} {
  error "modules variable does not exist!" 99
}

foreach mod $modules {
  if {[file exists $CDC_WAIVER_DIR/cdc_waivers.$mod.tcl]} {
    source $CDC_WAIVER_DIR/cdc_waivers.$mod.tcl
  }
}

# Common Waivers

