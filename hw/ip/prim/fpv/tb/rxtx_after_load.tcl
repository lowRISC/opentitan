# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This is a TCL file that can be sourced by FPV runs that are doing
# some form of "prim_alert_rxtx" verification.

set valid_state_props [get_property_list -regexp -include {"name" "ValidState_A$"}]
foreach prop $valid_state_props {
    assert -set_helper $prop
}
