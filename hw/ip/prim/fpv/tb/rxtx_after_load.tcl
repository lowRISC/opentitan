# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This is a TCL file that can be sourced by FPV runs that are doing
# some form of "prim_alert_rxtx" verification.

proc move_to_task {task_name assert_name} {
    task -edit ${task_name} -copy "${assert_name}*"
    assert -disable ${assert_name}
}


set valid_state_props [get_property_list -regexp -include {"name" "ValidState_A$"}]
foreach prop $valid_state_props {
    assert -set_helper $prop
}

# The property names in this list are properties that depend on some FSM state register pointing at
# a parasitic state. Use a stopat on various state registers to make the properties say something.

task -create FreeFsm
stopat -task FreeFsm "i_prim_alert_sender.state_q"
stopat -task FreeFsm "i_prim_alert_receiver.state_q"

set parasitic_state_props {SenderStateDValid_A ReceiverStateDValid_A}

foreach psn $parasitic_state_props {
    foreach psp [get_property_list -regexp -include [list name "${psn}$"]] {
        move_to_task FreeFsm $psp
    }
}

# Add FreeFsm to the cov_tasks variable, which is a list of the tasks that will be used for
# check_cov at the end of fpv.tcl if coverage is enabled.
lappend cov_tasks FreeFsm
