# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This is a TCL file that can be sourced by FPV runs that are doing
# some form of "prim_alert_rxtx" verification.

proc move_to_task {task_name assert_name} {
    task -edit ${task_name} -copy "${assert_name}*"
    assert -disable ${assert_name}
}

# Explicitly waive coverage for the empty default item at the end of the case statement in some
# instance of prim_diff_decode. This item doesn't actually have any effect, but is recommended by
# our style guide because in some situations this sort of thing affects behaviour when the FSM state
# is 'x.
proc waive_end_of_decode_fsm {instance} {
    # Get a list of all the cover items that depend on state_q (the FSM state) as a fanin
    set names [check_cov -name -get_cover_id -source ${instance}.state_q -direction fanin]

    # The cover item we are looking for has a name that starts with
    # ${instance}.gen_async.p_diff_fsm._automatic_. The item has subtype "case_stmt_empty_branch"
    # and it should be the only on with that subtype. Filter for items with the subtype.
    set regex "${instance}\\.gen_async\\.p_diff_fsm\\._automatic_.*case_stmt_empty_branch"
    set filtered [lsearch -all -inline -regexp $names $regex]

    # There should be exactly one hit
    set num_hits [llength ${filtered}]
    if {${num_hits} != 1} {
        error "# hits for empty case at end of ${instance} FSM: ${num_hits}, but we expected 1."
    }

    # Convert the cover item name back to an id. Bizarrely, the result with a silly name is
    # (uint32_t)(-1). To check nothing crazy has happened, check that the result is less than
    # 10,000.
    set cov_id [check_cov -get_cover_id -cover_name ${filtered}]
    if {${cov_id} > 10000} {
        error "Failed to find cover id for ${filtered}"
    }

    # Finally, waive the cover item
    puts "Waiving coverage for empty case item at end of FSM in ${instance}."
    check_cov -waiver -add -cover_item_id ${cov_id} -comment "Empty case item at end of FSM"
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

# If the alert sender/receiver pair is asynchronous then we want to waive the do-nothing empty case
# item at the end of each instance of prim_diff_decode. We detect this by looking at an "AsyncOn"
# localparam in the top module.
set localparams [get_design_info -list local_parameter -verbosity silent]
set async_on "?"
foreach {k v} ${localparams} {
    if {[string equal ${k} "AsyncOn"]} { set async_on $v; }
}
if {${async_on} == "?"} { error "No AsyncOn localparam in tb"; }

if {${async_on} == "1'b1"} {
    waive_end_of_decode_fsm i_prim_alert_sender.u_decode_ping
    waive_end_of_decode_fsm i_prim_alert_sender.u_decode_ack
    waive_end_of_decode_fsm i_prim_alert_receiver.u_decode_alert
}
