# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This is used as an "after_load" file for rom_ctrl verification.

proc move_to_task {task_name assert_name} {
    task -edit ${task_name} -copy "${assert_name}*"
    assert -disable ${assert_name}
}

# There is a security check in FpvSecCmCompareFsmAlert_A. This checks that an FSM error in
# u_checker_fsm.u_compare.u_state_regs will get propagated to an alert. Such an FSM error cannot
# happen without fault injection, so we move the property into a task and use a stopat to allow the
# FSM's state_q variable to vary arbitrarily.
#
# Once the property has been copied, disable the original version (in <embedded>::) and the
# associated cover property.
task -create CompareFsm
stopat -task CompareFsm "dut.gen_fsm_scramble_enabled.u_checker_fsm.u_compare.state_q"
move_to_task CompareFsm "tb.dut.gen_asserts_with_scrambling.FpvSecCmCompareFsmAlert_A"

# There is also a security check in FpvSecCmCheckerFsmAlert_A. The FSM uses PRIM_FLOP_SPARSE_FSM to
# check that if the FSM is corrupted then an assert will be generated. The assert doesn't quite work
# though, because it ends up asserting that a broken state_d will cause the assertion. The state_d
# variable is actually combinationally driven to ensure that it is always a valid state. (This is
# better than allowing the state to stay arbitrary: it guarantees that a fault will cause a the FSM
# state to move to one a large hamming distance from the valid states).
#
# The cleanest approach is probably to use a stopat on state_q and define a different assertion,
# which says an unexpected state will instantly cause the prim_alert_sender to be asked to send an
# alert.
task -create CheckerFsm
stopat -task CheckerFsm "dut.gen_fsm_scramble_enabled.u_checker_fsm.state_q"
assert \
    -name "CheckerFsm::BadCheckerStateCausesAlert_A" \
    "!(dut.gen_fsm_scramble_enabled.u_checker_fsm.state_q inside
       {rom_ctrl_pkg::ReadingLow, rom_ctrl_pkg::ReadingHigh, rom_ctrl_pkg::RomAhead,
        rom_ctrl_pkg::KmacAhead, rom_ctrl_pkg::Checking, rom_ctrl_pkg::Done})
       ->
     |dut.alerts"
assert -disable "tb.dut.gen_asserts_with_scrambling.FpvSecCmCheckerFsmAlert_A"
