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
