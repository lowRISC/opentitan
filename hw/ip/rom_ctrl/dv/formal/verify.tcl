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

# The register top has a write-enable check (u_prim_reg_we_check) and this uses prim_onehot_check to
# generate an error signal if the write-enable has more than one bit set. This can't happen in
# normal operation, so the FPV test cannot see the precondition for the inner prim's Onehot0Check_A
# assertion.
#
# Since there's actually only one register that is possible to write, this isn't really a security
# feature and doesn't need testing with e.g. a stopat. Instead, assert that the value is always
# onehot0 and disable the cover property.
assert -name "AlwaysOneHot0_A" "\$onehot0(dut.u_reg_regs.reg_we_check)"
set prim_onehot_check_path "tb.dut.u_reg_regs.u_prim_reg_we_check.u_prim_onehot_check"
cover -disable "${prim_onehot_check_path}.Onehot0Check_A:precondition1"

# There is also the FpvSecCmRegWeOnehotCheck_A assertion to check that a fatal alert gets generated
# if the reg_we_check signal in rom_ctrl_regs_reg_top is not onehot0. Since we have just proved this
# can't happen, disable the precondition cover.
cover -disable "tb.dut.FpvSecCmRegWeOnehotCheck_A:precondition1"

# The prim_one_hot_check module is instantiated with the EnableCheck parameter true. As such, it has
# an EnableCheck_A assertion that asserts none of the write-enable bits are set if en_i is false.
# The only way a write-enable signal can be set is through alert_test_we, which implies reg_we and
# addr_hit[0]. That addr_hit[0] signal implies that addrmiss will be false, which implies en_i will
# be high.
#
# But maybe it still makes sense to have this path to the error signal (catching some cases of fault
# injection). Use a stopat on the input to u_prim_reg_we_check to allow this signal to vary freely.
task -create FreeWe
stopat -task FreeWe "dut.u_reg_regs.u_prim_reg_we_check.oh_i"
move_to_task FreeWe "${prim_onehot_check_path}.gen_enable_check.gen_not_strict.EnableCheck_A"

# There are several prim_count instances in the dut. All of these detect fault injection by
# generating an error, which causes an alert, if the two counters don't sum to the right total. For
# FPV testing, we have to use stopat to allow the fault injection, copy the property to the task and
# disable the version that doesn't have the stopat.
#
# The prim_count instances that lie in u_tl_adapter_rom all have their clr_i and decr_en_i signals
# wired to zero. For these instances, disable the cover property for the assertions that talk about
# them handling the signals being nonzero.
task -create PrimCount
stopat -task PrimCount "dut.gen_fsm_scramble_enabled.u_checker_fsm.u_compare.u_prim_count_addr.cnt_q"

move_to_task PrimCount "tb.dut.gen_asserts_with_scrambling.FpvSecCmCompareAddrCtrCheck_A"

# Waive coverage for the ClrFwd_A assertion in every instantiation of prim_count. This assertion is
# supposed to check that the clr_i signal works, but the instantiation in tlul_adapter_sram wires
# clr_i to zero. Also add an assertion that checks this really is dead zero.
#
# The decr_en_i signal is also wired to zero. Again, we add an assertion to check this is true and
# then waive precondition coverage for things that need a decrement request.
#
# Similarly, we have to waive coverage for the UpCntIncrStable_A assertion. This assertion is
# supposed to be checking that the count saturates at its maximum value (instead of wrapping). But
# it's actually impossible to get into a situation where we're trying to increment past one request
# or response. This is because the ROM always responds in exactly one cycle so there's no way to
# increment a second time. The same is true for the down count.
#
# Finally, we have to waive coverage for the UpCntIncrStable_A and DnCntIncrStable_A assertions for
# these prim_count counters. In each case, these are impossible to hit because we have a 2 entry
# FIFO and the ROM always replies in exactly one cycle.

foreach fifo_pr { { u_reqfifo ReqFifo } { u_sramreqfifo SramReqFifo } { u_rspfifo RspFifo } } {
    set fifo_inst_name [lindex $fifo_pr 0]
    set fifo_prop_name [lindex $fifo_pr 1]

    set fifo_path "dut.u_tl_adapter_rom.${fifo_inst_name}"

    foreach ptr_pr { { u_wptr Wptr } { u_rptr Rptr } } {
        set ptr_inst_name [lindex $ptr_pr 0]
        set ptr_prop_name [lindex $ptr_pr 1]

        set ptr_path "${fifo_path}.gen_normal_fifo.u_fifo_cnt.gen_secure_ptrs.${ptr_inst_name}"

        stopat -task PrimCount "${ptr_path}.cnt_q"
        move_to_task PrimCount "tb.dut.FpvSecCm${fifo_prop_name}${ptr_prop_name}Check_A"

        assert -name "CannotSaturateUp_${fifo_prop_name}_${ptr_inst_name}_A" \
            "${ptr_path}.incr_en_i && !${ptr_path}.set_i -> !&${ptr_path}.cnt_o"
        cover -disable "tb.${ptr_path}.g_check_incr.UpCntIncrStable_A:precondition1"

        assert -name "CannotSaturateDn_${fifo_prop_name}_${ptr_inst_name}_A" \
            "${ptr_path}.incr_en_i && !${ptr_path}.set_i -> |${ptr_path}.cnt_q\[1\]"
        cover -disable "tb.${ptr_path}.g_check_incr.DnCntIncrStable_A:precondition1"
    }
}
