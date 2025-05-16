# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# The port data_o in u_data_chk is untied and used nowhere.
check_cov -waiver -add -start_line 25 -end_line 56 -type {statement} -instance {dut.u_reg.u_chk.u_tlul_data_integ_dec.u_data_chk} -comment {data_o is untied}

# The port data_o in u_data_chk is untied and used nowhere.
check_cov -waiver -add -start_line 25 -end_line 81 -type {statement} -instance {dut.u_reg.u_chk.u_chk} -comment {data_o is untied}

# Since the interrupts are level triggered, we don't use scr_q register in rv_plic_gateway. So,
# even if this logic is broken, nobody (in the assertions world) cares.
check_cov -waiver -add -start_line 33 -end_line 33 -instance {dut.u_gateway} -comment {Interrupts are level triggered and this assignment would not affect any assertions}

# To support the waivers above, this assertion is added. So, if interrupts are no longer level
# triggered, this will fail.
assert -name InterruptsLevelTriggered_A {!$rose(dut.u_gateway.le_i)}

# The ds output port is not connected for any instantiation of prim_subreg or prim_subreg_ext in
# rv_plic. This would only be connected for a writeable register that has an asynchronous clock
# (see reg_top.sv.tpl), and rv_plic doesn't have any of these. As such, the code that is waived
# here (which drives the port) is undetectable.
check_cov -waiver -add -source_file {../src/lowrisc_prim_subreg_0/rtl/prim_subreg.sv} -start_line 64 -end_line 64 -type {branch} -comment {Checker coverage is undetectable as ds is unconnected}

# For all the ip registers, de is true and hence wr_en is true. The branch misses the else part and
# appeared dead.
check_cov -waiver -add -source_file {../src/lowrisc_prim_subreg_0/rtl/prim_subreg.sv} -start_line 58 -end_line 58 -type {branch} -comment {wr_en is true and the branch doesn't contain the else part}

# The waivers below are waiving the branch and statement (inside those branches) in mubi(4-16)_and
# function in prim_mubi_pkg used in rv_plic_csr_assert_fpv. Since, rv_plic registers doesn't have
# any regwen types therefore all the mubi(4-16)_and functions are unused.
check_cov -waiver -add -start_line 119 -end_line 139 -instance {prim_mubi_pkg} -comment {Unused code block}

check_cov -waiver -add -start_line 258 -end_line 278 -instance {prim_mubi_pkg} -comment {Unused code block}

check_cov -waiver -add -start_line 397 -end_line 417 -instance {prim_mubi_pkg} -comment {Unused code block}

check_cov -waiver -add -start_line 536 -end_line 556 -instance {prim_mubi_pkg} -comment {Unused code block}

# Below task acts as an isolated container for the following assertion and stopat.
task -create FSMParasiticState

# Drives any possible value to state_q.
stopat -task FSMParasiticState "dut.gen_alert_tx\[0\].u_prim_alert_sender.state_q"

# If some silly state has been injected in state_q then the FSM will always comes back to Idle in
# the next state as the FSM treats the unrecognized state as Idle. This assertion also covers the
# checker coverage for the default case.
assert -name FSMParasiticState::AlertSenderFSMParasiticState_A {!(dut.gen_alert_tx[0].u_prim_alert_sender.state_q inside  {Idle, AlertHsPhase1, AlertHsPhase2, PingHsPhase1, PingHsPhase2, Pause0, Pause1}) ->  dut.gen_alert_tx[0].u_prim_alert_sender.state_d == Idle}

proc clog2 {NumSrc} {
  return [expr {ceil(log($NumSrc)/log(2))}]
}

# These are all the dead nodes in a binary tree. They are dead because the rightmost nodes at the
# bottom of the tree are tied with 1'b0. Hence, their parents on levels below them also assigned
# with 1'b0.
proc tree {NumSrc} {
  set Numlevels [clog2 $NumSrc]
  for {set level 1} {$level <= $Numlevels-1} {incr level} {
    set h [expr {$Numlevels - $level}]
    set node_int [expr {int(1 + floor(($NumSrc-1-2**($h-1))/(2**$h)))}]
    set exp1 "dut.gen_target\[0\].u_target.u_prim_max_tree"
    for {set node $node_int} {$node < 2**$level} {incr node} {
        set exp2 ".gen_tree\[$level].gen_level\[$node].gen_nodes.sel"
        set exp ""
        append exp $exp1 $exp2
        check_cov -waiver -add -expression "$exp" -type {branch} -comment {Dead node}
    }
  }
}

tree {186}
