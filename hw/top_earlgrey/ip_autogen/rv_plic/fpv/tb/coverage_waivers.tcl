# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This line is a default case statement which could be executed if a parasitic state has been
# injected to the state register of u_prim_alert_sender.
check_cov -waiver -add -start_line 249 -end_line 249 -instance {dut.gen_alert_tx[0].u_prim_alert_sender} -comment {No parasitic state injection while doing FPV}

# The intention to add this assertion is to make sure that while doing FPV there is not a
# possibility to inject parasitic state to the state register of alert sender FSM.
assert -name AlertSenderNoParasiticState_A {dut.gen_alert_tx[0].u_prim_alert_sender.state_q <= 6}

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

# These are all the dead nodes in a binary tree. They are dead because the rightmost nodes at the
# bottom of the tree are tied with 1'b0. Hence, their parents on levels below them also assigned
# with 1'b0.
for {set level 7} {$level > 0} {incr level -1} {
  switch $level {
    7
    {
      set min 93
      set max 127
    }
    6
    {
      set min 46
      set max 63
    }
    5
    {
      set min 23
      set max 31
    }
    4
    {
      set min 12
      set max 15
    }
    3
    {
      set min 6
      set max 7
    }
    2
    {
      set min 3
      set max 3
    }
    1
    {
      set min 1
      set max 1
    }
  }
  set exp1 "dut.gen_target\[0\].u_target.u_prim_max_tree"
  for {set node $min} {$node <= $max} {incr node} {
    set exp2 ".gen_tree\[$level\].gen_level\[$node\].gen_nodes.sel"
    set exp ""
    append exp $exp1 $exp2
    check_cov -waiver -add -expression "$exp" -type {branch} -comment {Dead node}
  }
}
