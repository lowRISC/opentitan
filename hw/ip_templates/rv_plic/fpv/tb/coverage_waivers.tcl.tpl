# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# This line is a default case statement which could be executed if a parasitic state has been
# injected to the state register of u_prim_alert_sender.
check_cov -waiver -add -start_line 249 -end_line 249 -type {branch} -instance\
 {dut.gen_alert_tx[0].u_prim_alert_sender} -comment {No parasitic state injection while doing FPV}

# The intention to add this assertion is to make sure that while doing FPV there is not a
# possibility to inject parasitic state to the state register of alert sender FSM.
assert -name AlertSenderNoParasiticState_A {dut.gen_alert_tx[0].u_prim_alert_sender.state_q <= 6}

# The port data_o in u_data_chk is untied and used nowhere.
check_cov -waiver -add -start_line 25 -end_line 56 -type {statement} -instance\
 {dut.u_reg.u_chk.u_tlul_data_integ_dec.u_data_chk} -comment {data_o is untied}

# The port data_o in u_data_chk is untied and used nowhere.
check_cov -waiver -add -start_line 25 -end_line 81 -type {statement} -instance\
 {dut.u_reg.u_chk.u_chk} -comment {data_o is untied}

# These are bunch of software controlled registers with RO and RW Software access. For RO
# registers, the branch is a deadcode as we for RO is tied to 0 in u_reg under the instantiation of
# these registers. For RW registers, since ds in untied for all of the software registers inside
# the instantiation in u_reg and no assertions are affected by ds, the checker coverage is
# undetectable. ds is the data that will be written into the flop while qs is the current flop
# value that the software can see so waiving the branch makes more sense then writing an assertion
# for future flop value when nobody uses it.
check_cov -waiver -add -source_file {../src/lowrisc_prim_subreg_0/rtl/prim_subreg.sv}\
 -start_line 64 -end_line 64 -type {branch} -comment {For RO regs, the branch is a deadcode. For\
 RW regs, the checker is undetectable as ds is unconnected}
