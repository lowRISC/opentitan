# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# The statement is a deadcode as le_i is always level triggered.
check_cov -waiver -add -start_line 34 -end_line 34 -type {branch} -instance {dut.u_gateway} -comment {le_i is tied to a parameter which is 0}

# All the interrupts are level triggered thus le_i is always 0. The reason to add this assertion is
# to support the waiver for the statement above. The statement is a ternary assignment and the
# conditional part of it is le_i which is always false.
assert -name InterruptsAreLevelTriggered {!$rose(dut.u_gateway.le_i)}

# This line is a default case statement which could be executed if a parasitic state has been
# injected to the state register of u_prim_alert_sender.
check_cov -waiver -add -start_line 249 -end_line 249 -type {branch} -instance\
 {dut.gen_alert_tx[0].u_prim_alert_sender} -comment {No parasitic state injection while doing FPV}

# The intention to add this assertion is to make sure that while doing FPV there is not a
# possibility to inject parasitic state to the state register of alert sender FSM.
assert -name AlertSenderNoParasiticState_A {dut.gen_alert_tx[0].u_prim_alert_sender.state_q <= 6}
