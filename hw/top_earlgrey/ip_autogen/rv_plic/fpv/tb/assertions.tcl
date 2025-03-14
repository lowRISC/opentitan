# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# The intention to add this assertion is to make sure that while doing FPV there is not a
# possibility to inject parasitic state to the state variable of alert sender FSM.
assert -name RvPlicAlertSenderNoParasiticState \
  {dut.gen_alert_tx[0].u_prim_alert_sender.state_q <= 6}

# It is unlikely to get the err_o for rv_plic. There is a precondition related to the assertion
# FpvSecCmRegWeOnehotCheck which is enabled if err_o is high. The intention to add this assertion
# is to make sure that err_o never happens as we waived off the precondition in waivers.tcl.
# Refer to waivers.tcl for the detailed argument as why this is not possible.
assert -name RvPlicRegNoOneHot&EnError \
  {dut.u_reg.u_prim_reg_we_check.u_prim_onehot_check.err_o == 0}
