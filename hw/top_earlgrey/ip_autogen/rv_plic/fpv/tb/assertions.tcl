# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# The intention to add this assertion is to make sure that while doing FPV there is not a
# possibility to inject parasitic state to the state variable of alert sender FSM.
assert -name RvPlicAlertSenderNoParasiticState \
  {dut.gen_alert_tx[0].u_prim_alert_sender.state_q <= 6}
