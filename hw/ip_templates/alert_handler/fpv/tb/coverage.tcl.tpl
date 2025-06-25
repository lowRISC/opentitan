# Copyright lowRISC contributors (OpenTitan project).
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

# Anything lives in this file has an intention to cover the undetectable coverage items.

# Below task acts as an isolated container for the following assertion and stopat.
task -create FSMParasiticState

# Drives any possible value to state_q.
stopat -task FSMParasiticState "i_prim_alert_sender.state_q"
stopat -task FSMParasiticState "i_prim_alert_receiver.state_q"

# If some silly state has been injected in state_q then the FSM will always comes back to Idle in
# the next state as the FSM treats the unrecognized state as Idle. This assertion also covers the
# checker coverage for the default case.
assert -name FSMParasiticState::AlertSenderFSMParasiticState_A {
!(i_prim_alert_sender.state_q inside
{i_prim_alert_sender.Idle, i_prim_alert_sender.AlertHsPhase1, i_prim_alert_sender.AlertHsPhase2,
 i_prim_alert_sender.PingHsPhase1, i_prim_alert_sender.PingHsPhase2, i_prim_alert_sender.Pause0,
 i_prim_alert_sender.Pause1}) -> i_prim_alert_sender.state_d == Idle
}

# For alert_receiver, this works slightly different. We should consider integrity failure and
# initialization request as well.
assert -name FSMParasiticState::AlertReceiverFSMParasiticState_A {
!(i_prim_alert_receiver.state_q inside
{i_prim_alert_receiver.Idle, i_prim_alert_receiver.HsAckWait, i_prim_alert_receiver.Pause0,
 i_prim_alert_receiver.Pause1, i_prim_alert_receiver.InitReq, i_prim_alert_receiver.InitAckWait
}) -> i_prim_alert_receiver.state_d inside {Idle, InitReq}
}
