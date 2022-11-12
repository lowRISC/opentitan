// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

ANNOTATION: "[LOWRISK] non-idle -> error"
INSTANCE: tb.dut.u_kmac_if
Fsm state_q "3597806508"
Transition StTxLast->StError "320->238"
Fsm state_q "3597806508"
Transition StTx->StError "155->238"
Fsm state_q "3597806508"
Transition StOpWait->StError "553->238"
Fsm state_q "3597806508"
Transition StClean->StError "1021->238"
ANNOTATION: "[UNR]"
Fsm state_q "3597806508"
Transition StIdle->StTxLast "930->320"
