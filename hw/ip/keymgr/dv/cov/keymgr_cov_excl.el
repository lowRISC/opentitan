// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

ANNOTATION: "[LOWRISK] non-idle -> error"
CHECKSUM: "117487336 1278423873"
INSTANCE: tb.dut.u_ctrl
Fsm state_q "1382639396"
Transition StCtrlOwnerKey->StCtrlWipe "894->51"

ANNOTATION: "[LOWRISK] non-idle -> error"
CHECKSUM: "2519441784 2391940402"
INSTANCE: tb.dut.u_kmac_if
Fsm state_q "3597806508"
Transition StClean->StError "1021->238"
Fsm state_q "3597806508"
Transition StTxLast->StError "320->238"
Fsm state_q "3597806508"
Transition StTx->StError "155->238"
Fsm state_q "3597806508"
Transition StOpWait->StError "553->238"
