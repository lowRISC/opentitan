// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package prim_ascon_duplex_tb_pkg;


typedef enum  {
  Idle,
  SendAD,
  WaitADRead,
  SendMSG,
  CheckMSGLen,
  WaitMSGRead,
  ReceiveTag,
  CheckCTLen,
  SendCT,
  WaitCTRead,
  VerifyTag,
  WaitForEver
} fsm_tb_state_e;

endpackage : prim_ascon_duplex_tb_pkg
