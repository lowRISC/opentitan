// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package usbdev_pkg;

  // Code the state values so that the transitions software could poll are single bit
  // Woken->Idle and WokenUon->Idle (after sw ack) should therefore be single bit changes
  typedef enum logic [2:0] {
    AwkIdle =     3'b000,
    AwkTrigUon =  3'b011,   // 2 bit change from Idle but sw not monitoring
    AwkTrigUoff = 3'b010,   // ok with two bit change out because chip power is off
    AwkWokenUon = 3'b001,   // one bit change in/out to TrigUon and Idle, chip off to Woken
    AwkWoken =    3'b100    // one bit change out to Idle, in has chip power off
  } awk_state_e;

  typedef awk_state_e awk_state_t;

endpackage : usbdev_pkg
