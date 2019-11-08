// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

.section .text.trap;
.align  4;

_trap_start:
    j _trap_exception

// This could be exception or user interrupt
// 0xb is the environment call to indicate the end
_trap_exception:
    csrr a0, mcause
    addi a1, zero, 0xb
    beq a0, a1, _int_exc
    la a1, begin_signature
    // write to value pointed by begin_signature and uses a1 as address scratch
    sw a0, begin_signature, a1
_int_exc:
    la a0, write_tohost
    jr a0
