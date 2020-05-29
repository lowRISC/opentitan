// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Allocate space in .bss for saving architectural state before jumping into the
// test
  .lcomm arch_state_store, 4 * 17 //(ra, sp, gp, tp, s0-s11, mtvec)

  .section .text

run_rvc_test:
  .globl run_rvc_test

  // Save the architectural state. There is no need to save caller preserved
  // registers as C calling run_rvc_test will expect them to be clobbered anyway
  // and act appropriately. RA is the exception as we need to know where to jump
  // back to after the test is complete. mtvec is saved as the compliance test
  // environment alters it, other CSRs may also be changed but no adverse
  // effects have yet been observed from this.
  la t0, arch_state_store

  sw ra,   0(t0)
  sw sp,   4(t0)
  sw gp,   8(t0)
  sw tp,  12(t0)
  sw s0,  16(t0)
  sw s1,  20(t0)
  sw s2,  24(t0)
  sw s3,  28(t0)
  sw s4,  32(t0)
  sw s5,  36(t0)
  sw s6,  40(t0)
  sw s7,  44(t0)
  sw s8,  48(t0)
  sw s9,  52(t0)
  sw s10, 56(t0)
  sw s11, 60(t0)

  csrr t1, mtvec
  sw t1, 64(t0)

// jump to compliance test
  j _rvc_start

end_rvc_test:
  .globl end_rvc_test

  // restore architectural state
  la t0, arch_state_store

  lw ra,   0(t0)
  lw sp,   4(t0)
  lw gp,   8(t0)
  lw tp,  12(t0)
  lw s0,  16(t0)
  lw s1,  20(t0)
  lw s2,  24(t0)
  lw s3,  28(t0)
  lw s4,  32(t0)
  lw s5,  36(t0)
  lw s6,  40(t0)
  lw s7,  44(t0)
  lw s8,  48(t0)
  lw s9,  52(t0)
  lw s10, 56(t0)
  lw s11, 60(t0)

  lw t1, 64(t0)
  csrw mtvec, t1

  jr ra

// riscv-compliance loads its own mtvec that will jump to mtvec_handler if the
// symbol exists
mtvec_handler:
  .globl mtvec_handler

  // restore gp/sp so handler from OT library can work
  la t0, arch_state_store

  lw sp,   4(t0)
  lw gp,   8(t0)

  // jump to the handler from the OT library
  j crt_interrupt_vector
