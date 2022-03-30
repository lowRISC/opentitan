// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

  .section .bss
arch_state_store:
  // Allocate space in .bss for saving architectural state before jumping
  // into the test
  .balign 4
  .zero 4 * 17 // ra, sp, gp, tp, s0-s11, mtvec
  .size arch_state_store, .-arch_state_store

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

  // Tail-call to compliance test.
  //
  // The test will jump to `end_rvc_test` at the end rather than
  // return, so we don't want to do a `call`.
  tail _rvc_start

end_rvc_test:
  .globl end_rvc_test

  // Restore architectural state.
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

  ret

// riscv-compliance loads its own mtvec that will jump to mtvec_handler if the
// symbol exists. This will only be jumped to in situations where we are not
// expected to recover.
mtvec_handler:
  .globl mtvec_handler

  // Restore gp/sp so handler from the OTTF will work correctly.
  la t0, arch_state_store

  lw sp,   4(t0)
  lw gp,   8(t0)

  // Virtual-tail-call into the OTTF's handler.
  lw t1,  64(t0)
  jr t1
