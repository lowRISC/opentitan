# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0

  
.section .text

default_exc_handler:
  jal x0, sleep_loop //exc handler

reset_handler:
  /* set all registers to zero */
  mv  x1, x0
  mv  x2, x1
  mv  x3, x1
  mv  x4, x1
  mv  x5, x1
  mv  x6, x1
  mv  x7, x1
  mv  x8, x1
  mv  x9, x1
  mv x10, x1
  mv x11, x1
  mv x12, x1
  mv x13, x1
  mv x14, x1
  mv x15, x1
  mv x16, x1
  mv x17, x1
  mv x18, x1
  mv x19, x1
  mv x20, x1
  mv x21, x1
  mv x22, x1
  mv x23, x1
  mv x24, x1
  mv x25, x1
  mv x26, x1
  mv x27, x1
  mv x28, x1
  mv x29, x1
  mv x30, x1
  mv x31, x1

  /* stack initilization */
  la   x2, _stack_start


_start:
  .global _start

  /* clear BSS */
  la x26, _bss_start
  la x27, _bss_end
  bge x26, x27, zero_loop_end
  
  
zero_loop:
  sw x0, 0(x26)
  addi x26, x26, 4
  ble x26, x27, zero_loop
zero_loop_end:


main_entry:
  /* jump to main program entry point (argc = argv = 0) */
  addi x10, x0, 0
  addi x11, x0, 0
  jal x1, main
  // Branch if non returned 0;
  beq x10, x0, success
  li a0, 0xc11c0018
  li t0, 0xFFFFFFFF
  sw t0, 0(a0)
  j sleep_loop

success:
  li a0, 0xc11c0018
  li t0, 0x1
  sw t0, 0(a0)

sleep_loop:
  wfi
  j sleep_loop

  
/* =================================================== [ exceptions ] === */
/* This section has to be down here, since we have to disable rvc for it  */

  .section .vectors, "ax"
  .option norvc;
  
  .org 0x00
  .rept 10
  jal x0, default_exc_handler
  .endr
  
  jal x0, default_exc_handler
  
  jal x0, external_irq_handler

  .org 0x30
  .rept 18
  jal x0, default_exc_handler
  .endr
  jal x0, default_exc_handler
  jal x0, default_exc_handler


  // reset vector
  .org 0x80
  jal x0, reset_handler

