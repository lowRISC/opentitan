// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

  /**
   * Linker-provided symbols for stack layout information.
   *
   * We assume that the stack is a word-aligned array of words,
   * so we can use word loads and stores on it exclusively.
   */
  .extern _stack_start
  .extern _stack_size

  /**
   * Linker-provided symbols for .bss and .data regions.
   *
   * These are all known to be word-aligned.
   */
  .extern _bss_start
  .extern _bss_end
  .extern _data_start
  .extern _data_end

// noreturn void _final_jump_asm(entrypoint_t entry, void *next_stack_start);
_final_jump_asm:
  .globl _final_jump_asm
  // Since this function is called from C, the registers |a0| and |a1|
  // correspond to the function arguments |entry| and |next_stack_start|,
  // respectively.

  // Bleach the ROM stack, which we no longer need for anything.
  // Here, |t0| is the current word being zeroed, while |t1| is
  // the number of bytes left to zero.
  //
  // This operation is "done in reverse", from the bottom of the stack
  // to the top. As such, |t0| decreases with each write.
  la   t0, _stack_start
  la   t1, _stack_size
stack_bleach:
  addi t0, t0, -4
  addi t1, t1, -4
  sw   zero, 0(t0)
  bnez t1, stack_bleach

  // Bleach the .bss section. |t0| is the current word being zeroed,
  // while |t1| is the end pointer.
  //
  // This operation is done in forward order.
  la  t0, _bss_start
  la  t1, _bss_end
  bge t0, t1, bss_bleach_end
bss_bleach:
  sw   zero, 0(t0)
  addi t0, t0, 4
  ble  t0, t1, bss_bleach
bss_bleach_end:

  // Do the exact same bleach operation to the .data section.
  la  t0, _data_start
  la  t1, _data_end
  bge t0, t1, data_bleach_end
data_bleach:
  sw   zero, 0(t0)
  addi t0, t0, 4
  ble  t0, t1, data_bleach
data_bleach_end:

  // Clobber every register, including |ra| and |sp|. However, do
  // not clobber |a0| and |a1|, which still function arguments passed
  // by the caller.
  li x1,  0  // ra
  li x2,  0  // sp
  li x3,  0
  li x4,  0
  li x5,  0
  li x6,  0
  li x7,  0
  li x8,  0
  li x9,  0
  // Skip |x10| and |x11|, aka |a0| and |a1|.
  li x12, 0
  li x13, 0
  li x14, 0
  li x15, 0
  li x16, 0
  li x17, 0
  li x18, 0
  li x19, 0
  li x20, 0
  li x21, 0
  li x22, 0
  li x23, 0
  li x24, 0
  li x25, 0
  li x26, 0
  li x27, 0
  li x28, 0
  li x29, 0
  li x30, 0
  li x31, 0

  // Copy the final trampoline to the top of the next stage's stack.
  // This will dirty some registers, but this is non-secret information,
  // so we won't be re-clobbering them.
  //
  // Like the stack bleach, this operation is done in reverse.
  //
  // As before, |t0| is the current word being copied, while |t1| is the
  // end pointer (the "start"). |t2| is the location to which the current word
  // is to be copied. |t3| is a scratch register.
  //
  // TODO: |a1| should be offset by a random amount.
  la  t0, _final_trampoline_end
  la  t1, _final_trampoline
  mv  t2, a1
trampoline_copy:
  addi t0, t0, -4
  addi t2, t2, -4
  lw   t3, 0(t0)
  sw   t3, 0(t2)
  bne  t0, t1, trampoline_copy

  // Jump to the trampoline. |t2| points to the last word written,
  // which is the start of the trampoline.
  jr t2

_final_trampoline:
  // This function takes |entry| and |args| from |_final_jump_asm| with
  // the same ABI: they sit in |a0| and |a1|, respectively.
  //
  // Also, this function must be independently relocatable, since it is
  // loaded an executed at a location not known until runtime. This means
  // that auipc, and pseudoinstructions that expand to it (such as j, call,
  // and la) must be avoided.

  .balign 4 // Ensure that our function is word-aligned.

  // TODO: Mark ROM as unreadable here. This should include tests to make
  // sure the rom has actually been made unreadable.

  // Perform the final jump.
  mv t0, a0  // Set up the jump address.
  mv a0, a1  // Set up the next stage argument pointer.
  // NOTE: it is not possible to return here, since |ra| is still zeroed;
  // a return from the entry point will result in an instruction fetch
  // fault.
  jr t0

_final_trampoline_end:
  .balign 4  // Ensure that our function can be copied as an array of words.
