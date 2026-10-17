// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/multibits_asm.h"
#include "hw/top/cheriot_mem_sys_regs.h" // Generated.
#include "hw/top/rv_core_ibex_regs.h" // Generated.
#include "hw/top/sram_ctrl_regs.h" // Generated.
#include "hw/top/top_memory.h" // Generated.

#define DV_STATUS_IN_TEST 0x4354
#define DV_STATUS_PASSED  0x900d
#define DV_STATUS_FAILED  0xbaad

#define TOP_CHERIOT_MEM_SYS_REVBM_SIZE_WORDS (TOP_CHERIOT_MEM_SYS_REVBM_SIZE_BYTES >> 2)

#define CAPABILITY_SIZE_BYTES   8
// Each region is defined by one word in the revocation bitmap,
// so the number of capabilities per region is just bits per RISC-V word.
#define CAPABILITIES_PER_REGION 32

#if !defined(TEST_ITERATION_COUNT)
#error "TEST_ITERATION_COUNT" must be defined with the number of iterations to run.
#endif

  .section .crt, "ax", @progbits
  .balign 4
  .globl _ottf_start
  .type _ottf_start, @function
_ottf_start:
  li   a0, TOP_SRAM_CTRL_META_REGS_BASE_ADDR
  li   a1, (1 << SRAM_CTRL_CTRL_INIT_BIT)
  sw   a1, SRAM_CTRL_CTRL_REG_OFFSET(a0)
meta_sram_init_loop:
  lw   a1, SRAM_CTRL_STATUS_REG_OFFSET(a0)
  andi a1, a1, (1 << SRAM_CTRL_STATUS_INIT_DONE_BIT)
  beqz a1, meta_sram_init_loop

cheriot_header:
  .option push
  .option norvc
  .option norelax

  li a0, TOP_RV_CORE_IBEX_CFG_BASE_ADDR
  li a1, MULTIBIT_ASM_BOOL4_TRUE
  sw a1, RV_CORE_IBEX_CHERIOT_ENA_REG_OFFSET(a0)
  sw a1, RV_CORE_IBEX_CHERIOT_LOCK_REG_OFFSET(a0)
  fence
  fence.i

  .option pop
cheriot_start:
  // In CHERIoT mode now.
  cspecialr a0, mtdc
  li        a1, TOP_RV_CORE_IBEX_CFG_BASE_ADDR
  csetaddr  ca1, ca0, a1
  li        a2, DV_STATUS_IN_TEST
  sw        a2, RV_CORE_IBEX_DV_SIM_WINDOW_REG_OFFSET(a1)

init_prng:
  // Xorshift32 PRNG requires non-zero seed value.
  li a5, 1

init_test_loop:
  // Load the iteration counter.
  li a4, TEST_ITERATION_COUNT

  j test_loop

prng:
  // Step the Xorshift32 PRNG state in register a5.
  // Clobbers: t0.
  //
  // Equivalent C code:
  // x ^= x << 13;
  // x ^= x >> 17;
  // x ^= x << 5;
  slli t0, a5, 13
  xor  a5, a5, t0
  srli t0, a5, 17
  xor  a5, a5, t0
  slli t0, a5, 5
  xor  a5, a5, t0
  cret

  // This test tests the revocation bitmap and the revocation engine (TBRE).
  // The test works as follows:
  //
  // In each iteration, the test chooses two 256-byte aligned regions of SRAM - A and B.
  // Region B simulates a "heap", from which memory is "allocated" from to region A.
  // Region A is filled with capabilities that point into region B, which simulates
  // memory allocations.
  //
  // The first capability in region A points to the first 8 bytes of region B,
  // the next capability in region A points to the next 8 bytes of region B, and so on.
  //
  // In each iteration, a random bit-pattern is written to the revocation bitmap
  // word corresponding to region B in SRAM. The tag bits of the capabilities in
  // region A should be the negation of the revocation bit-pattern.
  //
  // Region B revocation bits (REVBM, 4B)
  //          +----------+----------+----------+----------+
  //          |    1     |    0     |   ....   |    0     |
  //          +----------+----------+----------+----------+
  // Region B (SRAM, 256B)
  //          +----------+----------+----------+----------+
  //          |    8B    |    8B    |   ....   |    8B    |
  //          +----------+----------+----------+----------+
  //               ^          ^          ^          ^
  // Region A (SRAM, 256B)    |          |          |
  //          +----------+----------+----------+----------+
  //          |   Cap    |   Cap    |   ....   |   Cap    |
  //          +----------+----------+----------+----------+
  // Region A tags
  //          +----------+----------+----------+----------+
  //          |    0     |    1     |   ....   |    1     |
  //          +----------+----------+----------+----------+
  //
  // If the revocation word is cleared, the tags in region A should all be observed
  // to be set again, indicating that the revocation bitmap correctly inhibited the tags.
  //
  // The same revocation bit-pattern is then written again, and the revocation engine
  // is used on the capabilities in region A. After the revocation pass is completed
  // and the revocation bitmap is cleared, the capability tags in region A corresponding
  // to the set bits of the revocation bit-pattern should be cleared.
test_loop:
  beqz a4, success

  // Pick two regions, A and B, for each iteration of the test.
  // This is done by picking two random revocation bitmap words, then scaling
  // and offsetting them to the corresponding 256-byte address in SRAM.
  //
  // Note that the constants TOP_CHERIOT_MEM_SYS_REVBM_SIZE_BYTES,
  // TOP_SRAM_CTRL_MAIN_RAM_BASE_ADDR, etc, expose SRAM as a single
  // region of memory, despite the underlying hardware implementation
  // using two (primary and secondary) adjacent SRAMs.
  //
  // a3: 256-byte aligned address of region A in SRAM.
  // a2: 256-byte aligned address of region B in SRAM.
  // a1: 4-byte aligned address of revocation bits spanning region B in revocation bitmap.
test_pick_regions:
  ccall prng
  li    t0, TOP_CHERIOT_MEM_SYS_REVBM_SIZE_WORDS
  mulhu a3, a5, t0
  ccall prng
  li    t0, TOP_CHERIOT_MEM_SYS_REVBM_SIZE_WORDS
  mulhu a2, a5, t0
  beq   a2, a3, test_pick_regions // Try again if the same word is chosen for both regions.

  // Region A: [0, REVBM_SIZE_WORDS) revocation bitmap word number
  //    << 8 = [0, MAIN_RAM_SIZE_BYTES) SRAM byte offset of 256-byte region.
  slli a3, a3, 8
  li   t0, TOP_SRAM_CTRL_MAIN_RAM_BASE_ADDR
  //        -> [MAIN_RAM_BASE, MAIN_RAM_BASE+MAIN_RAM_SIZE_BYTES) SRAM address.
  add  a3, a3, t0

  // Region B: [0, REVBM_SIZE_WORDS) revocation bitmap word number
  //    << 2 = [0, REVBM_SIZE_BYTES) revocation bitmap byte offset of word.
  slli a1, a2, 2
  li   t0, TOP_CHERIOT_MEM_SYS_REVBM_BASE_ADDR
  //        -> [REVBM_BASE+0, REVBM_BASE+REVBM_SIZE_BYTES) revocation bitmap address.
  add  a1, a1, t0

  //    << 8 = [0, MAIN_RAM_SIZE_BYTES) SRAM byte offset of 256-byte region.
  slli a2, a2, 8
  li   t0, TOP_SRAM_CTRL_MAIN_RAM_BASE_ADDR
  //        -> [MAIN_RAM_BASE, MAIN_RAM_BASE+MAIN_RAM_SIZE_BYTES) SRAM address.
  add  a2, a2, t0

  // a0: Random byte offset within 8-byte revocation region.
  ccall prng
  andi  a0, a5, 7

  cspecialr s0, mtdc

test_init_regions:
  // Write region A with capabilities that point to region B.
  csetaddr   ct0, s0, a3 // t0: pointer to current capability to write in region A.
  csetaddr   ct1, s0, a2 // t1: current capability's target address in region B.
  .rep CAPABILITIES_PER_REGION
  cmove         ct2, ct1
  csetboundsimm ct2, ct2, 8
  cincoffset    ct2, ct2, a0 // randomised offset.
  sc            czero, 0(ct1)
  sc            ct2, 0(ct0)
  cincoffsetimm ct0, ct0, CAPABILITY_SIZE_BYTES
  cincoffsetimm ct1, ct1, CAPABILITY_SIZE_BYTES
  .endr
  fence

test_check_init_tags:
  // Test that all tags are set in region A, and none are set in region B.
  csetaddr ct0, s0, a3
  csetaddr ct1, s0, a2
  .rep CAPABILITIES_PER_REGION
  lc            ct2, 0(ct0)
  cgettag       t2, t2
  beqz          t2, failure
  lc            ct2, 0(ct1)
  cgettag       t2, t2
  bnez          t2, failure
  cincoffsetimm ct0, ct0, CAPABILITY_SIZE_BYTES
  cincoffsetimm ct1, ct1, CAPABILITY_SIZE_BYTES
  .endr

  // a0: Random revocation bitmap value.
  ccall prng
  mv    a0, a5

test_check_revocation_bitmap_works:
  // Write the random revocation bitmap value to the revocation bitmap
  // address corresponding to region B.
  csetaddr ct0, s0, a1
  sw       a0, 0(ct0)
  fence
  // Now, sweep through region A and read all the tags.
  // Where the revocation had a bit set, the capability in region A should
  // have a cleared tag, because the corresponding region of B has been revoked.
  csetaddr ct0, s0, a3
  // Negation of written revocation bitmap value = state of tag bits.
  not      t1, a0
  .rep CAPABILITIES_PER_REGION
  lc            ct2, 0(ct0)
  cgettag       t2, t2
  andi          tp, t1, 1
  bne           tp, t2, failure
  srli          t1, t1, 1
  cincoffsetimm ct0, ct0, CAPABILITY_SIZE_BYTES
  .endr

  // Unrevoke the region.
  csetaddr ct0, s0, a1
  sw       zero, 0(ct0)
  fence

test_check_tags_again:
  // Check that tags in region A appear set once again,
  // showing that they were just masked by the revocation bitmap.
  // Tags in region B should still be unset.
  csetaddr ct0, s0, a3
  csetaddr ct1, s0, a2
  .rep CAPABILITIES_PER_REGION
  lc            ct2, 0(ct0)
  cgettag       t2, t2
  beqz          t2, failure
  lc            ct2, 0(ct1)
  cgettag       t2, t2
  bnez          t2, failure
  cincoffsetimm ct0, ct0, CAPABILITY_SIZE_BYTES
  cincoffsetimm ct1, ct1, CAPABILITY_SIZE_BYTES
  .endr

test_run_revocation_engine:
  // Write the random revocation bitmap value to the revocation bitmap
  // address corresponding to region B again.
  csetaddr ct0, s0, a1
  sw       a0, 0(ct0)
  fence
  // Now use the TBRE to revoke capabilities in region A.
  li       t0, TOP_CHERIOT_MEM_SYS_REGS_BASE_ADDR
  csetaddr ct0, s0, t0
  sw       a3, CHERIOT_MEM_SYS_TBRE_BASE_ADDR_REG_OFFSET(t0)
  li       t1, CAPABILITIES_PER_REGION
  sw       t1, CHERIOT_MEM_SYS_TBRE_NUM_CAPS_REG_OFFSET(t0)
  li       t1, (1 << CHERIOT_MEM_SYS_TBRE_START_START_BIT)
  sw       t1, CHERIOT_MEM_SYS_TBRE_START_REG_OFFSET(t0)
  li       t1, (1 << CHERIOT_MEM_SYS_TBRE_STATUS_BUSY_BIT)
revocation_engine_poll:
  // Poll TBRE_STATUS until the revocation engine has finished.
  lw   t2, CHERIOT_MEM_SYS_TBRE_STATUS_REG_OFFSET(t0)
  and  t2, t2, t1
  bnez t2, revocation_engine_poll
revocation_engine_poll_done:
  // Check no errors occurred in the revocation engine.
  lw   t2, CHERIOT_MEM_SYS_TBRE_STATUS_REG_OFFSET(t0)
  andi t2, t2, ~(1 << CHERIOT_MEM_SYS_TBRE_STATUS_BUSY_BIT)
  bnez t2, failure
  // Clear the revocation bitmap after the region has been revoked.
  csetaddr ct0, s0, a1
  sw       zero, 0(ct0)
  fence

test_check_tags_after_revocation_engine:
  csetaddr ct0, s0, a3
  // Negation of written revocation bitmap value = state of tag bits.
  not      t1, a0
  .rep CAPABILITIES_PER_REGION
  lc            ct2, 0(ct0)
  cgettag       t2, t2
  andi          tp, t1, 1
  bne           tp, t2, failure
  srli          t1, t1, 1
  cincoffsetimm ct0, ct0, CAPABILITY_SIZE_BYTES
  .endr

test_iteration_done:
  // Success, onto the next iteration.
  addi a4, a4, -1
  j test_loop

success:
  cspecialr a0, mtdc
  li        a1, TOP_RV_CORE_IBEX_CFG_BASE_ADDR
  csetaddr  ca0, ca0, a1
  li        a1, DV_STATUS_PASSED
  sw        a1, RV_CORE_IBEX_DV_SIM_WINDOW_REG_OFFSET(a0)
  j park
failure:
  cspecialr a0, mtdc
  li        a1, TOP_RV_CORE_IBEX_CFG_BASE_ADDR
  csetaddr  ca0, ca0, a1
  li        a1, DV_STATUS_FAILED
  sw        a1, RV_CORE_IBEX_DV_SIM_WINDOW_REG_OFFSET(a0)
  j park
park:
  wfi
  j park
