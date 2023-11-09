// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Checks the given value is equal to zero or a second given value.
 * If they are not equal,
 * a0 is set to a unique value and returns early from sram_main.
 *
 * @param actual The value to check.
 * @param[opt] expected The value to check against. Defaults to zero.
 */
.macro check actual, expected=zero
  beq \actual, \expected, 1f
  li a0, \@+1
  jr s1
  1:
.endm

.section .text

/**
 * Runs every instruction that is available to the ibex.
 *
 * @param[out] a0 error code, will be non-zero if a check fails.
 */
  .balign 4
  .global sram_main
  .type sram_main, @function
sram_main:
  mv s1, ra
  li a0, -1

  jal smoke_branch
  jal smoke_auipc
  jal smoke_load_store
  jal smoke_alu_i
  jal smoke_alu_i_imm
  jal smoke_alu_m
  jal smoke_alu_zba
  jal smoke_alu_zbb
  jal smoke_alu_zbc
  jal smoke_alu_zbf
  jal smoke_alu_zbp
  jal smoke_alu_zbr
  jal smoke_alu_zbs
  jal smoke_alu_b_misc
  jal smoke_alu_zbt
  jal smoke_alu_b_imm
  jal smoke_csr
  jal smoke_fence
  c.jal smoke_c_sp
  la t0, smoke_c
  c.jalr t0

  mv a0, zero
  jr s1

/**
 * Check the RV32I branch instructions
 */
smoke_branch:
  li t0, 0x8e9c1d0d
  li t1, 0x3610897a
  mv t2, t1
  bne t0, t1, smoke_beq
  check t0
  smoke_beq:
  beq t1, t2, smoke_blt
  check t0
  smoke_blt:
  blt t0, t1, smoke_bge
  check t0
  smoke_bge:
  bge t2, t1, smoke_bltu
  check t0
  smoke_bltu:
  bltu t1, t0, smoke_bgeu
  check t0
  smoke_bgeu:
  bgeu t2, t1, smoke_branch_ret
  check t0
  smoke_branch_ret:
  ret

/**
 * Check the `auipc` instruction.
 */
smoke_auipc:
  auipc t0, 0xA
  auipc t1, 0xA
  addi  t0, t0, 4
  check t0, t1
  ret

/**
 * Checks the RV32I load and store instructions
 */
smoke_load_store:
  li t1, 0x2d3eae8c

  sb t1, -4(sp)
  lb t2, -4(sp)
  li t3, 0xffffff8c
  check t2, t3

  lbu t2, -4(sp)
  li t3, 0x0000008c
  check t2, t3

  sh  t1, -8(sp)
  lh  t2, -8(sp)
  li t3, 0xffffae8c
  check t2, t3

  lhu t2, -8(sp)
  li t3, 0x0000ae8c
  check t2, t3

  sw t1, -12(sp)
  lw t2, -12(sp)
  check t2, t1

  ret

/**
 * Checks the RV32I non-immediate ALU instructions
 */
smoke_alu_i:
  li   t0, 0x3217ab08
  li   t1, 0x24e6a04f

  add  t2, t1, t0
  slt  t1, t0, t2
  sll  t0, t2, t1
  sra  t1, t0, t2
  and  t2, t1, t0
  xor  t0, t2, t1
  sub  t1, t0, t2
  or   t2, t1, t0
  sltu t0, t1, t2
  srl  t1, t2, t0

  li t0, 0x7b03fdab
  check t1, t0
  ret

/**
 * Checks the RV32I immediate ALU instructions
 */
smoke_alu_i_imm:
  li    t0, 0xfcec24cf

  .option push
  .option norvc
  slti  t0, t0, 0x37e
  ori   t0, t0, 0x13b
  sltiu t0, t0, 0x23e
  addi  t0, t0, 0x7c4
  srli  t0, t0, 3
  xori  t0, t0, 0x4f1
  slli  t0, t0, 28
  srai  t0, t0, 30
  andi  t0, t0, 0x76b
  .option pop

  li t1, 0x76a
  check t1, t0
  ret

/**
 * Checks the RV32M instructions
 */
smoke_alu_m:
  li      t0, 144
  li      t1, 0x61a061b6
  div     t2, t1, t0
  divu    t2, t2, t0
  rem     t2, t1, t2
  remu    t2, t1, t2
  mulh    t0, t2, t1
  mulhsu  t2, t1, t0
  mul     t0, t2, t1
  mulhu   t2, t1, t0

  # check result
  li t0, 0x25f7c073
  check t2, t0
  ret

/**
 * Checks the instructions from the zba extension
 */
smoke_alu_zba:
  addi t0, zero, 0x2f7
  addi t1, zero, 0x7ce
  sh1add t0, t0, t1
  sh2add t0, t0, t1
  sh3add t0, t0, t1

  li t2, 0x0001fdbe
  check t2, t0
  ret

/**
 * Checks the instructions from the zbb extension
 *
 * Note: rev8, orc.b, and zext.h are pseudo instructions
 * for grevi, gorci, and pack respectively,
 * which are tested in `smoke_alu_b_imm` and `smoke_alu_zbp`.
 */
smoke_alu_zbb:
  li   t0, 3
  li   t1, 0x2bb36000
  ctz  t2, t1
  clz  t2, t2
  cpop t2, t2
  check  t0, t2

  li t3, 0x151a2a2a
  andn   t0, t3, t1
  rol    t0, t0, t2
  orn    t0, t3, t0
  sext.h t0, t0
  ror    t0, t0, t2
  xnor   t0, t1, t0
  li  t1, 0x2bb36a2a
  check t0, t1

  sext.b t0, t0
  li  t1, 0x0000002a
  check t0, t1

  max  t2, t1, t3
  check  t2, t3
  min  t2, t1, t3
  check  t2, t1
  maxu t2, t1, t3
  check  t2, t3
  minu t2, t1, t3
  check  t2, t1

  ret

/**
 * Checks the instructions from the zbc extension
 */
smoke_alu_zbc:
  addi t0, zero, 0x395
  li t1, 0x6ac8234c
  clmul   t0, t0, t1
  clmulr  t0, t0, t1
  clmulh  t0, t0, t1

  li t1, 0x08810f55
  check t0, t1
  ret

/**
 * Checks the instructions from the zbf extension
 *
 * Note: pack and packh are not checked here
 * but in covered in `smoke_alu_zbp`.
 */
smoke_alu_zbf:
  li t0, 0x0e0a47f3
  li t1, 0x0e1fcff3
  .option push
  .option arch, +zbf0p93
  bfp t0, t0, t0
  .option pop
  check t0, t1
  ret

/**
 * Checks the instructions from the zbp extension
 *
 * Note: andn, orn, xnor, rol, and ror are not checked here
 * but in `smoke_alu_zbb`.
 */
smoke_alu_zbp:
  .option push
  .option arch, +zbp0p93
  li t0, 0xcc9fd6b6
  li t1, 0x7ce71003
  pack    t2, t0, t1
  packu   t3, t0, t1
  packh   t2, t2, t3

  li t0, 0x00009fb6
  check t0, t2

  li t2, 0x04030001
  xperm.n t3, t3, t2
  xperm.b t3, t3, t2
  xperm.h t3, t3, t2
  li t0, 0x000000f7
  check t3, t0

  li t0, 4
  grev    t1, t1, t0
  shfl    t1, t1, t0
  gorc    t1, t1, t0
  unshfl  t1, t1, t0
  .option pop

  li t0, 0xffff3131
  check t0, t1
  ret

/**
 * Checks the instructions from the zbr extension
 */
smoke_alu_zbr:
  li t0, 0xabdca651
  li t1, 0xac605e47
  .option push
  .option arch, +zbr0p93
  crc32.b  t0, t0
  crc32.h  t0, t0
  crc32.w  t0, t0
  crc32c.b t0, t0
  crc32c.h t0, t0
  crc32c.w t0, t0
  .option pop
  check t1, t0
  ret

/**
 * Checks the instructions from the zbs extension
 */
smoke_alu_zbs:
  addi t0, zero, 0x3
  addi t1, zero, 0x4
  bclr t0, t0, 0
  binv t0, t0, 1
  bset t0, t0, 2
  check t0, t1

  bext t1, t0, 1
  check t1

  ret

/**
 * Checks the instructions from the zbt extension
 */
smoke_alu_zbt:
  .option push
  .option arch, +zbt0p93
  li t0, 7
  li t1, 4
  li t2, 0x5d76fb6b
  li t3, 0xe5693902
  fsl t2, t2, t3, t0
  fsr t2, t2, t3, t1
  cmix t2, t0, t2, t3

  li   t1, 0xe5693907
  check  t1, t2

  cmov t2, t0, t3, t2
  check  t2, t3
  .option pop

  ret

/**
 * Checks the `slo` and `sro` instructions
 */
smoke_alu_b_misc:
  li t0, 0x9bfae1bb
  li t1, 8
  li t2, 4
  //slo t0, t0, t1
  .insn r OP, 0b001, 0b0010000, t0, t0, t1
  //sro t0, t0, t2
  .insn r OP, 0b101, 0b0010000, t0, t0, t2

  li t1, 0xffae1bbf
  check t0, t1
  ret

/**
 * Checks the immediate bitmanip instructions.
 *
 * This is a superset of RV32B's immediate instructions.
 */
smoke_alu_b_imm:
  li    t0, 0xfcec24cf
  //sloi  t0, t0, 7
  .insn i OP_IMM, 0b001, t0, t0, 0x207
  // zbs
  bclri t0, t0, 3
  bseti t0, t0, 31
  binvi t0, t0, 19
  bexti t1, t0, 8
  // zbt
  .option push
  .option arch, +zbt0p93
  fsri  t0, t0, t1, 4
  .option pop
  //sroi  t0, t0, 5
  .insn i OP_IMM, 0b101, t0, t0, 0x205
  // zbb
  rori  t0, t0, 16
  // zbp
  .option push
  .option arch, +zbp0p93
  grevi   t0, t0, 4
  shfli   t0, t0, 4
  gorci   t0, t0, 2
  unshfli t0, t0, 4
  .option pop

  li t1, 0xf0ffafff
  check t0, t1
  ret

/**
 * Checks the RV32I CSR instructions.
 *
 * Note: This routine clobbers counters
 * and so inhibits all counters before returning.
 */
smoke_csr:
  li t0, 0b11100
  li t1, 0b00001
  li t2, 0b01000
  li t3, 0b10101
  csrw mcountinhibit, t0
  csrs mcountinhibit, t1
  csrc mcountinhibit, t2
  csrr t0, mcountinhibit
  check t0, t3

  csrwi mcountinhibit, 0b11100
  csrsi mcountinhibit, 0b00001
  csrci mcountinhibit, 0b01000
  csrr t0, mcountinhibit
  check t0, t3

  // Inhibit all counters
  csrw mcountinhibit, zero
  ret

/**
 * Runs the fence instructions.
 *
 * No checks are performed.
 */
smoke_fence:
  fence
  fence.i
  ret

/**
 * Checks the compressed 'add immediate to sp' instructions.
 */
smoke_c_sp:
  c.addi16sp sp, -64
  c.addi4spn a5, sp, 64
  c.addi16sp sp, 64
  check a5, sp


/**
 * Checks the RV32C instructions.
 *
 * Notes: `c.ebreak` and those within `smoke_c_sp` are not checked.
 */
smoke_c:
  c.lui  a5, 0x1b
  c.bnez a5, 2f
  check  ra
  2:
  c.sub  a5, a5
  c.beqz a5, 2f
  check  ra
  2:
  c.j 2f
  check  ra
  2:

  c.li   a5, 0x1b
  c.andi a5, 0x1e
  c.addi a5, 0x1a
  c.slli a5, 26
  c.srai a5, 4
  c.srli a5, 2

  li a3, 0x3f400000
  check a5, a3

  li a4, 0x37a
  c.xor a5, a4
  c.add a5, a4
  c.and a5, a4
  c.or  a5, a3

  addi a3, a3, 0x270
  check a5, a3

  c.mv a5, a4
  check a5, a4

  addi a5, sp, -8
  c.sw a4, 4(a5)
  c.lw a5, 4(a5)
  check a4, a5

  addi sp, sp, -12
  c.swsp a3, 8(sp)
  c.lwsp a4, 8(sp)
  addi sp, sp, 12
  check a4, a3

  c.jr ra
