/* Copyright lowRISC contributors. */
/* Licensed under the Apache License, Version 2.0, see LICENSE for details. */
/* SPDX-License-Identifier: Apache-2.0 */

# OTBN Smoke test, runs various instructions which are expected to produce the
# final register state see in smoke_expected.txt

.section .text

# x2 = 0xd0beb513
lui x2, 0xd0beb
add x2, x2, 0x513
# x3 = 0xa0be911a
lui x3, 0xa0be9
add x3, x3, 0x11a

# x4 = x2 + x3 = 0x717d462d
add x4, x2, x3

# x5 = x3 - x2 = 0xcfffdc07
sub x5, x3, x2

# x6 = x2 | x3 = 0xf0beb51b
or x6, x2, x3

# x7 = x2 & x3 = 0x80be9112
and x7, x2, x3

# x8 = x2 ^ x3 = 0x70002409
xor x8, x2, x3

# x9 = x2 | 0x123 = 0xd0beb533
or x9, x2, 0x123

# x10 = x2 & 0x7bc = 0x510
and x10, x2, 0x7bc

# x11 = x2 ^ 0x47a = 0xd0beb169
xor x11, x2, 0x47a

# x12 = x2 << 10 = 0xfad44c00
sll x12, x2, 10

# x13 = x2 >> 13 = 0x685f5
srl x13, x2, 13

# x14 = x2 >>> 7 =  0xffa17d6a
sra x14, x2, 7

# x15 = x2 << x3[4:0] = 0x4c000000
sll x15, x2, x3

# x16 = x2 >> x3[4:0] = 0x34
srl x16, x2, x3

# x17 = x2 >>> x3[4:0] = 0xfffffff4
sra x17, x2, x3

# x18 = dmem[16] = 0xfacefeed
lw x18, 16(x0)

# dmem[4] = x9 = 0xd0beb533
sw x9, 4(x0)

# x19 = dmem[4] = 0xd0beb533
lw x19, 4(x0)

# x20 = 0
li x20, 0

bne x19, x18, test_label_1

# x20 = 0xbaad (shouldn't happen due to branch)
li x20, 0xbaad

test_label_1:

# x20 = x20 + 0x123 = 0x123
add x20, x20, 0x123

jal x0, test_label_2

# x20 = x20 + 0x123 = 0x246 (shouldn't happen due to jump)
add x20, x20, 0x123

test_label_2:

# x21 = x20 + x0 = 0123
add x21, x20, x0

beq x20, x21, test_label_3

# x21 = x21 + 0x123 = 0x246 (shouldn't happen due to branch)
add x21, x21, 0x123

test_label_3:

# until LID/SID implemented use mod WSR to load bignum registers with base li
# psuedo-instruction
# mod = 0x78fccc06_2228e9d6_89c9b54f_887cf14e_c79af825_69be586e_9866bb3b_53769ada
li x23, 0x78fccc06
csrrw x0, 0x7d7, x23
li x23, 0x2228e9d6
csrrw x0, 0x7d6, x23
li x23, 0x89c9b54f
csrrw x0, 0x7d5, x23
li x23, 0x887cf14e
csrrw x0, 0x7d4, x23
li x23, 0xc79af825
csrrw x0, 0x7d3, x23
li x23, 0x69be586e
csrrw x0, 0x7d2, x23
li x23, 0x9866bb3b
csrrw x0, 0x7d1, x23
li x23, 0x53769ada
csrrw x0, 0x7d0, x23

# x22 = 0x89c9b54f
csrrs x23, 0x7d5, x0

# Note that some instructions used the fixed inputs (from w1 and w2) others use
# results from previous instructions. When debugging an failure it is recommened
# you first look at the failure from the lowest numbered register as failures
# can cascade into later instructions.

# w1 = mod = 0x78fccc06_2228e9d6_89c9b54f_887cf14e_c79af825_69be586e_9866bb3b_53769ada
bn.wsrr w1, 0

# rnd WSR gives fixed value for now
# w2 = rnd = 0x99999999_99999999_99999999_99999999_99999999_99999999_99999999_99999999
bn.wsrr w2, 1

# w3 = w1 + w2 = 0x1296659f_bbc28370_23634ee9_22168ae8_613491bf_0357f208_320054d4_ed103473
bn.add w3, w1, w2

# w4 = w1 - w2 = 0xdf63326c_888f503c_f0301bb5_eee357b5_2e015e8b_d024bed4_fecd21a1_b9dd0141
bn.sub w4, w1, w2

# w5 = w1 | w2 = 0xf9fddd9f_bbb9f9df_99d9bddf_99fdf9df_df9bf9bd_f9bfd9ff_99ffbbbb_dbff9bdb
bn.or w5, w1, w2

# w6 = x1 & w2 = 0x18988800_00088990_89899109_88189108_81989801_09981808_98009919_11109898
bn.and w6, w1, w2

# w7 = w1 ^ w2 = 0xe165559f_bbb1704f_10502cd6_11e568d7_5e0361bc_f027c1f7_01ff22a2_caef0343
bn.xor w7, w1, w2

# w8 = ~w1 = 0x870333f9_ddd71629_76364ab0_77830eb1_386507da_9641a791_679944c4_ac896525
bn.not w8, w1

# w9 = {w1, w2} >> 117 = 0xd7c12b4d_f2c374c3_35d9da9b_b4d6d4cc_cccccccc_cccccccc_cccccccc_cccccccc
bn.rshi w9, w1, w2 >> 117

# mod = w4 = 0xdf63326c_888f503c_f0301bb5_eee357b5_2e015e8b_d024bed4_fecd21a1_b9dd0141
bn.wsrw 0, w4

# w0 = 0
bn.xor w0, w0, w0

# w10 = w6 + w2 = 0xb2322199_99a2232a_23232aa3_21b22aa2_1b32319a_a331b1a2_319a32b2_aaaa3231
bn.addm w10, w6, w2

# w11 = w5 + w2 - mod = 0xb43444cc_ccc4433c_43433bc3_44b43bc4_4b3434cb_c334b4c4_34cc33b3_bbbc3433
bn.addm w11, w5, w2

# w12 = w11 - w2 = 0x1a9aab33_332aa9a2_a9a9a229_ab1aa22a_b19a9b32_299b1b2a_9b329a1a_22229a9a
bn.subm w12, w11, w2

# w13 = (w2 - w11) + mod = 0xc4c88739_5564a69a_4686798c_43c8b58a_7c66c359_a689a3aa_639a8787_97ba66a7
bn.subm w13, w2, w11

# w14 = w8 + w9 = 0x5ec45f47_d09a8aec_ac10254c_2c59e37e_0531d4a7_630e745e_34661191_795631f1
bn.add  w14, w8, w9, FG0

# w16 = w1 - w2 = 0xdf63326c_888f503c_f0301bb5_eee357b5_2e015e8b_d024bed4_fecd21a1_b9dd0141 (with borrow = 1)
bn.sub  w16, w1, w2, FG1

# w15 = w10 + w11 + 1 (carry) = 0x66666666_66666666_66666666_66666666_66666666_66666666_66666666_66666665
bn.addc w15, w10, w11, FG0

# x17 = w3 - w4 - 1 (borrow) = 0x33333333_33333333_33333333_33333333_33333333_33333333_33333333_33333331
bn.subb w17, w3, w4, FG1

# x24 = {fg1, fg0} = 0x55
csrrs x24, 0x7c8, x0

# w18 = w1 + (w2 << 136) = 0x1296659f_bbc28370_23634ee9_22168a4e_c79af825_69be586e_9866bb3b_53769ada
bn.add w18, w1, w2 << 136

# w19 = w1 & (w2 << 72) = 0x18988800_00088990_89899109_88189108_81989801_09981800_00000000_00000000
bn.and w19, w1, w2 << 72

# w20 = w1 - (w2 >> 184) = 0x78fccc06_2228e9d6_89c9b54f_887cf14e_c79af825_69be57d4_fecd21a1_b9dd0141
bn.sub w20, w1, w2 >> 184

# w21 = w1 | (w2 >> 120) = 0x78fccc06_2228e9d6_89c9b54f_887cf1df_df9bf9bd_f9bfd9ff_99ffbbbb_dbff9bdb
bn.or  w21, w1, w2 >> 120

# w22 = w21 + 0x1bd = 0x78fccc06_2228e9d6_89c9b54f_887cf1df_df9bf9bd_f9bfd9ff_99ffbbbb_dbff9d98
bn.addi w22, w21, 0x1bd

# w23 = w21 - 0x207 = 0x78fccc06_2228e9d6_89c9b54f_887cf1df_df9bf9bd_f9bfd9ff_99ffbbbb_dbff99d4
bn.subi w23, w21, 0x207

# *x26 == w24 = dmem[x25 == 0x0] = 0xcccccccc_bbbbbbbb_aaaaaaaa_facefeed_deadbeef_cafed00d_d0beb533_1234abcd
# x25 = x25 + 0x20 = 0x20
li x25, 0
li x26, 24
bn.lid x26, 0(x25++)

# dmem[x25 == 0x20] = *x26 == w20 = 0x78fccc06_2228e9d6_89c9b54f_887cf14e_c79af825_69be57d4_fecd21a1_b9dd0141
# x26 = x26 + 1 = 21 (0x15)
li x26, 20
bn.sid x26++, 0(x25)

# w25 = w24 = 0xcccccccc_bbbbbbbb_aaaaaaaa_facefeed_deadbeef_cafed00d_d0beb533_1234abcd
bn.mov w25, w24

# *x27 == w26 = *x26 == w21 = 0x78fccc06_2228e9d6_89c9b54f_887cf1df_df9bf9bd_f9bfd9ff_99ffbbbb_dbff9bdb
# x26 = x26 + 1 = 22 (0x16)
li x27, 26
bn.movr x27, x26++

# w27 = w2 == w1 ? w5 : w6 = w6 = 0x18988800_00088990_89899109_88189108_81989801_09981808_98009919_11109898
bn.cmp w1, w2
bn.sel w27, w5, w6, FG0.Z

# w28 = (w4 - w3 - 1 (borrow)) & 1 ? w7 : w8 = w7 = 0xe165559f_bbb1704f_10502cd6_11e568d7_5e0361bc_f027c1f7_01ff22a2_caef0343
bn.cmpb w4, w3
bn.sel w28, w7, w8, FG0.L

# acc = w26 = 0x78fccc06_2228e9d6_89c9b54f_887cf1df_df9bf9bd_f9bfd9ff_99ffbbbb_dbff9bdb
bn.wsrw 2, w26

# {w30, w29} = (w28 * w27 + acc) =
# 0x15a7cbef_a5f473e1_860c1110_6bcc33ed_1583aef1_8130f3df_1a806984_c4f3507e
#   41575c5d_24cf5526_1a1d070d_673963ce_e80fed2a_13c1b84d_b1fddf94_eb0953a3
bn.mulqacc           w27.0, w28.0, 0
bn.mulqacc           w27.1, w28.0, 64
bn.mulqacc.so w29.L, w27.0, w28.1, 64
bn.mulqacc           w27.2, w28.0, 0
bn.mulqacc           w27.1, w28.1, 0
bn.mulqacc           w27.0, w28.2, 0
bn.mulqacc           w27.3, w28.0, 64
bn.mulqacc           w27.2, w28.1, 64
bn.mulqacc           w27.1, w28.2, 64
bn.mulqacc.so w29.U, w27.0, w28.3, 64
bn.mulqacc           w27.3, w28.1, 0
bn.mulqacc           w27.2, w28.2, 0
bn.mulqacc           w27.1, w28.3, 0
bn.mulqacc           w27.3, w28.2, 64
bn.mulqacc.so w30.L, w27.2, w28.3, 64
bn.mulqacc.so w30.U, w27.3, w28.3, 0

# w31 = w28[127:0] * w27[127:0] = 0x2f97be14_a0c429f2_53b42730_953d7d2f_0873f36c_1a01de4e_17fe23d9_0f09b7c8
bn.mulqacc.Z       w27.0, w28.0, 0
bn.mulqacc         w27.0, w28.1, 64
bn.mulqacc         w27.1, w28.0, 64
bn.mulqacc.wo w31, w27.1, w28.1, 128

# w0 = acc = 0x2f97be14_a0c429f2_53b42730_953d7d2f_0873f36c_1a01de4e_17fe23d9_0f09b7c8
bn.wsrr w0, 2

# Nested loop testing, inner adds repeated a total of 3 * 5 = 15 times
# x28 = 4, x29 = 3
li x28, 4
li x29, 3
# Outer loop, repeat x29 == 3 times
loop x29, 4
  # Inner loop, repeat 5 times
  loopi  5, 2
    # x28 = x28 + x28 = x28 * 2
    add x28, x28, x28
    # x29 = x29 + x29 = x29 * 2
    add x29, x29, x29
    # end of inner loop
  # Nested loops cannot end on same instruction
  nop
  # end of outer loop
# x28 = 4 * (2 ** 15) = 0x00020000
# x29 = 3 * (2 ** 15) = 0x00018000

# Single instruction loop test
# Repeat  5 times
loopi 5, 1
  # x28 = x28 + x28 = x28 * 2
  add x28, x28, x28
# x28 = 0x00020000 * (2 ** 5) = 0x00400000

jal x0, end

# Place end at fixed address so write to x31 by jal doesn't have changing value
# as more is added to smoke test
.org 0x800
end:

# x31 = 0x804
jal x31, test_fn_1

# test call/return with call stack
jal x1, test_fn_2

# test call stack by pushing values without return
# push 0x80c to call stack
jal x1, call_stack_1

# push 0x810 to call stack
call_stack_1:
jal x1, call_stack_2

# push 0x814 to call stack
call_stack_2:
jal x1, call_stack_3

call_stack_3:

ecall

test_fn_1:
  # x21 = 0xcafef00d
  li x22, 0xcafef00d
  jalr x0, x31, 0

test_fn_2:
  # x21 = x21 + 3 = 0xcafef010
  addi x22, x22, 3
  jalr x0, x1, 0

.section .data
.word 0x1234abcd
.word 0xbaadf00d
.word 0xcafed00d
.word 0xdeadbeef
.word 0xfacefeed
.word 0xaaaaaaaa
.word 0xbbbbbbbb
.word 0xcccccccc
