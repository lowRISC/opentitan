/*
  veri-titan commit hash: 47792932f788b92221ff61e4037811a867e747c7
*/

.globl modexp_var_3072_f4
modexp_var_3072_f4:
  bn.xor w31, w31, w31 << 0, FG0
  li x8, 4
  li x9, 3
  li x10, 4
  li x11, 2
  addi x19, x23, 0
  addi x20, x26, 0
  addi x21, x24, 0
  jal x1, montmul
  loopi 12, 3
    bn.sid x8, 0(x21++)
    addi x8, x8, 1
    nop
  loopi 16, 9
    addi x19, x24, 0
    addi x20, x24, 0
    addi x21, x24, 0
    jal x1, montmul
    loopi 12, 3
      bn.sid x8, 0(x21++)
      addi x8, x8, 1
      nop
    nop
  addi x19, x23, 0
  addi x20, x24, 0
  addi x21, x24, 0
  jal x1, montmul
  bn.add w31, w31, w31 << 0, FG0
  li x17, 16
  loopi 12, 5
    bn.movr x11, x8++
    bn.lid x9, 0(x16++)
    bn.subb w2, w2, w3 << 0, FG0
    bn.movr x17++, x11
    nop
  csrrs x2, 1984, x0
  andi x2, x2, 1
  li x8, 4
  bne x2, x0, label_0
  li x8, 16
  label_0:
  addi x21, x24, 0
  loopi 12, 3
    bn.sid x8, 0(x21++)
    addi x8, x8, 1
    nop
  ret

.globl montmul
montmul:
  bn.lid x9, 0(x17)
  bn.mov w2, w31
  loopi 12, 2
    bn.movr x10++, x11
    nop
  loopi 12, 7
    bn.lid x11, 0(x20++)
    addi x6, x16, 0
    addi x7, x19, 0
    jal x1, mont_loop
    addi x16, x6, 0
    addi x19, x7, 0
    nop
  li x8, 4
  li x10, 4
  ret

mont_loop:
  addi x22, x16, 0
  li x12, 30
  li x13, 24
  li x8, 4
  li x10, 4
  bn.lid x12, 0(x19++)
  jal x1, mul256_w30xw2
  bn.movr x13, x8++
  bn.add w30, w27, w24 << 0, FG0
  bn.addc w29, w26, w31 << 0, FG0
  bn.mov w25, w3
  jal x1, mul256_w30xw25
  bn.mov w25, w27
  bn.mov w24, w30
  bn.lid x12, 0(x16++)
  jal x1, mul256_w30xw25
  bn.add w27, w27, w24 << 0, FG0
  bn.addc w28, w26, w31 << 0, FG0
  loopi 11, 15
    bn.lid x12, 0(x19++)
    bn.movr x13, x8++
    jal x1, mul256_w30xw2
    bn.add w27, w27, w24 << 0, FG0
    bn.addc w26, w26, w31 << 0, FG0
    bn.add w24, w27, w29 << 0, FG0
    bn.addc w29, w26, w31 << 0, FG0
    bn.lid x12, 0(x16++)
    jal x1, mul256_w30xw25
    bn.add w27, w27, w24 << 0, FG0
    bn.addc w26, w26, w31 << 0, FG0
    bn.add w24, w27, w28 << 0, FG0
    bn.addc w28, w26, w31 << 0, FG0
    bn.movr x10++, x13
    nop
  bn.add w24, w29, w28 << 0, FG1
  bn.movr x10++, x13
  bn.add w31, w31, w31 << 0, FG0
  csrrs x2, 1985, x0
  andi x2, x2, 1
  beq x2, x0, label_1
  li x12, 30
  li x13, 24
  addi x16, x22, 0
  li x8, 4
  loopi 12, 5
    bn.lid x13, 0(x16++)
    bn.movr x12, x8
    bn.subb w24, w30, w24 << 0, FG0
    bn.movr x8++, x13
    nop
  label_1:
  li x8, 4
  li x10, 4
  ret

mul256_w30xw2:
  bn.mulqacc.z w30.0, w2.0, 0
  bn.mulqacc w30.1, w2.0, 64
  bn.mulqacc.so w27.L, w30.0, w2.1, 64, FG0
  bn.mulqacc w30.2, w2.0, 0
  bn.mulqacc w30.1, w2.1, 0
  bn.mulqacc w30.0, w2.2, 0
  bn.mulqacc w30.3, w2.0, 64
  bn.mulqacc w30.2, w2.1, 64
  bn.mulqacc w30.1, w2.2, 64
  bn.mulqacc.so w27.U, w30.0, w2.3, 64, FG0
  bn.mulqacc w30.3, w2.1, 0
  bn.mulqacc w30.2, w2.2, 0
  bn.mulqacc w30.1, w2.3, 0
  bn.mulqacc w30.3, w2.2, 64
  bn.mulqacc.so w26.L, w30.2, w2.3, 64, FG0
  bn.mulqacc.so w26.U, w30.3, w2.3, 0, FG0
  ret

mul256_w30xw25:
  bn.mulqacc.z w30.0, w25.0, 0
  bn.mulqacc w30.1, w25.0, 64
  bn.mulqacc.so w27.L, w30.0, w25.1, 64, FG0
  bn.mulqacc w30.2, w25.0, 0
  bn.mulqacc w30.1, w25.1, 0
  bn.mulqacc w30.0, w25.2, 0
  bn.mulqacc w30.3, w25.0, 64
  bn.mulqacc w30.2, w25.1, 64
  bn.mulqacc w30.1, w25.2, 64
  bn.mulqacc.so w27.U, w30.0, w25.3, 64, FG0
  bn.mulqacc w30.3, w25.1, 0
  bn.mulqacc w30.2, w25.2, 0
  bn.mulqacc w30.1, w25.3, 0
  bn.mulqacc w30.3, w25.2, 64
  bn.mulqacc.so w26.L, w30.2, w25.3, 64, FG0
  bn.mulqacc.so w26.U, w30.3, w25.3, 0, FG0
  ret

