.macro init
.endm
.section .text.init
.globl _start
_start:
                  li x0, 0x1
                  li x1, 0x0
                  li x2, 0x4e04f00
                  li x3, 0x80000000
                  li x4, 0x0
                  li x5, 0x0
                  li x6, 0x80000000
                  li x7, 0x0
                  li x8, 0x0
                  li x9, 0x2486412d
                  li x10, 0xf96da636
                  li x11, 0x80000000
                  li x12, 0x0
                  li x13, 0x6a169e6f
                  li x14, 0x0
                  li x15, 0x0
                  li x16, 0x9
                  li x17, 0xecebb53e
                  li x18, 0x80000000
                  li x19, 0x6
                  li x20, 0x0
                  li x21, 0xfd7b9523
                  li x22, 0xf6a1c7ac
                  li x23, 0xf2d48ef9
                  li x24, 0x80000000
                  li x25, 0x3
                  li x26, 0x80000000
                  li x27, 0x80000000
                  li x28, 0x22f2ef4
                  li x29, 0xfdbae154
                  li x30, 0x34168a6f
                  li x31, 0xf1e45ffd
kernel_sp:        
                  la tp, _kernel_stack_end

trap_vec_init:    
                  la a0, mtvec_handler
                  csrw 0x305, a0 # MTVEC

mepc_setup:       
                  la x10, _init
                  csrw mepc, x10
                  j init_machine_mode

_init:            
                  la sp, _user_stack_end
_main:            c.srai     a2, 29
                  lui        zero, 238737
                  lui        s11, 235721
                  auipc      s7, 76889
                  xor        t3, ra, s6
                  c.addi     gp, 29
                  c.addi     a0, -27
                  lui        a2, 384033
                  c.sub      a0, a5
                  c.slli     t1, 28
                  srai       t1, a1, 2
                  auipc      a7, 827597
                  c.slli     t1, 5
                  c.addi     s9, 2
                  c.srli     s0, 26
                  c.srai     s0, 31
                  c.slli     a7, 28
                  nop
                  c.beqz     s0, 23f
                  divu       s5, s3, zero
                  la         t6, data_page_10+2392 #start riscv_load_store_rand_instr_stream_28
                  remu       t4, a1, zero
                  sw         t1, 124(t6)
                  sb         zero, -1935(t6)
                  c.addi     s4, 17
                  sltiu      t5, a6, 801
                  lb         s5, 1505(t6)
                  auipc      a5, 279144
                  lw         a2, 1536(t6)
                  lui        a6, 614242
                  c.srli     s0, 25
                  auipc      t3, 220077
                  c.lui      t3, 28
                  auipc      s0, 305607
                  c.slli     t1, 6
                  c.addi     t1, 22
                  auipc      s7, 871831
                  lb         s4, -1011(t6)
                  c.slli     a2, 15
                  div        zero, s6, s2
                  auipc      s4, 324009
                  c.slli     t5, 29
                  c.lui      t1, 10
                  sh         s9, -952(t6)
                  sb         ra, -1602(t6)
                  lui        s1, 459072
                  c.addi     gp, -29
                  c.lui      s4, 17
                  lb         s1, -1291(t6)
                  c.or       a0, a3
                  auipc      s1, 674641
                  lui        s0, 792087
                  sb         a1, 1581(t6)
                  sb         s8, 378(t6)
                  auipc      s3, 870733
                  lbu        s1, 849(t6)
                  sb         t4, -1621(t6)
                  c.addi     s1, 28
                  lb         s3, 1245(t6)
                  auipc      a2, 410504
                  auipc      gp, 783318
                  lh         t4, -64(t6)
                  lb         gp, -1679(t6)
                  lw         s1, -928(t6)
                  sub        t3, t2, a6
                  lb         a6, 477(t6)
                  c.addi     a3, 12
                  lb         s8, -1681(t6) #end riscv_load_store_rand_instr_stream_28
                  lui        a5, 538415
                  bgeu       sp, s0, 31f
                  mul        s10, t6, s6
23:               auipc      s10, 359030
                  lui        gp, 347341
                  c.andi     a4, -2
                  lui        t6, 399070
                  c.addi     t5, -26
                  c.lui      a0, 11
                  c.slli     a5, 11
                  c.srai     a1, 5
31:               c.srai     s0, 3
                  lui        s1, 610938
                  sltu       t2, sp, t3
                  c.addi     t4, 29
                  sra        a5, t4, s9
                  mulh       a7, s3, s7
                  c.srli     s0, 25
                  c.srli     a1, 27
                  lui        gp, 188064
                  c.or       a5, a0
                  c.srai     a3, 19
                  c.lui      s4, 25
                  blt        s10, s0, 49f
                  fence.i
                  c.addi     a3, 23
                  c.addi     s11, -27
                  c.slli     s2, 6
                  c.lui      t1, 22
49:               c.addi     a0, 16
                  c.andi     a2, 30
                  c.addi     s8, -9
                  slti       a3, s10, 221
                  lui        t5, 395389
                  c.lui      a6, 5
                  lui        t1, 827400
                  c.srai     a2, 18
                  c.addi     s5, -11
                  c.addi     t6, 7
                  c.addi     t6, 18
                  auipc      t2, 473859
                  c.addi     t3, -17
                  xori       s11, s8, 669
                  lui        a1, 173394
                  c.nop
                  c.addi     s10, -19
                  c.addi     s3, 11
                  c.addi     s9, -6
                  c.srli     a5, 20
                  sra        gp, a3, s1
                  lui        s7, 700176
                  sra        t5, t4, s6
                  c.addi     a1, -22
                  c.addi     s8, 11
                  nop
                  c.addi     a4, 17
                  lui        t1, 790428
                  c.slli     s8, 8
                  mulh       s1, t3, tp
                  bne        ra, zero, 86f
                  lui        a6, 8130
                  c.srli     a3, 13
                  c.mv       s11, t3
                  c.or       a2, s1
                  c.srai     s1, 7
                  c.mv       a5, s9
86:               auipc      s7, 819547
                  remu       gp, t5, s11
                  div        a7, s10, s10
                  c.addi     s3, -8
                  c.addi     s3, -12
                  bne        a1, sp, 101f
                  rem        a3, a3, t5
                  c.addi     a4, 16
                  lui        zero, 695379
                  lui        zero, 690954
                  c.addi     s8, -13
                  lui        t4, 388194
                  lui        t2, 218029
                  auipc      a0, 533303
                  c.add      a0, a4
101:              xori       s7, t4, -314
                  c.addi     s8, -27
                  auipc      a3, 448156
                  c.addi     t4, 28
                  c.addi     s2, 25
                  c.srai     s1, 30
                  xori       s5, s2, -427
                  c.and      a2, s0
                  auipc      s2, 697995
                  c.lui      s3, 23
                  auipc      s11, 545666
                  c.sub      s0, s0
                  div        zero, s3, tp
                  divu       t3, gp, s6
                  c.slli     a0, 25
                  remu       t6, s1, s9
                  c.srai     a4, 17
                  c.srli     s0, 14
                  c.srai     a3, 11
                  auipc      a3, 567602
                  mulhsu     s4, a2, s9
                  c.addi     a5, 17
                  auipc      a3, 503184
                  c.lui      t6, 18
                  blt        a5, t1, 140f
                  c.slli     t1, 15
                  c.addi     s0, 26
                  c.addi     gp, 19
                  c.lui      t6, 30
                  auipc      s2, 31723
                  c.lui      s1, 31
                  c.lui      a0, 2
                  c.addi     s7, -30
                  c.addi     a2, -32
                  c.srai     a5, 28
                  c.lui      s3, 22
                  lui        a2, 609043
                  c.addi     a0, 14
                  auipc      t1, 230242
140:              lui        a1, 158565
                  blt        ra, s11, 161f
                  c.slli     s4, 3
                  lui        s9, 379078
                  c.sub      a1, s1
                  c.lui      a2, 3
                  c.addi     t4, 28
                  lui        a2, 1047086
                  c.addi     a4, -28
                  auipc      s4, 228213
                  c.or       s1, a5
                  c.lui      t1, 14
                  lui        t3, 574314
                  c.srai     a0, 7
                  mul        a4, t5, sp
                  c.lui      s7, 27
                  c.bnez     a5, 159f
                  c.lui      a1, 21
                  lui        a2, 674232
159:              auipc      a7, 761974
                  addi       s5, t1, -414
161:              c.mv       s2, s0
                  c.slli     s9, 20
                  c.addi     a5, -18
                  lui        s3, 185509
                  mulhu      s10, t4, t0
                  c.addi     t2, 11
                  c.addi     s8, -20
                  c.addi     a5, 20
                  lui        s0, 374194
                  addi       s9, a4, -839
                  c.srai     s1, 28
                  c.slli     a5, 15
                  slt        t4, t5, t1
                  c.addi     a2, -4
                  mulhu      s11, tp, s3
                  lui        s8, 1008998
                  beq        s4, a4, 193f
                  sra        a2, s9, s10
                  lui        t5, 582185
                  mul        t3, tp, a2
                  auipc      t3, 920837
                  mulhsu     s6, t0, s6
                  c.addi     a7, 8
                  auipc      zero, 1038009
                  c.addi     a4, -28
                  lui        s6, 997119
                  auipc      a3, 779630
                  auipc      s5, 878993
                  c.srli     a2, 29
                  c.addi     t3, -10
                  c.lui      s3, 15
                  auipc      a0, 145555
193:              bgeu       ra, ra, 201f
                  andi       gp, a2, -494
                  c.srai     a2, 15
                  slli       t6, a0, 17
                  c.mv       s10, t5
                  c.addi     s2, 9
                  c.addi     s8, -15
                  c.addi     t2, -10
201:              c.slli     a0, 4
                  c.slli     t2, 1
                  c.beqz     a0, 217f
                  c.addi     s5, -2
                  c.srli     a3, 23
                  c.addi     s11, -6
                  sltiu      t3, t6, -45
                  c.and      s0, a1
                  auipc      s9, 1557
                  c.addi     a5, -28
                  auipc      t4, 5097
                  auipc      t5, 687856
                  addi       s6, s9, -678
                  c.addi     s10, 20
                  c.srai     a5, 8
                  blt        gp, s1, 219f
217:              c.srai     a2, 8
                  auipc      t6, 157471
219:              c.addi     a6, -24
                  c.srai     s1, 9
                  c.addi     s4, 23
                  c.addi     s2, 29
                  auipc      t2, 945652
                  c.addi     a2, 3
                  lui        s6, 212122
                  c.srai     a5, 7
                  c.addi     t2, 6
                  bgeu       a0, s11, 230f
                  c.lui      a4, 30
230:              c.addi     s3, 8
                  auipc      s8, 776288
                  c.addi     t1, -17
                  auipc      s6, 551060
                  bltu       tp, s7, 247f
                  c.addi     a4, -20
                  lui        zero, 658128
                  andi       a4, t1, -764
                  la         a4, data_page_11+2224 #start riscv_load_store_rand_instr_stream_52
                  lbu        s8, 583(a4)
                  lb         t5, -2043(a4)
                  c.addi     t1, -4
                  c.addi     t5, 18
                  lbu        t2, -621(a4)
                  c.addi     s3, -20
                  lh         t4, 1428(a4)
                  lh         t5, 1786(a4)
                  lhu        s3, -2(a4)
                  c.addi     a2, 12
                  lb         t1, 1591(a4)
                  c.or       s1, s1
                  lw         t5, 328(a4)
                  fence
                  lb         s8, 1753(a4)
                  lui        a7, 361756
                  sub        s4, t3, a6
                  lbu        s5, -1997(a4)
                  slli       t6, s2, 29
                  lb         s3, -807(a4)
                  c.srli     a5, 19
                  lb         s4, -1211(a4)
                  lbu        s5, 1593(a4)
                  c.addi     s4, -20
                  auipc      s4, 972420
                  lbu        s4, -898(a4)
                  c.slli     a6, 22
                  c.lui      s0, 11
                  c.addi     t2, 30
                  lbu        s0, 954(a4)
                  lb         s1, 1479(a4)
                  lhu        s8, -1530(a4)
                  rem        t2, a4, s1
                  lbu        a3, 868(a4)
                  lb         t6, -1699(a4)
                  fence.i
                  c.addi     s11, 27
                  mulh       s2, t5, a1
                  rem        t1, t2, s6
                  sh         s3, -1278(a4)
                  c.slli     s2, 5
                  auipc      s10, 96484
                  xori       s5, s1, 54
                  lui        t3, 198499
                  sb         s1, 686(a4)
                  lb         s6, 1559(a4) #end riscv_load_store_rand_instr_stream_52
                  c.addi     a5, 13
                  c.addi     a5, 24
                  auipc      t1, 544505
                  c.addi     s3, -29
                  sra        s7, s9, t3
                  c.srli     s1, 18
                  lui        t6, 1021882
                  c.addi     a0, 21
                  lui        s9, 581582
247:              c.srai     s1, 4
                  lui        s3, 790332
                  c.slli     t2, 21
                  c.slli     a2, 3
                  c.addi     t4, -10
                  c.addi     a7, 31
                  c.srai     a3, 17
                  c.addi     a7, -17
                  auipc      s0, 269048
                  c.srli     a4, 5
                  lui        t1, 602326
                  lui        a6, 371662
                  c.addi     t1, -31
                  lui        gp, 600642
                  c.lui      a0, 28
                  c.addi     a4, 31
                  lui        a5, 311416
                  c.addi     s9, 21
                  sltiu      s1, s0, -72
                  c.lui      t3, 9
                  c.srai     a5, 28
                  lui        a5, 853294
                  c.addi     s3, 3
                  c.addi     s2, 25
                  auipc      s5, 494201
                  c.addi     s5, 16
                  ori        s1, t2, 252
                  c.addi     t1, -12
                  c.addi     s5, -23
                  c.addi     s5, 4
                  lui        t3, 830400
                  c.addi     t4, -27
                  xor        s4, s5, t0
                  srli       a6, a6, 3
                  auipc      a7, 682700
                  and        s8, zero, s6
                  andi       a0, s5, 689
                  c.addi     s1, 9
                  srai       s11, a6, 4
                  lui        a5, 535401
                  c.srai     s0, 3
                  and        a6, t4, a7
                  lui        t1, 260102
                  bgeu       s6, a7, 300f
                  c.addi     s9, 31
                  lui        a1, 376678
                  auipc      s10, 343826
                  c.lui      gp, 5
                  lui        a3, 16797
                  c.addi     s10, 5
                  auipc      s1, 425800
                  c.lui      s10, 23
                  srl        s11, a7, t5
300:              lui        a7, 985039
                  lui        a3, 264571
                  c.addi     s8, -14
                  bltu       zero, a1, 304f
304:              c.srli     s0, 4
                  lui        a0, 694127
                  lui        t6, 416887
                  c.addi     gp, 16
                  c.srai     a3, 8
                  c.addi     t4, 15
                  c.lui      t2, 1
                  c.addi     t6, 5
                  lui        t3, 449411
                  c.addi     s0, -27
                  c.srai     a0, 29
                  auipc      a6, 638349
                  c.slli     t2, 3
                  c.srli     a5, 6
                  blt        s7, s3, 338f
                  c.or       s1, a4
                  c.slli     gp, 5
                  c.addi     s8, 20
                  c.addi     a6, -20
                  c.addi     s8, 4
                  c.srai     s0, 24
                  fence
                  lui        a5, 1046512
                  c.lui      a3, 8
                  c.slli     a1, 16
                  c.addi     t5, 13
                  c.srai     a0, 7
                  c.andi     a5, 10
                  xor        t5, t2, a3
                  auipc      s0, 689803
                  lui        t2, 449359
                  lui        s1, 62087
                  c.srli     a2, 3
                  srli       t5, a3, 26
338:              c.addi     a0, 11
                  c.add      a3, a5
                  c.addi     s2, 31
                  c.addi     s11, -16
                  auipc      a4, 671584
                  c.srli     a3, 25
                  lui        a4, 38256
                  lui        s9, 349156
                  bgeu       s7, t6, 366f
                  c.srai     a5, 4
                  c.nop
                  c.addi     a3, -5
                  c.lui      s1, 16
                  c.srai     a5, 14
                  lui        s5, 447102
                  c.lui      s11, 15
                  bgeu       s7, ra, j__main_sub_2_2 #branch to jump instr
                  lui        s4, 109441
                  c.slli     a1, 11
                  lui        a4, 43748
                  c.addi     s3, 21
                  slti       t1, t4, -304
j__main_sub_2_2:  jal        ra, sub_2
                  lui        s8, 775557
                  beq        gp, s1, 354f
                  c.add      a2, a0
                  lui        s0, 680257
354:              c.addi     a6, 19
                  c.srai     a1, 13
                  c.srai     a3, 3
                  c.srli     a5, 29
                  c.or       a4, s0
                  lui        s10, 4729
                  auipc      s4, 494582
                  c.addi     s8, 26
                  c.li       s1, 4
                  c.lui      s8, 4
                  c.lui      a7, 13
                  lui        a0, 691732
366:              c.addi     t4, -13
                  c.slli     t1, 4
                  c.addi     s1, -14
                  c.srai     a2, 12
                  auipc      t3, 1025792
                  c.addi     s0, 21
                  auipc      a5, 683643
                  srli       a7, t1, 17
                  c.xor      a1, a5
                  and        a3, a0, a7
                  sra        s6, a3, t3
                  c.lui      s11, 7
                  auipc      s9, 950518
                  c.srai     s0, 10
                  bltu       s4, s3, 399f
                  la         s1, data_page_0+1492 #start riscv_load_store_rand_instr_stream_64
                  fence.i
                  auipc      t4, 460297
                  auipc      s5, 418203
                  lbu        t4, 225(s1)
                  lbu        s9, 1409(s1)
                  lb         a3, -791(s1)
                  lb         a1, 723(s1)
                  auipc      gp, 845379
                  sh         s6, -868(s1)
                  c.addi     a4, -2
                  lbu        a1, 1939(s1)
                  lb         t4, -1473(s1)
                  c.srai     a0, 2
                  c.addi     a3, 25
                  c.srai     a3, 17
                  c.or       a1, a1
                  lh         zero, 1266(s1)
                  srl        s9, s1, s4
                  c.srli     a2, 7
                  c.srli     a0, 27
                  c.srli     a0, 18
                  lh         t4, 1228(s1)
                  c.srli     a3, 1
                  lh         s2, -1094(s1)
                  lhu        s8, -1178(s1)
                  c.slli     a5, 21
                  lw         s2, -160(s1)
                  div        s4, gp, s5
                  c.addi     s2, -10
                  lb         s8, -671(s1)
                  lb         t5, 373(s1)
                  lbu        s8, 112(s1)
                  c.srai     a4, 29
                  sb         t6, 1781(s1)
                  lhu        a4, 870(s1)
                  lbu        a3, 863(s1)
                  lb         s7, -633(s1)
                  lbu        s2, -1435(s1)
                  lh         gp, -1020(s1)
                  c.xor      s0, s0
                  sb         s7, 1165(s1)
                  lb         a3, 160(s1)
                  c.addi     s9, 30
                  lhu        t2, -1202(s1)
                  c.slli     s7, 18
                  remu       t1, s4, a6
                  sb         t1, -1266(s1)
                  lb         a1, 547(s1)
                  c.mv       s3, s7
                  lb         a0, 1494(s1)
                  lui        a4, 901233
                  addi       a1, a3, 532
                  lbu        a7, -329(s1) #end riscv_load_store_rand_instr_stream_64
                  bge        s5, t4, 392f
                  c.addi     s0, -11
                  c.addi     a6, -22
                  sltiu      a1, s4, -693
                  c.lui      s0, 10
                  auipc      t2, 187959
                  c.addi     t2, 29
                  auipc      s9, 197709
                  c.slli     gp, 10
                  c.srli     a1, 27
                  c.addi     a0, -21
392:              slli       s11, gp, 13
                  c.addi     t5, -11
                  c.addi     t5, 10
                  slti       t2, ra, 716
                  c.srli     a3, 23
                  c.addi     t1, -22
                  lui        t1, 127783
399:              c.andi     s1, 0
                  c.srli     s0, 17
                  c.addi     a1, 12
                  c.addi     a3, 13
                  c.srli     a4, 19
                  c.lui      a0, 1
                  c.addi     s2, 10
                  auipc      zero, 1022497
                  c.li       a4, -14
                  mulhu      s4, s4, s7
                  auipc      t3, 563250
                  c.slli     s5, 16
                  c.xor      a1, a4
                  c.addi     s7, -1
                  lui        a1, 149662
                  c.lui      s7, 11
                  slli       s4, tp, 9
                  c.srli     a1, 1
                  c.srai     a3, 22
                  lui        s11, 1032940
                  c.srai     s0, 11
                  c.slli     a3, 3
                  auipc      t4, 1028306
                  c.srai     a5, 5
                  lui        a5, 375450
                  lui        a0, 692917
                  auipc      a7, 633069
                  c.slli     s5, 2
                  auipc      s4, 167821
                  c.addi     s4, -19
                  auipc      t5, 944054
                  bgeu       s7, a1, 444f
                  andi       t6, t4, -237
                  c.srai     a5, 10
                  srai       t4, sp, 21
                  c.addi     a7, -11
                  c.srai     a1, 14
                  c.addi     s10, 27
                  c.lui      s1, 18
                  c.srli     a3, 11
                  auipc      s11, 199200
                  and        s4, a6, s8
                  auipc      s2, 107016
                  c.addi     s0, -19
                  auipc      s9, 30280
444:              c.addi     s7, -31
                  bne        t4, tp, 464f
                  or         s1, a4, a2
                  c.lui      s9, 7
                  c.addi     a7, 11
                  remu       s11, t4, a2
                  c.srli     a1, 3
                  c.srli     a2, 14
                  c.addi     a6, -1
                  c.slli     s7, 20
                  srai       a6, t5, 15
                  c.srai     a3, 26
                  c.addi     s11, 6
                  c.addi     s3, -32
                  c.nop
                  mulh       a2, s11, t5
                  c.addi     t4, 24
                  c.srai     a4, 31
                  c.addi     a4, -2
                  srai       s7, ra, 16
464:              auipc      t1, 435844
                  auipc      s10, 100898
                  c.slli     s0, 16
                  auipc      a3, 254598
                  c.addi     s11, 17
                  c.srai     s0, 4
                  auipc      t1, 563972
                  c.addi     a3, 18
                  div        s6, a7, s10
                  c.addi     s4, -4
                  c.srli     a2, 5
                  c.addi     s9, -22
                  auipc      s6, 778876
                  c.addi     a6, -15
                  c.addi     a5, 10
                  lui        zero, 263379
                  c.addi     a5, -29
                  lui        a3, 29651
                  lui        a2, 978869
                  lui        s8, 736912
                  c.addi     s1, -22
                  c.addi     gp, -20
                  c.addi     a1, -4
                  c.lui      a1, 23
                  srli       s11, a1, 23
                  c.addi     a7, 15
                  lui        a4, 828997
                  c.slli     t5, 23
                  c.nop
                  auipc      a7, 61928
                  c.srai     a1, 3
                  c.srai     a0, 14
                  c.addi     s10, -31
                  c.srai     s1, 25
                  c.slli     a4, 15
                  srai       a4, s3, 10
                  lui        s6, 604940
                  c.srli     a5, 7
                  lui        s11, 490326
                  lui        t2, 236336
                  auipc      s7, 193630
                  c.addi     s8, 28
                  c.addi     a2, -32
                  c.addi     t2, -21
                  c.addi     a6, -17
                  c.addi     s11, -1
                  c.lui      s6, 9
                  c.slli     s5, 4
                  fence
                  c.addi     gp, 17
                  c.addi     a5, 7
                  c.srai     a2, 12
                  auipc      a5, 95600
                  auipc      s7, 325515
                  auipc      s7, 395439
                  lui        s3, 17730
                  c.addi     s9, -9
                  c.addi     a1, -26
                  c.addi     a0, -7
                  auipc      t6, 166548
                  c.addi     t1, 29
                  auipc      s8, 557038
                  c.srai     s1, 5
                  auipc      a3, 151841
                  c.addi     t6, 11
                  c.or       a3, a2
                  c.addi     a4, 20
                  c.addi     gp, -14
                  auipc      gp, 685873
                  c.addi     a4, 14
                  c.slli     a5, 8
                  sll        s11, s6, a3
                  sll        s1, s7, a5
                  c.addi     s9, 10
                  c.lui      s2, 5
                  c.slli     a4, 31
                  la         a0, data_page_16+2651 #start riscv_load_store_rand_instr_stream_11
                  lui        s2, 677975
                  lbu        s6, 1266(a0)
                  c.addi     s7, -24
                  auipc      gp, 893098
                  lb         s11, 1291(a0)
                  auipc      a7, 123834
                  sh         s0, -727(a0)
                  c.srai     a4, 17
                  c.addi     t1, 16
                  c.srai     a5, 12
                  auipc      s4, 138483
                  sh         s2, -425(a0)
                  lbu        t3, -1950(a0)
                  c.addi     a7, 26
                  nop
                  lw         s10, -407(a0)
                  lhu        t3, 1033(a0)
                  lb         a7, 604(a0)
                  c.nop
                  auipc      s11, 463200
                  srli       s2, gp, 22
                  lb         a6, -556(a0)
                  srl        a6, s7, s8
                  c.srai     a3, 17
                  sh         s4, 851(a0)
                  auipc      t5, 869023
                  c.addi     a4, 5
                  c.addi     a5, 12
                  c.addi     t6, -32
                  c.addi     s2, 14
                  lbu        s10, -1862(a0)
                  srl        a4, zero, zero
                  slli       s9, t2, 30
                  lui        t1, 758692
                  c.addi     a2, -18
                  lui        a4, 633612
                  sb         a7, -984(a0) #end riscv_load_store_rand_instr_stream_11
                  c.and      s1, s0
                  bltu       a5, s4, 561f
                  sra        t3, t6, zero
                  auipc      s4, 73153
                  c.addi     a5, 21
                  addi       a3, a3, 69
                  lui        s3, 550687
                  c.srai     s1, 4
                  c.srai     a5, 29
                  div        t1, a1, s11
                  c.addi     s5, 30
                  or         a6, zero, ra
                  lui        s5, 182884
                  c.addi     t4, 17
                  c.addi     a7, -20
                  c.addi     t2, -1
                  c.addi     s1, 9
                  xori       s2, s9, 562
                  xor        s6, t0, t1
                  auipc      a0, 429914
                  rem        s10, zero, a6
561:              bltu       s6, s7, 563f
                  div        t6, s11, s11
563:              c.addi     s11, -25
                  nop
                  c.addi     t6, 18
                  c.addi     s3, 13
                  c.addi     gp, 8
                  c.srai     a2, 10
                  lui        a3, 446328
                  c.srai     a1, 7
                  c.addi     t4, 2
                  c.srli     a4, 13
                  c.addi     s7, 15
                  slt        t1, a5, s4
                  c.lui      s2, 3
                  c.srai     a0, 12
                  c.lui      s1, 13
                  c.addi     s3, 4
                  c.srai     a0, 22
                  c.addi     s4, -20
                  c.addi     s2, 11
                  c.slli     a7, 27
                  auipc      a5, 212688
                  c.addi     s5, 4
                  c.srai     a4, 2
                  c.srai     a3, 27
                  c.slli     a7, 25
                  beq        sp, gp, 600f
                  c.or       a1, a4
                  c.addi     s0, 26
                  auipc      s10, 258803
                  c.lui      a2, 4
                  c.srli     s1, 10
                  c.srli     s0, 16
                  c.slli     a1, 18
                  c.sub      s0, a4
                  c.addi     s10, 15
                  lui        a3, 417118
                  auipc      a7, 914260
600:              auipc      s0, 682039
                  c.addi     s7, 27
                  lui        s2, 889859
                  c.slli     a2, 19
                  sltiu      s6, t1, -21
                  c.addi     t1, 5
                  c.addi     s7, -29
                  c.srli     a2, 9
                  c.addi     s4, 12
                  xori       a6, s5, 146
                  c.srai     a3, 10
                  auipc      s6, 422956
                  c.addi     s4, 22
                  c.addi     s0, 12
                  c.srli     a3, 24
                  auipc      t5, 244872
                  c.lui      s8, 13
                  c.lui      s8, 30
                  c.addi     s5, -27
                  fence.i
                  lui        a3, 994628
                  c.addi     t6, -2
                  c.slli     s2, 14
                  c.beqz     a3, 637f
                  auipc      gp, 128473
                  auipc      a1, 437860
                  lui        s5, 229811
                  c.addi     s9, -6
                  c.addi     s3, 3
                  auipc      s6, 243702
                  auipc      s6, 884541
                  c.addi     a3, -31
                  auipc      a6, 820980
                  c.mv       a3, t1
                  c.srli     s0, 8
                  c.addi     s10, -13
                  auipc      zero, 207844
637:              c.srai     s0, 23
                  auipc      s0, 668958
                  c.addi     a2, -9
                  c.srai     s1, 28
                  ori        a2, a6, -807
                  bltu       a6, zero, 656f
                  slti       a2, t2, -769
                  auipc      a2, 891048
                  c.addi     s0, 4
                  c.slli     a7, 11
                  srai       s4, s0, 19
                  c.andi     a0, 14
                  c.slli     s8, 25
                  c.andi     s0, -15
                  auipc      t4, 219980
                  c.addi     t2, 21
                  sra        s2, s5, a6
                  c.slli     s2, 26
                  auipc      t4, 264867
656:              lui        a1, 690306
                  c.slli     gp, 9
                  c.srai     a1, 18
                  c.slli     s4, 20
                  mulh       zero, a1, s3
                  blt        s6, s4, 679f
                  auipc      s4, 1046395
                  lui        s8, 880860
                  c.lui      a7, 7
                  c.slli     t1, 3
                  c.addi     a0, -28
                  c.addi     a0, 4
                  c.slli     t5, 25
                  lui        a2, 384207
                  c.lui      a7, 4
                  fence
                  add        zero, s0, gp
                  srli       gp, a6, 24
                  lui        a4, 54286
                  beq        s4, a3, 678f
                  divu       s7, a7, a3
                  c.addi     a5, -26
678:              c.lui      s1, 8
679:              blt        s0, t0, 688f
                  c.addi     s0, -22
                  c.slli     t4, 7
                  c.slli     t1, 19
                  srli       s11, a0, 1
                  lui        a5, 236700
                  sltu       s1, a7, s8
                  c.slli     s1, 7
                  auipc      s8, 932021
688:              c.addi     s5, 15
                  c.srli     a2, 26
                  lui        s8, 877764
                  c.srli     a0, 14
                  c.lui      s7, 9
                  c.srai     s0, 15
                  bge        sp, a6, 709f
                  c.addi     a0, -17
                  rem        s2, t3, s7
                  c.addi     s9, -24
                  c.srli     s1, 18
                  lui        s5, 678544
                  c.addi     a3, -6
                  lui        zero, 526443
                  lui        s5, 163422
                  c.addi     s0, 28
                  add        a7, s0, a0
                  auipc      zero, 298302
                  lui        s0, 922806
                  div        s0, ra, a7
                  c.slli     a1, 6
709:              c.and      a0, a2
                  auipc      a7, 329824
                  c.addi     a4, 26
                  c.srai     s0, 1
                  auipc      a5, 956672
                  auipc      t5, 543404
                  mulh       a0, t6, t5
                  auipc      a4, 1037276
                  lui        a3, 682997
                  c.addi     s10, -17
                  mul        t1, a1, s6
                  auipc      zero, 465779
                  c.addi     a4, 6
                  nop
                  c.addi     t1, 31
                  c.addi     s4, 9
                  c.slli     a7, 1
                  auipc      s4, 389515
                  auipc      zero, 831625
                  auipc      gp, 95212
                  auipc      zero, 860212
                  mulhu      a3, s8, s2
                  auipc      s0, 812022
                  c.addi     a6, -27
                  lui        a1, 63596
                  c.srli     a0, 3
                  auipc      t4, 99309
                  lui        a5, 38321
                  c.addi     s5, 7
                  c.slli     t6, 3
                  lui        s9, 278381
                  c.srai     s0, 14
                  srl        s7, t2, s3
                  auipc      a5, 780951
                  c.lui      t1, 21
                  lui        gp, 221602
                  c.slli     s6, 14
                  c.nop
                  auipc      t5, 415099
                  c.slli     gp, 29
                  bltu       tp, t0, j__main_sub_1_1 #branch to jump instr
                  c.srai     s1, 24
                  c.slli     gp, 6
j__main_sub_1_1:  jal        ra, sub_1
                  c.addi     s8, 7
                  c.srai     s0, 4
                  c.srli     a5, 15
                  auipc      t4, 634659
                  sub        s6, s3, sp
                  lui        a7, 762190
                  xori       s9, t2, 256
                  srli       a7, s2, 15
                  lui        s8, 237823
                  c.beqz     a4, 757f
                  c.addi     a7, -10
                  sub        s9, s9, s1
                  blt        a6, s0, 775f
                  c.srai     a5, 5
757:              lui        a1, 944155
                  c.addi     a7, -12
                  c.addi     s7, -14
                  c.addi     t6, 21
                  nop
                  c.addi     s8, 24
                  c.addi     t2, -25
                  c.addi     s7, -8
                  c.lui      gp, 8
                  c.addi     t2, -13
                  mul        s6, a4, s2
                  c.lui      a2, 8
                  addi       t3, a5, -87
                  sll        a2, a5, s5
                  beq        t0, s4, 785f
                  c.addi     gp, -21
                  lui        a2, 61344
                  mulh       s4, a5, s3
775:              c.addi     s1, 26
                  c.and      a0, a0
                  auipc      a0, 687384
                  c.addi     t5, -32
                  c.srai     a1, 20
                  c.beqz     s0, 792f
                  c.addi     s4, -10
                  c.addi     s5, -23
                  c.mv       t4, s6
                  c.addi     a5, -11
785:              srli       s1, a3, 8
                  c.addi     s7, -26
                  c.addi     t6, -17
                  c.addi     s0, 13
                  lui        t5, 974165
                  c.add      a4, a1
                  slt        t1, t0, ra
792:              c.addi     s7, -6
                  auipc      s4, 235522
                  lui        s9, 920086
                  lui        a7, 225536
                  c.srai     a3, 15
                  c.addi     a6, -10
                  auipc      zero, 32660
                  lui        s9, 239905
                  c.srai     a5, 5
                  c.addi     a4, 14
                  mulhu      t2, t5, a2
                  c.slli     s11, 11
                  mulh       a7, a3, a3
                  auipc      s9, 682405
                  auipc      s1, 749015
                  mulhu      s2, a3, a4
                  c.addi     s11, 24
                  c.slli     t2, 9
                  auipc      s2, 103002
                  c.mv       a1, t2
                  mulhsu     s1, a0, sp
                  lui        zero, 330455
                  c.addi     a3, 22
                  c.srai     a2, 17
                  or         s5, s6, s2
                  c.addi     t5, -28
                  lui        t1, 186801
                  xor        t3, t6, s5
                  c.srli     a5, 23
                  c.slli     t2, 31
                  c.srai     a0, 7
                  c.lui      gp, 12
                  bne        t3, a0, 832f
                  c.srai     a4, 3
                  c.srli     a1, 23
                  auipc      s10, 268917
                  auipc      t5, 673960
                  c.srai     a0, 29
                  c.srli     a4, 17
                  c.srli     a4, 10
832:              c.srai     s1, 11
                  c.slli     s5, 11
                  slti       s10, s8, 715
                  c.addi     s9, -28
                  c.addi     t5, -18
                  c.addi     a7, 24
                  lui        t4, 677639
                  auipc      gp, 486315
                  c.bnez     a2, 846f
                  lui        a2, 604350
                  c.addi     s7, -12
                  c.lui      s11, 21
                  c.addi     t1, -19
                  sra        s11, a5, t5
846:              c.srli     a4, 17
                  c.lui      a3, 19
                  c.addi     t1, -18
                  c.addi     a2, 28
                  c.slli     s5, 11
                  auipc      s10, 66254
                  auipc      zero, 361722
                  c.addi     a4, 25
                  c.addi     a5, -25
                  bne        a1, a2, 865f
                  auipc      s8, 675017
                  c.addi     a2, 24
                  fence
                  c.addi     a0, -29
                  c.addi     a4, -3
                  slli       zero, t1, 17
                  lui        zero, 638282
                  c.or       a1, a3
                  lui        a0, 967671
865:              lui        s3, 141214
                  c.lui      t6, 3
                  c.srli     a3, 24
                  c.addi     s8, 17
                  c.nop
                  c.addi     s11, -5
                  lui        a4, 263199
                  c.srli     a0, 9
                  c.nop
                  c.srai     s0, 8
                  c.srli     a2, 18
                  c.slli     s9, 8
                  srli       t5, a0, 2
                  c.slli     s11, 8
                  c.addi     t6, -4
                  auipc      zero, 188225
                  c.addi     t5, -10
                  div        s10, ra, t4
                  c.srai     a0, 7
                  c.addi     s8, 17
                  srai       t3, sp, 14
                  c.addi     t4, 2
                  c.addi     a1, 30
                  lui        t3, 259752
                  lui        s1, 139287
                  lui        t4, 950285
                  lui        s6, 825854
                  auipc      s0, 702119
                  c.addi     s4, -12
                  lui        a1, 236741
                  slti       zero, t2, 363
                  c.addi     s11, -23
                  c.srli     a3, 28
                  c.slli     s8, 8
                  c.srai     a5, 5
                  c.addi     t3, 12
                  c.lui      s0, 6
                  c.slli     t1, 21
                  sra        s0, zero, s4
                  c.addi     t2, 18
                  c.slli     s5, 11
                  lui        a7, 719474
                  c.lui      t4, 25
                  c.srai     a2, 8
                  auipc      a0, 755032
                  lui        t3, 676474
                  c.srai     a4, 9
                  c.srli     a5, 7
                  auipc      s11, 447190
                  lui        t2, 1787
                  c.srli     a0, 25
                  c.addi     s2, -21
                  auipc      s10, 511423
                  c.lui      a2, 4
                  c.xor      a3, a0
                  c.addi     t1, 22
                  slti       s11, t0, -210
                  blt        t3, s7, 939f
                  auipc      s1, 794184
                  lui        zero, 741657
                  c.srai     a5, 10
                  c.srli     a0, 18
                  c.srli     a1, 7
                  bne        t1, a2, 933f
                  c.addi     gp, 22
                  c.addi     s9, 29
                  lui        t4, 466063
                  c.srli     a1, 29
933:              c.slli     s8, 18
                  c.lui      a7, 31
                  divu       a5, a4, a5
                  c.addi     s1, 4
                  c.slli     s6, 2
                  c.addi     s11, 24
939:              c.addi     gp, 4
                  c.addi     a4, -23
                  c.addi     t3, 14
                  c.addi     s6, 9
                  c.and      a3, a3
                  and        a3, a5, s3
                  c.lui      t5, 15
                  c.addi     s9, 31
                  c.slli     s6, 1
                  c.srai     a5, 21
                  auipc      s11, 896169
                  c.addi     s1, 24
                  c.slli     s4, 18
                  lui        t2, 492633
                  mulhu      a5, sp, s7
                  c.srli     a1, 26
                  c.lui      t3, 9
                  lui        t5, 694853
                  auipc      s0, 446961
                  c.nop
                  c.lui      s4, 8
                  c.srli     a2, 16
                  c.addi     s7, -23
                  c.addi     s1, 22
                  c.slli     t4, 28
                  slli       s1, tp, 3
                  c.slli     s11, 12
                  c.srli     a0, 8
                  c.addi     t3, 6
                  srai       s7, s5, 12
                  c.addi     a7, -5
                  c.lui      s9, 1
                  srl        s10, t4, s4
                  c.addi     s5, -22
                  lui        s6, 165197
                  lui        s8, 808861
                  lui        s9, 447092
                  sltu       t5, zero, zero
                  c.lui      t5, 4
                  c.or       a0, s0
                  c.xor      a1, a0
                  auipc      s6, 1024152
                  c.slli     s4, 9
                  auipc      t2, 207620
                  c.lui      t5, 11
                  c.beqz     a5, 988f
                  la         s11, data_page_1+2630 #start riscv_load_store_rand_instr_stream_4
                  sb         t3, 269(s11)
                  c.srai     a1, 17
                  sb         t3, -1121(s11)
                  lbu        a7, 323(s11)
                  lbu        a0, -207(s11)
                  lbu        s7, -1223(s11)
                  lui        t4, 261232
                  lb         a3, -1241(s11)
                  lb         a1, -1546(s11)
                  c.addi     s2, -17
                  sltu       s10, s7, a5
                  sh         a1, -864(s11)
                  sb         s2, 672(s11)
                  sb         s3, 1241(s11)
                  sb         gp, -1245(s11)
                  lbu        t2, -1179(s11)
                  lbu        s7, 1107(s11)
                  slt        gp, t3, s0
                  lbu        a6, -1658(s11)
                  lh         s7, 1182(s11)
                  c.add      a3, s0
                  c.addi     s3, 1
                  c.slli     s3, 3
                  c.srli     a5, 31
                  lbu        t3, 33(s11)
                  lui        a5, 483618
                  c.addi     a6, 23
                  c.andi     a1, -3
                  nop
                  auipc      a5, 507618
                  c.srli     a4, 24
                  sw         a7, 1026(s11)
                  c.slli     t2, 11
                  lw         a2, -206(s11)
                  c.addi     t4, -8
                  lbu        s7, 1025(s11)
                  sb         s8, 1309(s11)
                  c.addi     s2, 23
                  lb         a3, -793(s11)
                  sb         t1, -1806(s11)
                  lb         t3, -1075(s11)
                  sb         s5, -1091(s11)
                  sb         a6, 1417(s11)
                  sb         t6, -1125(s11)
                  lbu        a7, -488(s11) #end riscv_load_store_rand_instr_stream_4
                  c.srli     s0, 26
                  c.addi     s2, -6
                  c.addi     s10, -19
988:              c.beqz     s0, 999f
                  auipc      s6, 413318
                  c.lui      t6, 15
                  c.addi     s5, -16
                  c.lui      s11, 1
                  lui        s9, 279039
                  sltiu      t4, a2, -410
                  c.addi     s10, 15
                  lui        a6, 6368
                  auipc      a1, 1006566
                  fence
999:              slt        t6, t5, a4
                  c.addi     a3, 5
                  beq        t4, t6, 1016f
                  rem        a7, t1, t2
                  lui        a2, 99607
                  c.slli     s0, 8
                  c.slli     s11, 12
                  c.addi     a6, -24
                  la         s11, data_page_5+1543 #start riscv_load_store_rand_instr_stream_7
                  c.srli     a2, 27
                  lbu        s1, 1577(s11)
                  lhu        s8, -811(s11)
                  lbu        t1, 530(s11)
                  c.srli     s1, 25
                  lb         a7, 1709(s11)
                  c.lui      s0, 4
                  lbu        s7, 1788(s11)
                  c.lui      s9, 27
                  sb         a0, 140(s11)
                  lb         t3, -1528(s11)
                  lbu        s9, 1722(s11)
                  lhu        s3, 1435(s11)
                  sb         sp, -428(s11)
                  sb         ra, 408(s11)
                  sra        s5, t5, t5
                  sb         s9, 118(s11)
                  sb         t1, -1417(s11)
                  auipc      s10, 207075
                  c.srli     a0, 19
                  lui        s10, 96014
                  c.srli     s1, 19
                  c.addi     s8, -30
                  lh         a7, -1063(s11)
                  nop
                  mulh       t6, zero, t5
                  sh         t1, 2009(s11)
                  sb         s8, -740(s11)
                  lbu        s2, 596(s11)
                  sb         t3, 640(s11)
                  lb         s7, 675(s11)
                  lh         s4, 863(s11)
                  lbu        s2, 28(s11)
                  lhu        t2, -521(s11)
                  sb         s6, -558(s11)
                  c.or       s0, a3
                  lhu        s1, 1983(s11)
                  lb         a7, 1213(s11)
                  sh         a0, 1313(s11)
                  lb         a6, -778(s11) #end riscv_load_store_rand_instr_stream_7
                  lui        s8, 790887
                  c.lui      a5, 9
                  c.addi     s11, -9
                  c.nop
                  c.addi     s9, 10
                  c.addi     s11, -30
                  beq        s7, t5, 1019f
                  c.srli     s0, 16
                  c.slli     t1, 24
1016:             c.srai     a5, 7
                  lui        a0, 331489
                  c.lui      a1, 20
1019:             ori        s8, s11, -589
                  c.srli     a1, 24
                  c.addi     a1, -6
                  c.srli     a2, 1
                  fence.i
                  c.slli     t3, 30
                  auipc      a1, 683881
                  auipc      t4, 119934
                  c.addi     a6, -8
                  c.srai     a5, 10
                  c.lui      t2, 22
                  or         gp, t4, a1
                  c.addi     a2, 6
                  c.slli     s5, 9
                  c.addi     s8, -14
                  slti       s10, t2, -728
                  auipc      s5, 866547
                  lui        a6, 120865
                  c.addi     s3, -22
                  c.srai     s1, 11
                  lui        a5, 42815
                  c.addi     a5, -28
                  auipc      s9, 1011478
                  auipc      a7, 441599
                  div        s7, s3, t2
                  la         s2, data_page_1+1724 #start riscv_load_store_rand_instr_stream_20
                  c.addi     s1, 15
                  sb         t5, -645(s2)
                  sh         t5, 282(s2)
                  c.addi     t3, 30
                  sb         t5, -1653(s2)
                  lbu        a6, -469(s2)
                  c.lui      s0, 23
                  sb         t2, 1893(s2)
                  lbu        a1, 556(s2)
                  c.addi     s4, -16
                  sh         s10, -1342(s2)
                  c.xor      a4, s1
                  sb         s7, -1562(s2)
                  auipc      t6, 708188
                  sw         s6, -148(s2)
                  c.addi     t6, 22
                  lui        t2, 348584
                  or         s0, zero, s2
                  lbu        t5, 85(s2)
                  c.srai     a4, 29
                  lb         a1, 1610(s2)
                  c.add      a5, a5
                  lui        t6, 1041524
                  slli       zero, t2, 23
                  sb         t5, 73(s2)
                  sh         t6, -306(s2)
                  c.srli     a1, 4
                  mul        a4, ra, s5
                  sb         a2, 388(s2)
                  auipc      a6, 913922
                  c.lui      gp, 28
                  lui        s9, 962267
                  auipc      s1, 996200
                  lbu        s9, -59(s2) #end riscv_load_store_rand_instr_stream_20
                  c.addi     s0, -19
                  auipc      a4, 222235
                  addi       s6, t4, 1017
                  lui        s9, 702747
                  c.slli     t5, 27
                  c.addi     s8, 11
                  c.addi     a3, -11
                  sra        t4, t5, a3
                  c.srai     a5, 8
                  c.addi     s11, -4
                  c.slli     a3, 6
                  c.addi     s6, 5
                  c.srai     a2, 31
                  lui        s7, 671113
                  auipc      gp, 704043
                  lui        a2, 368874
                  c.addi     s3, 23
                  auipc      a6, 330102
                  c.addi     t5, -3
                  c.srai     a2, 19
                  c.lui      t5, 1
                  c.addi     s0, -28
                  c.add      s1, a2
                  lui        s11, 455321
                  c.beqz     a1, 1069f
1069:             c.addi     t4, 29
                  sltiu      s8, s10, 1015
                  c.addi     s9, 12
                  auipc      t5, 804000
                  bltu       s0, s0, 1075f
                  c.srli     a1, 8
1075:             c.lui      s0, 25
                  c.addi     s3, -3
                  auipc      s8, 652640
                  c.beqz     s1, 1087f
                  c.srai     a4, 5
                  c.slli     s7, 18
                  lui        s8, 795346
                  lui        a3, 693738
                  lui        s0, 166776
                  c.srli     a2, 19
                  c.lui      s3, 24
                  c.srai     s1, 3
1087:             andi       zero, a5, -399
                  lui        s11, 367858
                  bgeu       t5, a6, 1108f
                  c.slli     t5, 15
                  c.srai     s0, 10
                  lui        s3, 784594
                  c.slli     s1, 11
                  c.slli     a0, 18
                  c.bnez     a3, 1112f
                  auipc      s10, 681744
                  lui        a6, 641348
                  or         s10, t4, tp
                  sra        a7, ra, s5
                  sub        s6, a2, s2
                  c.addi     s6, 17
                  c.srai     s0, 13
                  auipc      a5, 462929
                  c.srai     a2, 12
                  lui        s7, 1043471
                  c.add      a3, a0
                  c.slli     s4, 14
1108:             c.srli     a3, 22
                  c.srli     a5, 31
                  c.srai     s1, 30
                  lui        s8, 520317
1112:             srli       a7, s11, 6
                  c.addi     s7, -7
                  c.addi     s11, 23
                  lui        s6, 907921
                  c.sub      a4, s0
                  lui        a1, 1013181
                  c.addi     a0, -23
                  c.addi     t6, -8
                  auipc      t1, 937048
                  c.addi     s6, -31
                  c.addi     t5, -10
                  lui        a7, 64308
                  sltu       s4, a1, s1
                  c.addi     s2, 20
                  auipc      s7, 803028
                  c.addi     s2, 4
                  c.slli     a6, 25
                  and        gp, a5, a2
                  lui        s9, 101155
                  c.addi     s10, 20
                  auipc      a1, 871498
                  c.slli     a5, 26
                  or         a1, s11, gp
                  c.srai     s0, 19
                  c.srai     a0, 14
                  c.li       s5, 17
                  c.addi     s6, -20
                  srai       t5, s9, 3
                  c.addi     s2, 28
                  auipc      s9, 839827
                  lui        s9, 938338
                  c.addi     a7, -3
                  c.lui      t5, 13
                  c.addi     s1, -15
                  fence.i
                  c.srai     s1, 26
                  lui        t5, 801837
                  c.addi     a6, 15
                  c.slli     t5, 19
                  c.srai     a4, 26
                  fence
                  c.addi     s11, 11
                  c.addi     t6, 8
                  lui        gp, 614888
                  c.addi     s11, 9
                  c.slli     t1, 21
                  lui        a6, 458400
                  c.addi     t2, 5
                  c.bnez     a5, 1166f
                  c.addi     gp, 25
                  c.sub      a3, a4
                  c.addi     s7, 19
                  c.addi     a5, -8
                  xori       a5, t3, -60
1166:             c.srai     a4, 15
                  c.and      a3, a4
                  lui        t1, 378074
                  auipc      s5, 759562
                  auipc      s1, 134935
                  c.srli     a3, 23
                  c.xor      a5, a5
                  nop
                  ori        s4, s8, -172
                  c.addi     s2, 17
                  lui        t5, 836223
                  auipc      s11, 931116
                  lui        a4, 800192
                  c.srai     s1, 1
                  lui        s6, 464928
                  c.addi     a2, -4
                  c.addi     a6, 28
                  c.srai     a2, 19
                  c.addi     s2, -7
                  c.addi     s8, 28
                  lui        s5, 836100
                  c.addi     a5, -23
                  beq        a4, s1, 1205f
                  lui        t6, 728693
                  c.addi     s5, 16
                  srli       a3, t6, 5
                  auipc      a5, 332743
                  c.lui      s8, 23
                  c.slli     s6, 5
                  c.addi     gp, -13
                  ori        t1, a2, -508
                  c.slli     s7, 31
                  lui        t1, 8942
                  la         s8, data_page_13+2421 #start riscv_load_store_rand_instr_stream_14
                  c.addi     a4, 2
                  lb         s3, -799(s8)
                  sb         a2, -1278(s8)
                  c.lui      a2, 11
                  c.srai     a0, 29
                  lui        t6, 695772
                  addi       a1, a7, 928
                  auipc      t2, 91169
                  c.addi     gp, -9
                  lbu        t4, -1367(s8)
                  mul        a6, t0, a2
                  c.addi     a4, -16
                  lui        s6, 728944
                  sb         a2, 1643(s8)
                  lui        s10, 984077
                  nop
                  lb         s0, 221(s8)
                  lui        gp, 622819
                  slli       a4, s0, 31
                  lbu        s6, 186(s8)
                  lh         zero, 301(s8)
                  sra        s11, zero, gp
                  c.lui      s9, 20
                  sb         s1, 79(s8)
                  xor        t5, s4, s3
                  sra        a2, t2, a0
                  sb         a5, 694(s8)
                  lb         s3, -57(s8)
                  lui        a5, 931897
                  c.addi     t6, -29
                  divu       s10, s2, a2
                  c.addi     a3, 10
                  c.addi     a4, 6
                  lb         s2, 607(s8) #end riscv_load_store_rand_instr_stream_14
                  div        s8, s11, zero
                  mulh       a1, zero, gp
                  c.lui      a0, 9
                  c.slli     t5, 20
                  c.slli     s3, 15
                  c.slli     s4, 7
1205:             and        s9, t1, a4
                  c.lui      a1, 6
                  auipc      t2, 1034334
                  c.sub      s0, a2
                  c.addi     a7, -18
                  sra        s5, s7, a0
                  c.addi     s8, 6
                  c.addi     a3, -8
                  c.srli     a3, 28
                  c.addi     t1, 7
                  c.addi     s4, -29
                  c.addi     t6, 16
                  auipc      s10, 525781
                  auipc      t3, 1018180
                  auipc      s6, 895265
                  auipc      s1, 60492
                  and        s3, ra, a4
                  c.slli     s9, 20
                  c.lui      t2, 2
                  c.srai     a4, 23
                  c.addi     a2, -4
                  slli       t2, s0, 6
                  c.addi     t2, 9
                  c.lui      s3, 10
                  auipc      a5, 300851
                  c.lui      a4, 8
                  c.addi     s7, -1
                  c.addi     s11, -3
                  c.srai     a1, 30
                  c.srli     s0, 3
                  c.srli     s0, 7
                  c.srai     a5, 27
                  c.addi     t6, -22
                  la         s11, data_page_0+1771 #start riscv_load_store_rand_instr_stream_30
                  lb         s2, -461(s11)
                  c.lui      s7, 23
                  lh         s10, 523(s11)
                  lbu        s8, 288(s11)
                  lw         s3, -187(s11)
                  lhu        s1, 1063(s11)
                  c.slli     a2, 7
                  lb         s1, -270(s11)
                  lh         s7, -7(s11)
                  lb         t3, 1190(s11)
                  lbu        t1, 1782(s11)
                  c.addi     t1, 7
                  lbu        s4, 693(s11)
                  c.slli     a4, 26
                  c.addi     a0, 23
                  c.xor      s0, a0
                  auipc      a6, 317523
                  lb         s6, -1450(s11)
                  andi       gp, s6, -613
                  sb         s4, 1970(s11)
                  c.srli     a2, 24
                  lbu        a6, -734(s11)
                  auipc      s4, 276395
                  sra        s6, a1, a5
                  sw         tp, -1231(s11)
                  lh         a4, 1347(s11)
                  lbu        a3, -907(s11)
                  sb         t5, 1263(s11)
                  lb         t6, -1355(s11)
                  sb         t6, 1429(s11)
                  sb         t2, 1749(s11)
                  c.addi     a2, 21
                  lhu        a0, 1523(s11)
                  c.addi     s7, 22
                  c.slli     gp, 14
                  lhu        a7, -825(s11)
                  lh         t4, 1491(s11)
                  sltu       t1, a7, s7
                  c.addi     s0, -2
                  c.li       a2, -23
                  sb         s10, -1102(s11)
                  c.srai     a0, 8
                  lbu        s9, 1654(s11)
                  sb         s0, 272(s11)
                  lbu        s9, 1292(s11) #end riscv_load_store_rand_instr_stream_30
                  auipc      a6, 848854
                  lui        s3, 472616
                  c.addi     s8, 10
                  c.lui      a3, 3
                  lui        s1, 849718
                  c.srai     a4, 9
                  c.addi     t5, -31
                  divu       s7, s3, zero
                  c.srli     a3, 24
                  c.slli     t1, 25
                  auipc      s9, 72748
                  or         s9, ra, s2
                  c.addi     t5, 21
                  lui        a2, 987006
                  c.addi     a7, -5
                  c.addi     s9, -5
                  div        a1, zero, s4
                  divu       a6, s0, a3
                  auipc      a4, 68096
                  bgeu       s7, t5, 1276f
                  sltiu      s0, a2, -974
                  c.srai     a4, 9
                  c.addi     a2, -27
                  lui        a1, 86752
                  c.addi     s1, 25
                  c.slli     a2, 26
                  lui        gp, 548602
                  c.srai     a3, 10
                  c.bnez     a3, 1270f
                  c.mv       t2, a3
                  c.lui      t1, 8
                  c.addi     s5, -5
1270:             add        a3, sp, a0
                  lui        s0, 842855
                  c.srai     s1, 22
                  lui        a0, 986239
                  c.li       s8, -7
                  lui        t4, 844279
1276:             mul        s11, gp, s3
                  c.addi     t4, 4
                  fence.i
                  auipc      a3, 680069
                  c.lui      s10, 8
                  auipc      t1, 486570
                  c.addi     t2, 22
                  c.addi     s7, 20
                  lui        a7, 399143
                  lui        s9, 115047
                  auipc      s8, 164519
                  c.slli     s11, 12
                  c.addi     s4, 18
                  bgeu       a5, s5, 1306f
                  auipc      s11, 939445
                  c.lui      a2, 20
                  c.nop
                  c.srli     a3, 11
                  c.slli     s3, 7
                  c.beqz     a1, 1304f
                  bltu       s8, s5, 1298f
                  c.srli     s0, 13
1298:             c.and      a2, s1
                  c.lui      a5, 12
                  mul        s1, t5, a5
                  c.srli     s0, 26
                  c.addi     a7, -6
                  c.slli     s0, 27
1304:             auipc      s9, 44757
                  c.srli     a1, 6
1306:             c.sub      a1, a1
                  c.lui      gp, 12
                  and        t3, gp, s11
                  xori       a5, s5, -955
                  c.lui      a1, 20
                  c.xor      a4, a5
                  auipc      a5, 935577
                  c.addi     s9, -10
                  fence.i
                  xor        s3, tp, sp
                  srl        s4, t3, s2
                  c.slli     gp, 29
                  c.srai     s1, 31
                  bge        s0, t1, 1329f
                  c.addi     t4, -29
                  c.nop
                  c.addi     s2, 17
                  la         a0, data_page_12+1825 #start riscv_load_store_rand_instr_stream_62
                  sh         t4, -723(a0)
                  lbu        s11, 1892(a0)
                  lh         s2, 443(a0)
                  lbu        t4, 357(a0)
                  xori       s8, s3, 339
                  auipc      s0, 434421
                  lbu        gp, -1063(a0)
                  sh         s9, -1611(a0)
                  andi       a1, s0, 244
                  mul        a5, sp, a5
                  c.slli     s8, 5
                  lb         t3, 402(a0)
                  auipc      s2, 779977
                  lb         a4, 189(a0)
                  lui        s0, 1007077
                  c.addi     s6, 3
                  sb         s3, -455(a0)
                  c.addi     t2, -7
                  c.addi     s0, -21
                  lhu        s3, -1435(a0)
                  auipc      t2, 1041398
                  auipc      gp, 757890
                  lbu        a1, -380(a0)
                  lb         s0, 1456(a0)
                  lbu        s1, -215(a0)
                  c.slli     a6, 27
                  c.lui      a3, 5
                  sb         t6, 1604(a0)
                  lbu        s8, -973(a0)
                  sb         t1, 717(a0)
                  c.addi     gp, 16
                  mulhsu     a6, a6, s4
                  sb         ra, 305(a0)
                  lb         s10, 156(a0)
                  c.lui      s3, 5
                  c.srai     a3, 8
                  c.lui      t1, 22
                  lh         s11, -821(a0) #end riscv_load_store_rand_instr_stream_62
                  auipc      a3, 1029053
                  c.addi     s7, -5
                  auipc      s4, 1005310
                  c.addi     t1, -26
                  c.lui      t5, 5
                  lui        a4, 21081
1329:             c.lui      s7, 22
                  c.addi     a6, 13
                  c.addi     s6, 3
                  c.addi     s7, -11
                  c.srli     a0, 21
                  c.addi     t6, -32
                  c.addi     s2, -7
                  c.addi     t5, 6
                  sub        a5, a6, a5
                  or         t4, tp, s6
                  c.slli     s5, 28
                  div        s11, t6, a2
                  la         s4, data_page_14+1844 #start riscv_load_store_rand_instr_stream_53
                  lb         zero, 182(s4)
                  c.srli     s0, 10
                  lb         t1, -414(s4)
                  lb         t4, -771(s4)
                  sb         tp, -1155(s4)
                  rem        s3, t5, t5
                  lui        s1, 944122
                  c.lui      s2, 19
                  sb         t3, -182(s4)
                  sb         tp, 1819(s4)
                  lw         a0, 336(s4)
                  lhu        s8, 694(s4)
                  lbu        s2, -737(s4)
                  c.slli     a3, 31
                  c.addi     s2, -6
                  sltiu      a0, a7, 77
                  c.addi     s10, -24
                  mulhsu     s6, a6, t0
                  lui        s1, 1044687
                  c.addi     s10, -11
                  lb         t6, 979(s4)
                  auipc      a2, 781810
                  c.lui      s9, 15
                  lb         t3, 411(s4)
                  and        s10, a2, s2
                  lbu        t6, -227(s4)
                  c.srai     s0, 4
                  c.addi     s11, 27
                  sb         zero, 1588(s4)
                  lui        a5, 680568
                  c.li       gp, -13
                  mul        s11, a6, s11
                  lui        gp, 640587
                  c.addi     s3, 1
                  c.lui      a6, 23
                  c.slli     a7, 1
                  c.srai     a2, 15
                  lui        s0, 709472
                  sb         s9, 803(s4)
                  c.addi     a2, 27
                  sb         s1, -499(s4)
                  lui        a2, 249519
                  c.srli     a5, 25
                  lb         s2, 501(s4)
                  auipc      t3, 270073
                  c.addi     s11, -19
                  lbu        s9, -1801(s4)
                  sh         t3, 1206(s4)
                  lbu        a4, -739(s4)
                  lb         a6, -102(s4) #end riscv_load_store_rand_instr_stream_53
                  auipc      s9, 794964
                  c.srli     a2, 8
                  or         a0, a3, a2
                  lui        s1, 179380
                  c.and      s1, s1
                  andi       s5, a5, 816
                  c.addi     t1, 22
                  ori        t4, s11, 634
                  c.slli     t3, 4
                  c.addi     a1, 29
                  sra        s2, a3, s10
                  c.addi     s9, 6
                  c.addi     s3, 14
                  c.addi     t5, -5
                  c.addi     s2, 5
                  lui        a0, 417459
                  c.slli     s7, 9
                  c.lui      s10, 18
                  lui        s10, 830928
                  c.addi     a7, -28
                  lui        a5, 556747
                  auipc      s0, 678597
                  beq        a6, s10, 1364f
1364:             auipc      t4, 61505
                  fence
                  c.srli     s1, 4
                  c.srai     a1, 15
                  c.addi     t4, 9
                  lui        a6, 521290
                  c.xor      a2, a4
                  fence
                  c.addi     s0, -24
                  lui        a5, 875803
                  blt        ra, zero, 1377f
                  c.addi     s3, -16
                  c.addi     s7, 11
1377:             xor        a6, a0, s6
                  c.addi     a3, -26
                  c.slli     a1, 27
                  c.srli     s0, 9
                  remu       t5, s7, gp
                  c.addi     s6, 4
                  c.addi     s4, 15
                  c.addi     t3, -28
                  slli       s0, ra, 15
                  div        a1, s4, ra
                  auipc      s10, 946116
                  slli       s6, s5, 19
                  auipc      a3, 863730
                  c.addi     t4, 2
                  c.addi     s11, -31
                  auipc      a6, 680798
                  c.srai     a4, 21
                  slti       s10, tp, 719
                  lui        t5, 627780
                  bge        s7, a1, 1413f
                  c.sub      a4, a2
                  fence.i
                  c.slli     a5, 4
                  c.lui      s1, 31
                  c.addi     a4, -4
                  srai       s3, a3, 1
                  lui        t6, 982699
                  bge        s11, t2, 1419f
                  c.addi     s0, -5
                  divu       a0, a3, s9
                  c.li       a2, 0
                  auipc      t5, 506679
                  lui        a0, 772363
                  and        s5, a7, gp
                  auipc      a0, 777985
                  auipc      a4, 876749
1413:             c.srai     a2, 25
                  c.addi     s3, 22
                  c.addi     t1, -10
                  sltiu      s4, s9, 941
                  slli       a1, s1, 7
                  lui        a0, 734643
1419:             c.lui      t2, 25
                  c.addi     a2, -18
                  lui        s1, 82773
                  sltiu      a5, t2, -329
                  c.addi     t1, -8
                  auipc      t1, 188875
                  c.lui      t2, 17
                  c.srli     a1, 9
                  c.slli     s10, 8
                  c.addi     s5, 14
                  c.addi     s10, -26
                  c.slli     s0, 6
                  c.addi     a5, 29
                  c.srli     a0, 14
                  c.srai     a3, 8
                  lui        s8, 973427
                  c.addi     t3, 14
                  c.lui      s10, 6
                  c.srli     a1, 29
                  c.slli     gp, 21
                  c.addi     t5, -5
                  c.slli     a6, 20
                  c.srai     s1, 9
                  c.addi     s7, 30
                  c.slli     t3, 7
                  c.addi     s1, -15
                  lui        s11, 599643
                  lui        s7, 104762
                  mulh       s6, a4, gp
                  c.addi     a4, 3
                  c.addi     a3, 23
                  lui        s1, 151454
                  c.lui      s4, 9
                  bge        tp, t2, 1458f
                  bge        s5, a7, 1473f
                  c.slli     a0, 8
                  c.addi     s4, 24
                  c.addi     a1, -31
                  sltiu      a5, s10, -1001
1458:             c.slli     a3, 26
                  add        t3, t5, t2
                  c.addi     s2, 15
                  lui        t4, 593590
                  c.srli     s0, 4
                  c.addi     s7, 28
                  c.srli     a2, 3
                  c.addi     t4, 13
                  lui        s6, 345561
                  and        a6, a3, s8
                  c.lui      a0, 3
                  c.addi     t3, 28
                  lui        a2, 744887
                  c.addi     a7, -1
                  mulhsu     gp, gp, a5
1473:             or         zero, a7, ra
                  auipc      s4, 823919
                  bgeu       s1, t4, 1488f
                  c.slli     a2, 13
                  c.addi     a4, -26
                  c.slli     a5, 18
                  lui        s10, 782514
                  c.srli     a1, 24
                  c.lui      a2, 8
                  sll        zero, s8, a3
                  c.srli     a1, 24
                  auipc      a4, 32662
                  auipc      s6, 131750
                  lui        s9, 541476
                  andi       gp, a4, -127
1488:             slti       zero, a3, -106
                  c.srai     a1, 27
                  c.srli     a3, 8
                  c.addi     s8, -26
                  and        a1, a5, t5
                  c.slli     s1, 17
                  c.slli     a3, 6
                  mulhu      t5, sp, a6
                  mulh       s8, gp, s8
                  lui        a2, 944657
                  lui        s6, 95264
                  bltu       a3, s8, 1516f
                  and        s3, s0, a4
                  sub        t1, s8, a4
                  c.lui      gp, 10
                  auipc      s8, 102267
                  div        t3, t5, a7
                  or         a4, s7, tp
                  c.slli     s3, 10
                  c.addi     t3, 22
                  lui        s9, 197262
                  lui        s6, 254709
                  auipc      s10, 43869
                  c.li       s3, 4
                  c.beqz     a2, 1532f
                  c.addi     a0, 17
                  c.addi     t5, -16
                  c.lui      t5, 10
1516:             c.addi     t2, 7
                  lui        a0, 878359
                  fence.i
                  lui        a1, 966684
                  c.addi     s4, 1
                  bne        t2, a4, 1524f
                  auipc      a3, 102439
                  andi       zero, a6, 62
1524:             auipc      s11, 530572
                  auipc      a2, 289985
                  c.addi     s0, -29
                  c.lui      gp, 21
                  lui        s6, 144134
                  c.addi     s0, 18
                  c.addi     t1, 29
                  lui        s0, 195374
1532:             c.addi     t3, -13
                  c.srli     a1, 30
                  mul        a0, a2, tp
                  c.srai     s1, 30
                  auipc      a3, 996938
                  bltu       tp, s9, 1542f
                  c.addi     a2, 22
                  c.lui      s3, 22
                  c.addi     s3, 7
                  rem        a1, s9, t4
1542:             lui        a4, 924453
                  c.addi     s11, -25
                  auipc      a2, 521986
                  beq        t5, s10, 1564f
                  c.addi     s11, -26
                  auipc      t2, 412993
                  c.addi     t6, 19
                  c.addi     s6, -4
                  auipc      a0, 98830
                  c.lui      s7, 24
                  c.slli     s3, 21
                  xori       s10, ra, 881
                  c.addi     t3, -15
                  c.mv       s11, s10
                  c.srli     s0, 29
                  c.addi     s1, -7
                  c.srli     a2, 26
                  lui        s6, 192187
                  c.lui      t2, 26
                  c.lui      t3, 11
                  c.lui      t1, 15
                  c.lui      a1, 28
1564:             andi       gp, s2, -7
                  c.srli     s0, 25
                  c.addi     s11, 8
                  andi       s11, a6, 765
                  auipc      gp, 558666
                  auipc      s0, 213918
                  c.srai     s0, 16
                  c.addi     t1, 21
                  divu       t2, tp, s7
                  c.addi     s8, 4
                  andi       s3, a1, -115
                  auipc      t3, 763510
                  lui        s7, 710011
                  c.addi     a3, 18
                  c.slli     t4, 10
                  c.srli     a4, 15
                  lui        s3, 562833
                  lui        a1, 862259
                  c.srai     a4, 24
                  lui        s8, 526701
                  and        s10, a7, t0
                  c.addi     s0, -18
                  lui        s7, 655846
                  c.addi     s6, -1
                  auipc      a4, 56341
                  c.addi     s9, 14
                  lui        a7, 789822
                  auipc      t6, 523409
                  c.addi     t4, 22
                  div        s2, s0, sp
                  c.lui      s6, 11
                  c.addi     t5, 28
                  c.srai     a5, 16
                  mul        gp, s8, s5
                  c.addi     t1, -19
                  c.addi     a5, 12
                  c.addi     t4, -8
                  c.srai     a1, 7
                  sra        s8, a0, ra
                  c.addi     t4, -25
                  c.srai     a3, 18
                  c.addi     s6, 31
                  c.addi     gp, 4
                  c.addi     s10, -2
                  c.or       a0, a4
                  c.lui      a3, 25
                  c.slli     t3, 11
                  auipc      s3, 203246
                  c.addi     s0, -12
                  c.addi     t3, -7
                  c.lui      t1, 26
                  rem        s8, s9, s5
                  or         a6, a3, s9
                  addi       s4, s0, 558
                  nop
                  c.addi     a0, 13
                  c.bnez     a5, 1637f
                  c.srai     a4, 21
                  lui        a0, 955744
                  mul        s10, s9, s1
                  c.addi     a4, -11
                  c.slli     a4, 13
                  c.srai     s0, 16
                  c.addi     s10, -22
                  c.addi     s3, 20
                  c.srli     a0, 27
                  c.srai     a1, 29
                  c.srai     a3, 27
                  c.srli     a1, 7
                  mulhu      t5, s1, gp
                  auipc      t2, 53382
                  lui        s11, 258391
                  mulhsu     t4, t0, s3
1637:             auipc      a2, 75374
                  nop
                  c.slli     t2, 22
                  mulhsu     t6, a5, s2
                  c.lui      s7, 18
                  c.slli     a6, 28
                  c.lui      a5, 2
                  c.srli     a4, 16
                  bltu       a2, a5, 1646f
1646:             c.slli     t6, 6
                  c.slli     s0, 20
                  c.srli     s1, 9
                  c.addi     s5, -4
                  c.addi     t6, 7
                  c.addi     s3, -5
                  auipc      t6, 897499
                  auipc      s3, 994142
                  nop
                  auipc      t1, 395617
                  sltu       t2, a4, t2
                  srai       s8, s10, 14
                  c.srli     a1, 21
                  c.slli     t1, 30
                  auipc      s3, 500989
                  c.addi     s4, -32
                  auipc      a1, 531841
                  lui        s0, 792199
                  c.srai     a4, 29
                  c.srli     s1, 5
                  c.addi     s11, 26
                  bgeu       t5, ra, 1676f
                  c.addi     a0, 9
                  c.addi     s1, 8
                  lui        a1, 562929
                  c.addi     a0, -21
                  c.slli     s8, 5
                  c.addi     a4, -20
                  slti       s0, a6, -252
                  sra        s10, t5, s10
1676:             c.addi     a1, -4
                  c.lui      s3, 12
                  c.addi     a3, -21
                  lui        t1, 436648
                  c.addi     a4, -22
                  c.lui      s8, 19
                  c.srai     a3, 31
                  c.lui      a5, 7
                  sub        s11, t6, a3
                  mul        gp, s4, s0
                  c.srli     a2, 28
                  c.addi     s1, 31
                  c.addi     s10, 28
                  rem        a4, s7, a6
                  srai       s7, t5, 28
                  c.srli     s0, 3
                  c.slli     s1, 20
                  c.addi     s2, -19
                  srl        zero, s5, a0
                  lui        s8, 721061
                  c.slli     t6, 14
                  c.addi     a5, -15
                  auipc      s7, 67148
                  divu       zero, a0, s6
                  c.addi     a5, -28
                  lui        s3, 109861
                  lui        s3, 210410
                  ori        s1, s1, 404
                  c.addi     s0, 23
                  lui        t5, 171570
                  c.lui      a2, 21
                  xor        s1, t6, t1
                  c.srli     a2, 5
                  la         s11, data_page_12+2133 #start riscv_load_store_rand_instr_stream_35
                  c.srai     a0, 1
                  srli       s2, a1, 25
                  lui        a3, 705079
                  lb         t1, -265(s11)
                  lbu        a5, -864(s11)
                  lb         a7, 504(s11)
                  lhu        s5, -1811(s11)
                  xori       a7, s8, 484
                  sh         t6, -193(s11)
                  c.addi     s9, -17
                  c.add      s1, a4
                  lb         t5, 1142(s11)
                  lw         t1, 135(s11)
                  c.and      a3, s1
                  lhu        t4, -1813(s11)
                  c.lui      t5, 19
                  c.lui      t1, 8
                  lb         s1, 1706(s11)
                  lb         s9, -1456(s11)
                  lb         t1, -1982(s11)
                  lh         a3, 1393(s11)
                  c.srai     a1, 1
                  xor        s4, s11, t2
                  lh         a0, -489(s11)
                  auipc      gp, 149162
                  c.srli     s0, 23
                  sh         s0, -437(s11)
                  lb         a0, -1343(s11)
                  lui        s2, 102727
                  c.or       a2, s1
                  c.addi     s2, -13
                  sh         s3, 1327(s11)
                  sh         s7, 71(s11)
                  sb         t0, 1632(s11)
                  auipc      a2, 463577
                  lb         a2, 1631(s11)
                  lb         t1, -1806(s11)
                  lb         s8, -1242(s11)
                  lb         s6, -1240(s11)
                  c.srli     a3, 25
                  lb         t2, 433(s11)
                  sb         zero, 1731(s11)
                  slti       a0, t0, -703
                  sb         s1, -1432(s11)
                  lw         t1, 791(s11)
                  auipc      gp, 210937
                  lbu        t2, -341(s11)
                  sw         ra, -997(s11)
                  sb         s11, 770(s11) #end riscv_load_store_rand_instr_stream_35
                  c.srli     s0, 20
                  c.addi     s5, 2
                  lui        s4, 167681
                  sll        t6, s4, a4
                  c.srli     a4, 5
                  c.lui      s3, 23
                  lui        a2, 96765
                  c.addi     t4, -20
                  c.srli     a1, 12
                  c.sub      s1, a0
                  xori       a0, a6, 601
                  c.addi     a4, -24
                  c.addi     s10, -23
                  c.srai     a1, 4
                  c.addi     t1, -10
                  c.addi     t2, -19
                  lui        a3, 301600
                  c.srai     a5, 18
                  c.slli     t5, 25
                  auipc      t5, 927593
                  remu       t2, t5, a2
                  lui        t2, 232550
                  c.srai     s0, 15
                  c.addi     s7, -26
                  c.addi     s6, -3
                  c.addi     a6, 28
                  lui        s1, 454149
                  auipc      a0, 989152
                  ori        s9, s3, -385
                  auipc      a3, 985948
                  lui        gp, 674405
                  remu       s1, t1, a2
                  c.bnez     s1, 1749f
                  lui        s4, 137730
                  c.addi     a4, -25
                  auipc      a7, 297504
                  c.addi     a2, 5
                  c.addi     t2, 15
                  slli       s8, s8, 11
                  c.addi     s3, -13
1749:             c.lui      s8, 6
                  c.addi     s1, 31
                  c.nop
                  c.slli     t5, 4
                  c.addi     t6, -1
                  auipc      zero, 544295
                  c.srai     s0, 23
                  c.addi     s10, -2
                  c.addi     s2, -8
                  c.addi     a7, 10
                  c.addi     t1, -5
                  c.lui      t5, 13
                  auipc      s10, 546697
                  c.addi     s1, -21
                  auipc      s0, 852686
                  c.slli     s1, 20
                  srai       s8, t5, 19
                  c.addi     a7, 26
                  c.srli     s0, 7
                  c.addi     a3, 3
                  c.addi     a0, 7
                  c.addi     t3, -25
                  auipc      t6, 865215
                  auipc      s9, 131751
                  bgeu       s10, gp, 1779f
                  c.addi     a6, 1
                  c.srai     a0, 22
                  lui        a3, 368459
                  c.addi     a4, 21
                  lui        t6, 888345
1779:             c.addi     a6, 9
                  c.bnez     a0, 1795f
                  addi       s3, s10, -359
                  c.addi     s8, -7
                  c.addi     s8, -24
                  xor        s11, t6, a7
                  slti       s0, a0, -843
                  c.addi     s11, 22
                  c.srli     s1, 15
                  c.andi     a1, 19
                  srai       s8, s2, 22
                  lui        a2, 979935
                  auipc      a0, 984523
                  c.addi     s6, 6
                  c.addi     a6, -8
                  c.addi     a5, 31
1795:             c.srai     a0, 20
                  auipc      s7, 861975
                  c.srli     a0, 20
                  la         t6, data_page_2+2503 #start riscv_load_store_rand_instr_stream_48
                  sh         a3, -677(t6)
                  sb         s7, 987(t6)
                  divu       s1, t5, a0
                  c.addi     s4, -27
                  sw         s0, -435(t6)
                  auipc      a7, 886710
                  lb         a1, 313(t6)
                  c.addi     a0, -13
                  sb         t0, -104(t6)
                  auipc      a1, 936706
                  c.addi     t2, 20
                  auipc      a0, 940896
                  c.addi     s4, 2
                  lui        s9, 90422
                  sw         s9, 1529(t6)
                  c.lui      a3, 22
                  lb         t2, -600(t6)
                  auipc      s6, 751602
                  lb         a4, 88(t6)
                  sb         t1, 83(t6)
                  lb         a1, -974(t6)
                  sb         a3, -1722(t6) #end riscv_load_store_rand_instr_stream_48
                  c.andi     s1, 14
                  c.beqz     s0, 1804f
                  c.addi     s6, 26
                  srl        s9, a6, t2
                  auipc      a5, 537901
                  lui        t2, 953172
1804:             lui        a3, 548393
                  auipc      gp, 16528
                  c.addi     t3, 24
                  la         s11, data_page_7+1543 #start riscv_load_store_rand_instr_stream_63
                  lbu        s3, 608(s11)
                  c.srai     a1, 14
                  lw         a0, 93(s11)
                  remu       a4, s10, a4
                  sb         s4, -996(s11)
                  lui        gp, 56584
                  lw         a4, 629(s11)
                  lb         s10, 380(s11)
                  lb         a2, 1203(s11)
                  add        s10, t3, s9
                  sb         s2, 428(s11)
                  lb         a0, 742(s11)
                  fence.i
                  c.slli     s9, 25
                  c.srai     a1, 17
                  lb         s5, 1952(s11)
                  c.srai     a1, 3
                  lui        s6, 263629
                  lbu        s3, 587(s11)
                  sb         s9, 1678(s11)
                  c.addi     s9, -22
                  c.srai     a5, 11
                  c.srai     a2, 26
                  c.slli     s3, 15
                  c.srai     a0, 23
                  c.addi     a5, -14
                  lb         a2, -1222(s11)
                  c.lui      s10, 14
                  c.andi     a3, -16
                  sll        s9, t5, s3
                  lb         s2, 652(s11)
                  lui        s8, 198493
                  sb         gp, 1497(s11)
                  c.addi     a1, 16
                  c.srli     a3, 23
                  slti       s4, zero, 319
                  auipc      a7, 330031
                  sw         a5, 709(s11)
                  c.mv       gp, s10
                  mulh       s6, s9, gp
                  lhu        t3, 1521(s11)
                  lbu        s6, 156(s11)
                  lui        s9, 783578
                  lb         t2, 1934(s11) #end riscv_load_store_rand_instr_stream_63
                  xor        s11, s11, t1
                  c.li       s5, 31
                  c.addi     a6, -22
                  c.addi     gp, -27
                  c.addi     a4, -29
                  div        a5, a6, s5
                  sub        t4, a3, a5
                  c.bnez     a0, 1832f
                  c.srli     s1, 10
                  c.srli     a5, 16
                  c.addi     s0, -12
                  auipc      a6, 329090
                  c.addi     s2, 12
                  lui        s5, 370149
                  remu       t4, a2, a4
                  c.slli     a7, 29
                  c.srli     a2, 10
                  auipc      s8, 66952
                  sra        a1, s10, gp
                  c.slli     t2, 20
                  auipc      t5, 343436
                  xor        s1, a0, t3
                  c.addi     a4, -7
                  lui        s9, 671831
                  auipc      s9, 912751
                  la         s9, data_page_4+1740 #start riscv_load_store_rand_instr_stream_39
                  c.lui      a4, 5
                  auipc      s7, 527944
                  sb         ra, 36(s9)
                  lbu        s7, 389(s9)
                  lbu        s3, -1113(s9)
                  c.slli     t1, 22
                  lh         a2, 708(s9)
                  lb         a0, -1354(s9)
                  lbu        gp, 428(s9)
                  c.addi     a1, 12
                  lbu        gp, -1532(s9)
                  sb         s11, 2028(s9)
                  lb         t6, 1870(s9)
                  lh         a6, 1050(s9)
                  lui        t1, 467304
                  c.addi     a2, -6
                  sb         ra, -901(s9)
                  sh         t0, -250(s9)
                  sb         s0, 1571(s9)
                  sb         a6, 304(s9)
                  div        a4, s9, a1
                  lui        s8, 990582
                  c.lui      t1, 14
                  sw         s11, 1888(s9)
                  srl        a3, a7, t3
                  sh         s10, 734(s9)
                  lb         s5, -1441(s9)
                  lb         a0, -1543(s9)
                  c.nop
                  lui        s2, 681189
                  lui        s5, 801952
                  sb         s2, 1303(s9)
                  lb         s7, -506(s9)
                  lh         s2, -816(s9)
                  lw         t4, 1200(s9)
                  c.srai     a5, 8
                  c.srli     a3, 23
                  lbu        s1, 1781(s9)
                  lh         s7, -1082(s9)
                  andi       zero, tp, 934
                  sb         s10, 1246(s9)
                  lw         s8, 1900(s9)
                  srli       a1, sp, 12
                  lbu        t3, 903(s9)
                  lw         s1, -328(s9)
                  c.srli     a1, 23
                  lh         t3, -176(s9) #end riscv_load_store_rand_instr_stream_39
1832:             c.srli     a2, 5
                  c.addi     a4, 16
                  auipc      a3, 814522
                  c.srli     a5, 1
                  c.addi     s2, 3
                  c.slli     s0, 25
                  auipc      t3, 148703
                  lui        t1, 1043002
                  c.xor      s1, a0
                  c.addi     a3, -12
                  auipc      s8, 359430
                  c.srli     a5, 18
                  c.addi     s2, 24
                  c.addi     s1, -26
                  c.addi     t5, 26
                  c.srai     a2, 19
                  xor        t2, t1, a6
                  c.srli     s1, 6
                  nop
                  c.lui      a2, 30
                  c.addi     a0, 3
                  srli       gp, a2, 21
                  c.lui      a6, 26
                  c.addi     s8, 1
                  c.addi     gp, 1
                  c.lui      s8, 21
                  c.addi     a0, 25
                  c.addi     a5, -25
                  c.slli     s8, 22
                  lui        t5, 595435
                  c.addi     s3, -26
                  lui        a4, 311158
                  auipc      a1, 965221
                  auipc      t5, 983850
                  c.addi     a3, 10
                  c.addi     t3, -18
                  c.srai     s0, 20
                  mulhu      gp, a5, s2
                  auipc      zero, 546827
                  lui        s1, 19635
                  divu       s0, s4, t1
                  c.addi     a0, 10
                  auipc      s1, 979090
                  mulh       a6, a0, a5
                  c.nop
                  c.sub      a2, a3
                  c.srai     a5, 14
                  sll        t6, t6, a3
                  lui        s9, 1520
                  c.addi     t1, -6
                  c.addi     s1, 26
                  c.slli     s11, 17
                  c.lui      s5, 11
                  c.addi     a1, -30
                  la         a2, data_page_17+1992 #start riscv_load_store_rand_instr_stream_51
                  sb         t6, 169(a2)
                  sb         s6, 155(a2)
                  lh         s10, 1520(a2)
                  auipc      s9, 355175
                  lhu        s9, -1986(a2)
                  sb         s8, 1753(a2)
                  sltiu      t6, a2, -694
                  c.addi     s2, -9
                  lbu        s2, 949(a2)
                  lbu        s3, 1969(a2)
                  lbu        a7, 290(a2)
                  lb         a5, 1098(a2)
                  c.srai     a3, 29
                  lb         gp, 22(a2)
                  lbu        s0, 215(a2)
                  lbu        s0, -841(a2)
                  lb         s10, 749(a2)
                  lui        a7, 674250
                  lb         a0, -1267(a2)
                  lb         t6, -1881(a2)
                  lh         t3, -1170(a2)
                  c.srli     a1, 19
                  lbu        a1, -1630(a2)
                  lb         t6, -1510(a2)
                  c.mv       a3, s9
                  lh         s11, 1578(a2)
                  lb         t2, 994(a2)
                  sb         a7, -1565(a2)
                  lui        a4, 1041924
                  lui        s7, 364090
                  sb         a1, 612(a2)
                  lb         a3, 1537(a2)
                  c.or       a0, a3
                  lbu        a5, -1169(a2)
                  auipc      s10, 90273
                  lbu        t5, -606(a2)
                  sb         a7, -1224(a2)
                  sb         a3, -873(a2)
                  auipc      t1, 385914
                  lbu        s6, 1887(a2) #end riscv_load_store_rand_instr_stream_51
                  auipc      a7, 878710
                  c.addi     a2, 9
                  c.addi     a7, -30
                  c.srli     a3, 12
                  c.srli     a0, 3
                  c.lui      s8, 6
                  auipc      t5, 990314
                  auipc      a0, 656047
                  c.lui      a0, 2
                  c.slli     t1, 9
                  c.lui      a3, 23
                  ori        s4, s2, -322
                  c.addi     t3, 26
                  c.addi     a7, -19
                  auipc      a5, 463322
                  bltu       a2, sp, 1905f
                  lui        a0, 252213
                  srli       gp, s1, 12
                  c.addi     s0, -3
1905:             lui        s7, 602832
                  sltu       a1, t2, a7
                  auipc      s6, 565548
                  la         a4, data_page_9+2030 #start riscv_load_store_rand_instr_stream_60
                  divu       s8, tp, a6
                  lh         s11, -1256(a4)
                  c.addi     a5, -15
                  sb         a2, 133(a4)
                  lb         a6, 419(a4)
                  c.lui      s6, 2
                  lbu        t6, -2016(a4)
                  sh         a3, 1740(a4)
                  lui        a6, 890201
                  lhu        s2, 848(a4)
                  sb         t5, -872(a4)
                  c.addi     s8, -6
                  sb         t6, 373(a4)
                  c.addi     s2, 31
                  lbu        a0, -1237(a4)
                  lbu        gp, 621(a4)
                  sb         sp, 237(a4)
                  lui        s0, 787273
                  c.addi     t1, 20
                  lbu        t4, 1585(a4)
                  sb         s0, 1759(a4)
                  lb         a5, 733(a4)
                  lb         a2, -1003(a4)
                  lb         t1, 577(a4)
                  rem        s5, a5, s2
                  lh         zero, -470(a4)
                  sb         t6, 961(a4)
                  lb         s10, 1657(a4)
                  lh         s6, -1300(a4)
                  auipc      s6, 790716
                  sw         zero, 674(a4)
                  c.lui      t2, 17
                  sb         tp, 1858(a4)
                  sh         t1, 556(a4)
                  c.sub      s0, a0
                  sb         sp, -1254(a4)
                  lh         t4, -610(a4)
                  c.srli     a1, 13
                  auipc      t3, 278045
                  c.addi     a7, 4
                  lb         s11, 778(a4)
                  lbu        t1, -257(a4)
                  lui        a6, 319628
                  lh         s9, 1080(a4)
                  c.slli     a2, 28
                  auipc      s8, 928654
                  srl        t4, s0, s1
                  sb         sp, -1239(a4) #end riscv_load_store_rand_instr_stream_60
                  lui        gp, 922246
                  c.srli     s0, 18
                  c.addi     t5, 30
                  lui        t6, 525744
                  c.lui      a0, 25
                  lui        s7, 60147
                  lui        t6, 384917
                  auipc      s0, 81512
                  lui        t6, 799931
                  c.srai     a4, 9
                  c.addi     a5, -31
                  or         s4, zero, t3
                  c.addi     t4, 27
                  c.xor      s0, a3
                  c.addi     s9, -30
                  c.srai     a1, 15
                  lui        a4, 142895
                  c.lui      s4, 26
                  auipc      s11, 402455
                  c.sub      a3, a3
                  c.srli     a2, 14
                  c.addi     t5, 23
                  and        t5, a3, t1
                  c.addi     s4, 26
                  c.srli     a5, 6
                  lui        s10, 484818
                  auipc      a3, 221149
                  sra        a4, a5, s4
                  la         s4, data_page_5+2139 #start riscv_load_store_rand_instr_stream_69
                  lui        a5, 462253
                  auipc      s6, 550898
                  auipc      t2, 182425
                  lhu        t2, -1479(s4)
                  c.srai     a4, 19
                  lb         s11, 1008(s4)
                  sb         tp, -1039(s4)
                  sb         s1, 1423(s4)
                  c.addi     a5, 24
                  sb         a4, 203(s4)
                  sb         zero, -445(s4)
                  c.addi     s0, 22
                  lb         a4, 238(s4)
                  lbu        s8, 1640(s4)
                  sb         s1, -1952(s4)
                  div        t5, a3, a3
                  sb         s11, 1732(s4)
                  sb         s2, -860(s4)
                  sb         s7, -548(s4)
                  lb         a4, 407(s4)
                  mulh       s11, s0, s8
                  c.add      a2, a3
                  lbu        a0, 870(s4)
                  lb         s8, 1696(s4)
                  lb         a2, 620(s4)
                  auipc      a3, 766907
                  c.srai     a1, 8
                  sb         s7, -1442(s4)
                  c.srli     s0, 3
                  sb         t4, -637(s4)
                  lbu        a2, -707(s4)
                  c.or       a4, a5
                  c.addi     t1, -4
                  c.addi     s2, 3
                  c.srli     a2, 23
                  lhu        t5, -1935(s4)
                  sb         s2, -646(s4)
                  lbu        a1, 831(s4)
                  c.xor      a2, a5
                  sb         s9, -536(s4)
                  mul        a6, a4, sp
                  c.lui      a3, 31
                  sb         t0, 1323(s4)
                  lw         s8, 1521(s4)
                  c.addi     a6, -30
                  sb         a4, 684(s4)
                  lb         s11, 816(s4)
                  auipc      s6, 729940
                  lh         t3, 1465(s4) #end riscv_load_store_rand_instr_stream_69
                  c.addi     s0, -26
                  lui        s1, 175503
                  c.srli     a1, 30
                  lui        s9, 270028
                  auipc      s4, 769434
                  auipc      a4, 434390
                  auipc      s3, 965256
                  c.addi     t1, 16
                  auipc      t1, 1003810
                  c.lui      s11, 23
                  c.lui      t5, 26
                  bne        t5, s6, 1952f
                  auipc      s5, 269713
                  mul        a7, zero, s4
                  c.addi     a0, 27
                  sltu       a3, a1, t5
1952:             srl        t6, t6, a3
                  c.srai     s1, 14
                  c.srai     a1, 29
                  lui        a6, 45412
                  c.addi     s0, 14
                  c.beqz     s0, 1975f
                  c.addi     s3, 11
                  srai       t1, s10, 0
                  c.addi     t2, -20
                  and        a5, s1, a1
                  c.addi     a5, -3
                  c.addi     s9, -24
                  c.srai     a4, 3
                  auipc      t3, 18126
                  c.srai     s0, 22
                  c.srli     a2, 5
                  c.addi     gp, 19
                  c.addi     t5, 11
                  c.addi     s10, -6
                  ori        a6, s4, 981
                  c.addi     gp, -20
                  c.lui      a6, 28
                  mulhsu     s5, a7, a5
1975:             auipc      s4, 303718
                  auipc      s4, 603139
                  c.andi     a5, -5
                  sub        s0, s1, s10
                  auipc      s2, 488125
                  c.lui      s8, 14
                  c.srli     a4, 6
                  mulh       s1, a1, a5
                  c.slli     t3, 31
                  c.addi     a5, 28
                  c.srai     s0, 22
                  auipc      zero, 406501
                  lui        t5, 221654
                  lui        s7, 418305
                  c.srli     a3, 24
                  c.slli     s0, 21
                  bgeu       s1, sp, 1995f
                  auipc      a5, 689031
                  c.addi     s10, -12
                  c.addi     s3, 2
1995:             c.srai     s1, 28
                  auipc      s6, 16770
                  sltu       s10, a1, s0
                  c.beqz     s0, 1999f
1999:             c.addi     t4, -6
                  c.slli     s3, 25
                  auipc      s9, 57187
                  auipc      a0, 808500
                  sll        a2, s0, s9
                  c.addi     a6, 31
                  remu       s11, tp, a7
                  c.srai     a5, 8
                  c.addi     s11, -6
                  c.slli     a4, 16
                  bltu       s9, a4, 2012f
                  c.srli     a1, 3
                  addi       s8, s0, -52
2012:             c.srai     a3, 2
                  c.srli     s0, 28
                  c.addi     a4, 11
                  auipc      t6, 316424
                  bge        t5, a0, 2017f
2017:             c.addi     s10, -31
                  c.srai     a3, 26
                  sra        a3, ra, t0
                  c.srli     s0, 17
                  lui        s1, 890452
                  auipc      a5, 977995
                  c.srli     a2, 29
                  auipc      a5, 780337
                  c.srai     a2, 16
                  srl        zero, tp, s3
                  c.addi     s11, 26
                  c.addi     s9, -13
                  c.lui      a2, 14
                  c.li       t2, 27
                  c.or       a5, a4
                  la         t3, data_page_16+2425 #start riscv_load_store_rand_instr_stream_23
                  c.slli     t6, 10
                  lb         t6, -1719(t3)
                  sb         a6, 1253(t3)
                  sb         s9, -1704(t3)
                  lhu        s4, -657(t3)
                  c.srai     a4, 19
                  lh         t1, -751(t3)
                  auipc      zero, 541040
                  sw         gp, -1233(t3)
                  fence
                  sb         zero, 1151(t3)
                  lbu        a7, 538(t3)
                  c.slli     s8, 11
                  lb         a6, 47(t3)
                  c.addi     t6, -7
                  lbu        s8, 946(t3)
                  lbu        s3, -1470(t3)
                  lh         t5, 1233(t3)
                  lbu        t4, 1435(t3)
                  c.lui      s3, 3
                  c.addi     s7, 23
                  lui        s10, 779248
                  c.nop
                  lhu        a2, -635(t3)
                  lh         t6, -179(t3)
                  lb         a1, -846(t3)
                  lb         zero, -1874(t3)
                  sh         s8, -1103(t3)
                  sw         a5, -1621(t3)
                  lbu        a1, 155(t3)
                  sb         s1, -622(t3)
                  c.slli     t1, 2
                  sb         s10, 104(t3)
                  sh         s8, 83(t3)
                  lbu        a5, 962(t3)
                  lbu        gp, 352(t3)
                  lbu        s11, 1214(t3)
                  sb         a0, 1027(t3)
                  sb         a6, 1604(t3)
                  lb         a5, -1363(t3) #end riscv_load_store_rand_instr_stream_23
                  c.srai     s1, 11
                  lui        t2, 573969
                  c.addi     t3, 15
                  remu       s11, s4, a6
                  c.addi     a1, -25
                  c.lui      t6, 20
                  bne        s3, s9, 2039f
2039:             c.lui      s8, 7
                  c.addi     a3, -8
                  auipc      t1, 854768
                  lui        a1, 974885
                  c.li       s6, 4
                  c.srai     a1, 20
                  c.addi     s7, -31
                  c.addi     a2, -32
                  c.addi     a3, -11
                  c.addi     t2, 27
                  c.srai     a1, 2
                  c.srai     s1, 31
                  slt        s9, a3, a2
                  lui        a0, 341706
                  c.beqz     a5, 2060f
                  c.addi     s0, -19
                  c.addi     s6, -23
                  c.srli     a1, 22
                  c.addi     s6, -31
                  sll        s8, a4, t6
                  auipc      s11, 678016
2060:             c.addi     gp, -8
                  c.slli     a6, 27
                  c.lui      a4, 10
                  c.addi     s2, 25
                  c.lui      a7, 27
                  lui        s6, 793446
                  c.slli     s3, 23
                  c.lui      s9, 6
                  srl        zero, s9, s3
                  auipc      a0, 917236
                  lui        s6, 695792
                  c.lui      s3, 14
                  mulhu      s9, a2, ra
                  c.addi     s7, 14
                  c.addi     s5, 25
                  c.slli     s5, 6
                  c.srai     a4, 18
                  c.addi     s11, -2
                  sltu       t4, t3, s5
                  c.slli     t1, 9
                  c.srli     a1, 24
                  lui        a0, 12369
                  c.lui      s6, 6
                  lui        s4, 366649
                  c.srai     a2, 5
                  auipc      t2, 73866
                  auipc      s6, 756711
                  c.addi     s1, -24
                  c.addi     s11, 18
                  c.slli     s11, 15
                  c.addi     a7, -3
                  c.and      s0, a3
                  c.slli     t5, 6
                  c.bnez     a5, 2098f
                  auipc      s8, 181874
                  lui        s11, 456591
                  sub        s3, s8, t3
                  c.sub      a1, a2
2098:             lui        s3, 470971
                  c.addi     s3, -3
                  srl        t5, s11, s10
                  c.addi     s1, -26
                  c.lui      t2, 17
                  c.lui      a0, 9
                  c.srli     s0, 18
                  la         t5, data_page_15+1961 #start riscv_load_store_rand_instr_stream_0
                  lbu        s4, 1854(t5)
                  lbu        t3, 112(t5)
                  lhu        a7, 999(t5)
                  lb         s1, -64(t5)
                  c.srai     s0, 31
                  sh         a5, 601(t5)
                  lui        a6, 197077
                  c.lui      s5, 19
                  ori        zero, a6, -391
                  sb         tp, -447(t5)
                  auipc      s2, 496573
                  sh         a1, 497(t5)
                  sh         a0, -1221(t5)
                  c.lui      t2, 14
                  sb         s8, 529(t5)
                  c.addi     s8, -23
                  ori        a0, gp, 113
                  lb         t4, 1672(t5)
                  c.srai     a5, 22
                  lhu        a7, -1681(t5)
                  lw         a5, -729(t5)
                  c.addi     s7, 27
                  c.slli     s4, 11
                  c.addi     s1, -25
                  lhu        a4, 393(t5)
                  lhu        s1, 639(t5)
                  sltu       s7, t5, a6
                  lh         s4, 1899(t5)
                  auipc      s1, 962489
                  sh         t1, 1503(t5)
                  lb         t1, -1680(t5)
                  lbu        s11, -571(t5)
                  c.srai     a1, 27
                  sb         a5, -352(t5)
                  lhu        zero, 423(t5)
                  lbu        a4, -1866(t5)
                  c.srai     a0, 24
                  c.slli     s11, 15
                  lui        t2, 479247
                  slt        t4, s7, a0
                  mul        t2, a3, t0
                  lh         s7, -105(t5)
                  lbu        s6, -554(t5)
                  sw         zero, -993(t5)
                  fence
                  lw         s11, 603(t5)
                  lui        gp, 985587
                  lb         t2, -118(t5)
                  lbu        t4, 1708(t5) #end riscv_load_store_rand_instr_stream_0
                  auipc      t3, 735589
                  addi       s2, a6, -1
                  lui        a3, 77439
                  c.mv       a1, t5
                  lui        s6, 146185
                  c.addi     s3, -6
                  c.addi     s1, 10
                  andi       t1, s5, -461
                  c.addi     a0, 6
                  c.addi     t6, -27
                  slli       s3, a1, 14
                  lui        s10, 667895
                  auipc      a3, 449642
                  c.slli     s4, 10
                  lui        t5, 674181
                  c.srli     a3, 26
                  auipc      a0, 156250
                  slli       a3, s4, 22
                  c.addi     a0, -14
                  c.addi     a6, -16
                  c.slli     a7, 31
                  c.addi     s1, 13
                  c.xor      a1, a1
                  c.lui      s8, 13
                  nop
                  lui        a6, 923562
                  c.slli     s6, 22
                  c.srli     a1, 2
                  auipc      s2, 266498
                  c.addi     s4, 26
                  c.lui      s1, 5
                  auipc      s9, 242794
                  sltu       a2, t2, s6
                  c.nop
                  c.srai     a4, 4
                  c.bnez     a3, 2142f
                  lui        s6, 477656
2142:             c.addi     a0, -32
                  lui        s10, 834685
                  c.nop
                  c.lui      a2, 27
                  mulhsu     s9, gp, gp
                  c.addi     s5, 22
                  c.beqz     a1, 2165f
                  c.addi     a0, 29
                  remu       a4, t5, t2
                  c.addi     s5, -20
                  auipc      a1, 631524
                  fence.i
                  add        s8, zero, t1
                  c.addi     t2, 8
                  mul        s4, s8, a6
                  auipc      s3, 807605
                  auipc      a1, 569270
                  c.srli     a0, 6
                  fence.i
                  c.or       a0, a4
                  blt        a7, a0, 2165f
                  c.slli     a6, 13
                  c.addi     s10, -13
2165:             c.srai     a1, 11
                  auipc      a7, 597807
                  c.slli     t1, 7
                  auipc      s3, 820927
                  c.slli     a5, 5
                  c.addi     s6, -24
                  lui        a3, 501529
                  rem        s2, s10, sp
                  lui        a2, 444421
                  bltu       a5, s6, 2179f
                  c.addi     s9, -6
                  c.slli     s6, 24
                  srai       a7, t6, 24
                  c.slli     a0, 21
                  la         t4, data_page_11+2031 #start riscv_load_store_rand_instr_stream_46
                  lhu        a4, 571(t4)
                  c.addi     a2, 19
                  sh         s10, -231(t4)
                  fence
                  lbu        s2, 1425(t4)
                  c.addi     t5, -20
                  srai       s4, a2, 2
                  c.srai     a2, 6
                  or         s5, s5, s4
                  sw         s8, -987(t4)
                  lbu        gp, 628(t4)
                  c.srai     a5, 8
                  srli       s1, ra, 1
                  c.srli     s1, 17
                  lui        t3, 64349
                  c.srai     s0, 31
                  lb         t6, -1773(t4)
                  sw         tp, 513(t4)
                  lbu        s0, 534(t4)
                  sb         s8, 1061(t4)
                  sb         a6, 653(t4)
                  c.srai     a0, 21
                  c.addi     t1, -5
                  c.lui      s9, 17
                  lb         s10, -1540(t4)
                  c.addi     a4, 31
                  srl        t2, s10, s11
                  sh         tp, 1199(t4)
                  lui        s7, 616483
                  c.srai     a5, 9
                  c.addi     t3, -17
                  auipc      a1, 693980
                  lui        a3, 918384
                  c.srli     a4, 31
                  lui        t1, 62385
                  auipc      s8, 110641
                  c.srli     a5, 8
                  lui        t3, 927764
                  sll        s0, a3, sp
                  auipc      a7, 1004050
                  lh         s0, -345(t4)
                  c.addi     t5, -13
                  remu       s8, s0, t4
                  lb         a1, 1922(t4) #end riscv_load_store_rand_instr_stream_46
2179:             c.addi     a2, -27
                  c.srli     a4, 25
                  c.srli     a1, 23
                  c.srai     a4, 9
                  lui        a3, 344882
                  c.beqz     a5, 2191f
                  c.mv       s6, t6
                  c.addi     s11, -32
                  c.addi     s6, -26
                  lui        t1, 222053
                  c.srai     a3, 19
                  c.addi     s8, 16
2191:             auipc      gp, 149523
                  c.addi     t5, 2
                  c.srli     a1, 23
                  lui        s3, 911036
                  c.addi     s9, -9
                  c.lui      s5, 15
                  c.lui      a0, 13
                  lui        a4, 716933
                  c.addi     s5, 1
                  lui        a3, 268337
                  c.lui      s1, 4
                  auipc      t2, 88047
                  c.srli     a1, 18
                  bltu       s0, t6, 2211f
                  c.slli     a0, 10
                  auipc      s9, 22627
                  lui        s8, 41080
                  c.addi     t3, 5
                  c.addi     s6, 21
                  c.lui      a3, 9
2211:             auipc      s7, 442117
                  auipc      s1, 82412
                  c.addi     s7, -4
                  c.srai     a5, 30
                  c.slli     a0, 13
                  fence
                  c.srai     a0, 2
                  fence
                  lui        a2, 421872
                  lui        s10, 138635
                  slli       t6, s10, 1
                  auipc      t6, 317496
                  c.addi     t3, 18
                  c.lui      a2, 26
                  c.addi     s5, 10
                  c.xor      s1, a4
                  c.addi     s1, 14
                  auipc      a4, 869127
                  lui        t4, 186959
                  bgeu       zero, s10, 2247f
                  c.lui      a2, 10
                  c.addi     s11, 20
                  c.addi     s4, -30
                  auipc      a4, 786666
                  c.lui      a3, 5
                  c.addi     a3, 4
                  lui        a5, 809502
                  auipc      a5, 815870
                  c.lui      s1, 25
                  c.addi     gp, 11
                  lui        s11, 973828
                  c.lui      t2, 7
                  c.addi     a0, -6
                  lui        s4, 454012
                  c.addi     s3, -23
                  c.addi     t6, -1
2247:             remu       a0, a4, ra
                  lui        t3, 407791
                  c.addi     gp, 23
                  c.srai     a4, 13
                  c.addi     s2, 18
                  c.srai     s1, 16
                  c.srai     a5, 21
                  c.addi     t5, -7
                  c.lui      a7, 21
                  div        s11, s7, s5
                  auipc      s8, 782012
                  c.addi     s0, 3
                  c.addi     s0, -22
                  blt        a7, zero, 2275f
                  auipc      s4, 10255
                  c.addi     t5, 20
                  c.addi     a7, -32
                  c.addi     t4, 22
                  auipc      t2, 269271
                  c.lui      a4, 8
                  c.addi     s0, -15
                  lui        s3, 273856
                  lui        s8, 325157
                  c.slli     t5, 18
                  c.xor      a1, a0
                  c.mv       t3, t6
                  la         t6, data_page_3+1939 #start riscv_load_store_rand_instr_stream_49
                  lh         t2, -1711(t6)
                  lb         t5, 1563(t6)
                  lbu        s0, -714(t6)
                  lb         a4, 766(t6)
                  c.addi     s1, -9
                  c.slli     s8, 15
                  lbu        s1, -1598(t6)
                  slli       s3, s11, 15
                  lbu        s9, 18(t6)
                  sb         a2, -462(t6)
                  c.addi     s0, 4
                  c.addi     s3, -25
                  lui        s3, 1043585
                  lui        s5, 1025475
                  c.addi     t5, 3
                  lb         t4, -1893(t6)
                  sb         s9, 947(t6)
                  sb         t0, 1976(t6)
                  lb         s3, 1124(t6)
                  sb         t3, -848(t6)
                  c.srli     a3, 22
                  c.srai     a3, 19
                  lui        a0, 720752
                  c.slli     a5, 23
                  sh         tp, 795(t6)
                  lui        s8, 837920
                  lbu        a5, 1278(t6)
                  sb         gp, 1158(t6)
                  lui        s1, 283922
                  c.srli     a1, 7
                  lb         t2, 1854(t6)
                  srai       s0, a0, 11
                  sb         s5, 986(t6)
                  lui        t5, 910330
                  c.slli     s8, 18
                  srai       t5, t6, 16
                  c.slli     s8, 22
                  lbu        s11, 348(t6)
                  sltiu      s9, a0, 892
                  srai       a3, a6, 8
                  c.slli     s3, 6
                  c.addi     a3, 21
                  lui        s3, 220726
                  lui        t1, 531360
                  lh         s3, -1851(t6)
                  lui        zero, 717317
                  srli       t1, s11, 28
                  c.slli     s1, 3
                  auipc      s2, 792136
                  lh         s3, 591(t6)
                  sb         a4, 920(t6) #end riscv_load_store_rand_instr_stream_49
                  c.srai     a3, 5
                  lui        a1, 315813
2275:             xori       a5, s6, -479
                  c.lui      a3, 31
                  auipc      s3, 218523
                  la         t1, data_page_2+2040 #start riscv_load_store_rand_instr_stream_67
                  lb         a5, 235(t1)
                  lb         a5, -1151(t1)
                  sb         a7, -229(t1)
                  c.addi     a2, -21
                  lbu        zero, 184(t1)
                  lbu        a5, 1297(t1)
                  sra        a5, a2, a0
                  lbu        t2, -891(t1)
                  lbu        s6, -1601(t1)
                  lb         s7, 1981(t1)
                  lb         zero, -1323(t1)
                  lb         s4, 8(t1)
                  sb         ra, 1759(t1)
                  c.mv       s6, a7
                  lbu        s0, 1841(t1)
                  lh         s1, -1254(t1)
                  lb         a3, 1911(t1)
                  sb         a7, 1401(t1)
                  lbu        t4, 279(t1)
                  lb         s2, -1010(t1)
                  lbu        s3, -99(t1)
                  c.addi     s5, 1
                  c.addi     s10, -13
                  sb         s10, 1187(t1)
                  lw         s6, 732(t1)
                  srli       s9, s9, 11
                  sltiu      t4, a3, -459
                  lb         s4, -783(t1)
                  auipc      s11, 876006
                  c.addi     s8, -7
                  lb         a3, -1117(t1)
                  lui        a1, 582596
                  lui        a7, 849834
                  auipc      a4, 282879
                  auipc      a0, 504331
                  lb         a6, 1409(t1)
                  lb         t6, -299(t1)
                  sw         s3, -1128(t1)
                  lhu        t3, -1450(t1) #end riscv_load_store_rand_instr_stream_67
                  c.lui      t6, 4
                  auipc      s0, 727510
                  c.beqz     a2, 2300f
                  auipc      t4, 903513
                  c.lui      a2, 25
                  mulhsu     s6, s0, sp
                  c.addi     s4, 4
                  c.srai     a0, 3
                  bge        s2, a0, 2305f
                  auipc      a7, 91755
                  c.addi     s1, -32
                  rem        s11, s9, gp
                  c.srli     a5, 10
                  auipc      s7, 206659
                  c.li       a1, -18
                  auipc      s9, 62901
                  c.addi     a2, 19
                  auipc      a4, 18616
                  fence
                  c.slli     a0, 17
                  auipc      t4, 823615
                  c.srli     a3, 25
2300:             bltu       s2, s1, 2318f
                  c.addi     s8, 9
                  lui        t4, 792282
                  lui        s2, 1010477
                  c.lui      t1, 30
2305:             c.srli     a4, 16
                  c.srli     a3, 8
                  c.addi     a5, 23
                  srli       s8, s8, 22
                  c.addi     a2, -4
                  blt        t6, t6, 2323f
                  auipc      s0, 302692
                  c.srai     s1, 25
                  c.srai     a2, 22
                  auipc      s6, 150518
                  sltu       s5, zero, t3
                  auipc      s4, 305021
                  la         a7, data_page_18+1804 #start riscv_load_store_rand_instr_stream_19
                  auipc      t5, 923834
                  sb         a5, 923(a7)
                  sub        s2, a5, s9
                  c.addi     a1, 29
                  c.addi     a6, 3
                  lhu        zero, 1898(a7)
                  c.addi     a6, -17
                  c.srai     a2, 8
                  c.lui      s6, 20
                  lb         s10, -1465(a7)
                  c.slli     t6, 19
                  c.addi     a2, -32
                  c.add      a5, a4
                  c.addi     s4, 3
                  lh         s2, 148(a7)
                  lh         t3, -822(a7)
                  lbu        s2, -1217(a7)
                  c.lui      s5, 2
                  lui        t2, 892518
                  c.slli     a4, 9
                  auipc      a1, 207232
                  auipc      t6, 658989
                  c.srai     a1, 22
                  c.slli     a5, 6
                  sb         s6, 521(a7)
                  lui        s6, 521869
                  addi       s8, s0, 750
                  c.xor      a4, a2
                  c.lui      s2, 28
                  c.li       s9, 29
                  lhu        s11, -1254(a7)
                  addi       s7, t6, -401
                  c.addi     a3, -27
                  lhu        s4, 1194(a7)
                  lui        a4, 851415
                  xori       s5, a5, 402
                  divu       s5, t4, s10
                  lbu        gp, 554(a7) #end riscv_load_store_rand_instr_stream_19
                  c.addi     t3, 18
2318:             c.addi     t6, -13
                  c.srli     s0, 24
                  c.addi     s6, -24
                  nop
                  c.addi     s11, 22
2323:             c.lui      a3, 23
                  c.addi     s6, 31
                  c.addi     gp, 18
                  c.nop
                  c.nop
                  sub        a5, tp, s10
                  andi       t1, tp, -888
                  sra        s11, s2, zero
                  slt        t4, s1, t3
                  c.andi     s1, 4
                  bgeu       tp, s9, 2338f
                  c.addi     s5, 3
                  lui        s3, 483302
                  c.addi     t1, 1
                  lui        a4, 228489
2338:             c.addi     t5, 23
                  sra        s3, s2, a5
                  c.addi     s6, 25
                  beq        tp, tp, 2359f
                  lui        a2, 18784
                  xor        a4, t2, s2
                  c.srai     a3, 13
                  c.addi     s1, -20
                  bne        ra, a2, 2358f
                  srli       s10, tp, 17
                  c.srli     s0, 12
                  c.or       a0, a1
                  lui        t1, 794980
                  auipc      a4, 74620
                  c.addi     s3, -7
                  xor        s8, a6, s4
                  lui        zero, 311662
                  lui        gp, 572792
                  auipc      s11, 676611
                  bge        a6, t6, 2359f
2358:             c.addi     s6, -4
2359:             c.addi     s7, -27
                  auipc      s4, 375168
                  c.slli     s0, 19
                  lui        s6, 911841
                  c.srli     a2, 7
                  sltu       a0, s8, s5
                  c.lui      t3, 11
                  lui        s0, 229591
                  c.slli     s2, 25
                  slli       a4, t2, 12
                  c.addi     a5, -9
                  c.addi     s11, 27
                  c.srli     a2, 9
                  c.addi     t3, 28
                  sll        s0, s4, a0
                  lui        s8, 785631
                  c.nop
                  lui        t5, 610661
                  c.srli     a0, 27
                  c.addi     t5, 17
                  c.addi     s1, 23
                  lui        t4, 968445
                  c.srli     a0, 25
                  c.addi     a4, -18
                  lui        t1, 651413
                  lui        s3, 445396
                  c.addi     s10, -25
                  auipc      s8, 910745
                  slt        a7, t5, t4
                  c.addi     t5, 24
                  c.addi     s6, -6
                  c.addi     a1, -31
                  sra        a2, a6, gp
                  c.addi     a3, 1
                  c.add      a5, a4
                  c.srai     a0, 19
                  auipc      s1, 201010
                  auipc      a1, 356128
                  auipc      zero, 1002468
                  auipc      t1, 976446
                  c.addi     s7, 22
                  srli       a2, t2, 1
                  c.nop
                  la         a4, data_page_19+2828 #start riscv_load_store_rand_instr_stream_31
                  slli       a6, t2, 18
                  lh         gp, -206(a4)
                  lb         t6, 170(a4)
                  c.srai     a1, 4
                  lb         a6, 250(a4)
                  c.srai     a0, 4
                  lhu        s5, -1950(a4)
                  auipc      t1, 649263
                  c.addi     a6, -7
                  sw         sp, -380(a4)
                  mul        s10, a5, s9
                  c.addi     t5, -16
                  c.srai     a3, 7
                  sh         s7, 514(a4)
                  lh         a0, -1552(a4)
                  c.slli     s1, 12
                  sb         s9, 617(a4)
                  c.slli     s10, 18
                  remu       t1, s4, s4
                  sb         s3, -1198(a4)
                  lhu        s9, -290(a4)
                  lbu        s2, 595(a4)
                  c.addi     a3, 6
                  c.addi     a3, -30
                  sub        s2, a5, t2
                  lw         s6, 1128(a4)
                  lhu        a0, 1136(a4)
                  lb         s11, 781(a4)
                  sb         t1, 372(a4)
                  lb         s2, 1092(a4)
                  sb         tp, -1276(a4)
                  remu       a7, t6, sp
                  lb         s5, -135(a4)
                  c.addi     s6, 16
                  c.slli     a0, 15
                  lb         s3, -717(a4)
                  lh         a5, -1332(a4)
                  lh         gp, -252(a4)
                  nop
                  c.addi     s3, -17
                  sb         tp, -510(a4)
                  sb         s6, -1901(a4)
                  lbu        s7, 1150(a4)
                  lui        s4, 175053
                  slti       zero, sp, 270
                  lb         s6, 286(a4)
                  lb         s2, 437(a4)
                  lbu        s3, -533(a4)
                  sb         t0, -1229(a4)
                  c.or       a0, a3
                  lbu        a1, 1013(a4)
                  lbu        s4, 5(a4) #end riscv_load_store_rand_instr_stream_31
                  divu       a3, s8, a5
                  auipc      a7, 313251
                  c.addi     s4, 27
                  c.addi     s4, 28
                  c.srli     a4, 31
                  sltiu      s10, s9, 483
                  c.srli     s0, 12
                  c.srli     a2, 29
                  remu       s3, sp, s2
                  c.slli     s6, 28
                  c.addi     t1, 11
                  sltiu      t4, s4, 264
                  c.addi     s9, -15
                  srl        t4, a5, s3
                  lui        s11, 515051
                  lui        s11, 179595
                  c.srli     a4, 8
                  auipc      a1, 820305
                  c.addi     s11, -16
                  auipc      gp, 362245
                  c.slli     a3, 28
                  sra        a2, gp, t4
                  c.srai     a2, 3
                  c.addi     t5, 19
                  c.lui      a6, 14
                  c.addi     s11, -8
                  c.sub      a3, a0
                  c.lui      a4, 13
                  c.srli     a5, 16
                  c.slli     s4, 20
                  add        a2, a4, t3
                  auipc      a0, 785446
                  c.addi     s9, -28
                  c.addi     a2, -26
                  c.addi     s11, 4
                  c.andi     a5, 5
                  lui        zero, 737329
                  mul        s11, a5, s4
                  c.addi     s9, 12
                  slti       gp, s9, -354
                  c.slli     gp, 12
                  c.addi     a7, 12
                  c.slli     a3, 28
                  lui        s10, 87200
                  c.srai     a5, 26
                  c.slli     a7, 27
                  c.srli     s0, 11
                  lui        a3, 749113
                  c.addi     t2, 28
                  c.xor      s1, s1
                  c.addi     s10, 3
                  srai       s2, a1, 3
                  c.lui      a5, 24
                  c.srai     a0, 27
                  c.slli     t6, 16
                  c.nop
                  bge        a5, t5, 2475f
                  auipc      s10, 4157
                  la         a1, data_page_0+2419 #start riscv_load_store_rand_instr_stream_41
                  sb         a3, -186(a1)
                  auipc      a7, 968141
                  sh         t1, 433(a1)
                  lbu        a5, -461(a1)
                  lbu        s3, 1406(a1)
                  srl        a2, s11, t0
                  c.srai     a2, 2
                  lbu        a3, 959(a1)
                  lb         a7, 1102(a1)
                  mul        s0, t2, s10
                  lb         a7, -1627(a1)
                  lb         s7, -740(a1)
                  ori        a4, s9, 549
                  sb         t1, -388(a1)
                  lb         s10, -536(a1)
                  lh         t1, -1991(a1)
                  lbu        a4, -1318(a1)
                  lb         t5, -781(a1)
                  sb         a4, -1693(a1)
                  ori        zero, s4, 775
                  lbu        a3, 1648(a1)
                  c.addi     s11, 19
                  lb         a6, -1501(a1)
                  lb         t2, -1676(a1)
                  c.slli     t6, 11
                  sb         s3, 538(a1)
                  auipc      s9, 983074
                  lbu        s1, 1386(a1)
                  sb         t6, 1107(a1)
                  c.srli     a3, 9
                  sb         s8, -1666(a1)
                  c.addi     a4, -30
                  lb         a4, 1546(a1)
                  mulhu      s8, a3, s2
                  sh         t3, 1125(a1)
                  lb         t3, -1705(a1) #end riscv_load_store_rand_instr_stream_41
                  c.addi     s11, -16
                  mulh       a6, t2, s6
                  c.addi     t1, -19
                  lui        zero, 700553
                  div        a1, s7, t0
                  c.addi     s9, -26
                  c.addi     a0, 20
                  c.srai     a1, 22
                  c.srli     s0, 20
                  c.addi     gp, -31
                  divu       s4, s5, a4
                  c.slli     s6, 17
                  c.addi     a6, 9
                  c.slli     s9, 12
                  lui        t2, 902839
2475:             c.add      a4, a5
                  fence
                  c.lui      a6, 7
                  c.nop
                  c.addi     s2, 24
                  srl        a6, s9, t4
                  mulhu      s9, s0, s2
                  auipc      t2, 785640
                  srli       t1, a7, 10
                  slli       a1, ra, 13
                  lui        a2, 492005
                  c.addi     t6, -16
                  c.addi     t1, 19
                  c.addi     s2, 2
                  c.srai     s1, 20
                  c.addi     t2, -25
                  auipc      a4, 323929
                  lui        t4, 864476
                  auipc      gp, 311801
                  c.addi     t4, 30
                  srl        a7, t3, tp
                  c.srai     a2, 2
                  c.addi     a2, 16
                  sub        s10, s3, gp
                  lui        t6, 91381
                  c.srli     a4, 7
                  c.slli     t1, 30
                  c.addi     t2, -20
                  or         gp, s6, a2
                  c.addi     s10, -32
                  c.addi     s6, 1
                  bgeu       t3, t1, 2516f
                  c.addi     a5, 21
                  lui        a6, 539752
                  c.srai     s1, 29
                  auipc      a5, 258905
                  lui        a1, 856988
                  mulh       a7, a7, s8
                  c.addi     a7, -28
                  c.lui      s7, 14
                  la         s0, data_page_8+2125 #start riscv_load_store_rand_instr_stream_2
                  lw         a6, 1515(s0)
                  lb         t4, 1130(s0)
                  srli       a6, s2, 19
                  sb         a0, -1356(s0)
                  c.sub      a0, s0
                  lhu        t1, -1093(s0)
                  sb         t4, 164(s0)
                  rem        s4, t5, t5
                  lb         a3, -1726(s0)
                  lbu        s1, -1338(s0)
                  add        s7, a3, t3
                  c.addi     t3, -1
                  auipc      s11, 144141
                  lb         a2, 1006(s0)
                  c.srli     a0, 20
                  auipc      gp, 162967
                  c.lui      a6, 21
                  auipc      a4, 888620
                  lb         t6, 260(s0)
                  sb         s4, -740(s0)
                  lb         a1, 1146(s0)
                  sb         ra, -448(s0)
                  lui        a0, 111746
                  lbu        a1, 141(s0)
                  auipc      s10, 873882
                  sltu       a1, s5, tp
                  sw         s6, -473(s0)
                  lhu        t6, 1719(s0)
                  lbu        t1, 1607(s0)
                  lui        t2, 939958
                  lb         gp, -1147(s0)
                  c.srli     a2, 22
                  lb         s8, -1186(s0)
                  lb         s3, -1570(s0)
                  lbu        s2, 30(s0) #end riscv_load_store_rand_instr_stream_2
                  c.slli     s3, 29
2516:             c.addi     s2, -20
                  andi       s4, s5, -666
                  c.addi     s1, 16
                  c.xor      a4, a5
                  c.addi     t1, 21
                  c.lui      t2, 1
                  srli       s10, a4, 27
                  c.slli     t5, 29
                  c.or       a4, a2
                  c.lui      s7, 14
                  c.lui      a3, 2
                  c.slli     t4, 3
                  auipc      t3, 45033
                  c.addi     a4, 27
                  c.slli     s11, 31
                  lui        s11, 666960
                  c.lui      a1, 22
                  c.srai     s1, 26
                  c.addi     a4, 5
                  c.lui      a6, 14
                  c.addi     a7, 12
                  c.srai     s0, 4
                  auipc      a3, 588044
                  c.srai     a0, 16
                  or         s0, t3, zero
                  c.srli     a0, 6
                  c.addi     s2, -29
                  c.addi     a5, -18
                  auipc      a6, 694129
                  c.addi     s2, -21
                  c.lui      t4, 30
                  c.lui      s10, 17
                  c.bnez     a5, 2552f
                  c.addi     s0, -20
                  c.addi     t4, 21
                  fence.i
2552:             c.slli     a2, 15
                  blt        s9, zero, 2569f
                  c.addi     s11, 24
                  c.xor      s1, s0
                  c.lui      s4, 8
                  slli       t4, s11, 15
                  sll        s7, s0, s5
                  auipc      a0, 841525
                  c.addi     t3, -17
                  c.sub      a2, s1
                  andi       s9, t1, 860
                  auipc      s6, 664865
                  lui        t3, 549283
                  c.lui      t3, 11
                  c.addi     s2, -10
                  addi       a7, a5, 337
                  srl        s1, t1, t0
2569:             c.addi     s4, -10
                  c.srai     a5, 24
                  sub        s6, zero, s9
                  auipc      s9, 460186
                  beq        s10, a2, 2588f
                  lui        a7, 457644
                  bge        t1, t6, 2576f
2576:             lui        s8, 85532
                  c.slli     a3, 30
                  c.or       a4, a4
                  auipc      s6, 11396
                  c.xor      a4, a0
                  addi       s0, s11, 404
                  bltu       a3, s7, 2588f
                  c.lui      t3, 7
                  c.lui      t1, 19
                  c.addi     s11, -13
                  sub        a2, ra, t6
                  c.addi     s7, -20
2588:             lui        t3, 433658
                  c.srai     a4, 18
                  nop
                  andi       zero, a0, -698
                  lui        s11, 491966
                  auipc      s2, 222743
                  c.addi     s4, -24
                  sll        t1, ra, t6
                  auipc      a3, 888777
                  c.addi     t3, 6
                  slt        s3, s1, s0
                  lui        a2, 649583
                  bge        t5, tp, 2608f
                  auipc      t1, 1047723
                  sll        t5, s0, s8
                  c.addi     s10, -27
                  andi       gp, a0, -1023
                  fence
                  fence
                  c.addi     s0, -13
2608:             auipc      t2, 90273
                  auipc      t1, 623272
                  mul        a1, a0, s5
                  c.srli     a0, 2
                  c.addi     s6, 9
                  srl        s8, s10, a0
                  c.addi     s2, 16
                  lui        a5, 155746
                  c.addi     s7, 26
                  c.slli     s0, 10
                  c.addi     a7, 25
                  c.slli     t2, 15
                  auipc      s8, 274680
                  c.addi     a7, 8
                  c.addi     s6, -32
                  and        s1, s9, s4
                  c.addi     a3, -30
                  c.add      a5, a5
                  beq        s11, t2, 2644f
                  c.lui      a6, 3
                  add        t6, t1, t3
                  c.srli     a3, 2
                  blt        s11, ra, 2650f
                  c.slli     t2, 25
                  addi       a3, t6, -539
                  div        s4, a1, a3
                  c.srai     a0, 20
                  c.addi     a2, -8
                  c.nop
                  c.nop
                  c.srli     s1, 5
                  c.addi     s4, 8
                  la         s3, data_page_15+1831 #start riscv_load_store_rand_instr_stream_38
                  c.lui      s2, 28
                  c.addi     t6, 17
                  c.slli     s7, 28
                  lh         zero, 1681(s3)
                  sh         sp, 1667(s3)
                  sb         tp, -1457(s3)
                  fence.i
                  lhu        s9, -289(s3)
                  lb         a1, 1728(s3)
                  auipc      a6, 41648
                  srai       t6, s0, 28
                  c.srai     a4, 29
                  lui        s4, 23064
                  lbu        a3, 1140(s3)
                  sb         s1, -107(s3)
                  auipc      s11, 805943
                  c.andi     a0, 17
                  sb         s7, 1279(s3)
                  div        s8, s8, t6
                  c.lui      a0, 16
                  c.slli     t1, 22
                  fence.i
                  lh         t4, -1283(s3)
                  sb         t1, -503(s3)
                  lhu        a6, -417(s3)
                  c.srai     a4, 8
                  lbu        t5, 194(s3)
                  c.add      a2, a3
                  lhu        t4, -1295(s3)
                  sb         a5, 685(s3)
                  c.addi     t5, 14
                  c.addi     a4, 29
                  sh         ra, -209(s3)
                  c.addi     t4, 27
                  sh         s4, -1809(s3)
                  xori       s9, s11, -100
                  c.add      a1, s1
                  c.srai     a4, 10
                  nop
                  auipc      t4, 315074
                  lb         s11, -1300(s3)
                  lui        t1, 285538
                  sb         s11, -1062(s3)
                  xor        t6, t2, s2
                  sb         s2, 1626(s3)
                  c.li       a4, -26
                  c.xor      a5, a5
                  sw         t6, 2009(s3)
                  lbu        t5, 1812(s3)
                  c.addi     s2, -16
                  lh         s2, 551(s3)
                  sb         a7, -1165(s3)
                  c.addi     s1, -6
                  lhu        a1, 1771(s3)
                  sh         t4, -727(s3) #end riscv_load_store_rand_instr_stream_38
                  la         s10, data_page_7+1936 #start riscv_load_store_rand_instr_stream_50
                  c.addi     s6, 20
                  lbu        s0, -319(s10)
                  lb         t6, 1624(s10)
                  lhu        a7, -1042(s10)
                  lb         s0, -1589(s10)
                  c.addi     s3, 15
                  lb         a1, 1836(s10)
                  c.lui      t2, 24
                  c.addi     a1, 4
                  lb         t3, 1205(s10)
                  c.srli     a3, 20
                  sb         t1, 879(s10)
                  sra        t6, s5, a1
                  auipc      a5, 853821
                  auipc      a3, 176264
                  lui        t4, 926852
                  lb         s6, 1347(s10)
                  lb         a2, 1065(s10)
                  sb         gp, -685(s10)
                  c.xor      s1, a1
                  lbu        s7, -557(s10)
                  lb         s5, -1215(s10)
                  c.addi     t1, -19
                  lbu        t3, 969(s10)
                  lbu        s8, 1140(s10)
                  sb         a4, -569(s10)
                  lui        a7, 132380
                  lb         s5, -240(s10)
                  lui        s0, 213497
                  auipc      a4, 209883
                  lhu        t6, 686(s10)
                  sb         s3, -1009(s10)
                  c.slli     t4, 30
                  lbu        s9, 987(s10)
                  c.mv       s6, a5
                  sb         s3, 585(s10)
                  lbu        t3, 633(s10) #end riscv_load_store_rand_instr_stream_50
                  c.slli     t3, 2
                  c.addi     s0, -5
                  auipc      a0, 634640
                  lui        s7, 731993
2644:             c.addi     a3, -7
                  c.addi     t5, -11
                  c.srai     a4, 19
                  c.srai     a2, 5
                  lui        s3, 52963
                  c.add      a0, a2
2650:             lui        s1, 388621
                  c.addi     a5, 31
                  xor        a6, s1, tp
                  sll        s1, zero, t6
                  c.addi     a6, 29
                  xori       s1, tp, 403
                  c.addi     a7, -15
                  andi       s0, a0, -1010
                  la         s2, data_page_14+2190 #start riscv_load_store_rand_instr_stream_61
                  c.slli     t1, 8
                  c.lui      s1, 22
                  slt        t6, t1, s2
                  lb         s8, 233(s2)
                  c.xor      a2, s0
                  lb         a7, 1813(s2)
                  auipc      a7, 555858
                  lb         s6, 1001(s2)
                  c.addi     s8, 22
                  sb         a4, -255(s2)
                  lbu        zero, 389(s2)
                  sb         s6, 1257(s2)
                  sh         t0, -1898(s2)
                  auipc      s7, 467484
                  lbu        s11, -753(s2)
                  lh         a1, 1280(s2)
                  sh         ra, -536(s2)
                  andi       gp, s9, 629
                  auipc      s9, 579468
                  c.lui      s0, 6
                  sb         sp, 259(s2)
                  c.slli     t6, 25
                  sb         s0, -685(s2)
                  c.srai     a2, 29
                  sb         a0, -1021(s2)
                  and        a3, a5, t1
                  c.addi     s6, 9
                  sb         s10, -597(s2)
                  c.srli     a2, 15
                  nop
                  auipc      a0, 161872
                  sub        t3, t1, ra
                  c.addi     s7, -9
                  auipc      a4, 794185
                  lbu        s1, 1206(s2)
                  c.srai     a1, 11
                  lb         t3, -1893(s2)
                  lb         s6, 356(s2)
                  c.addi     a4, 22
                  andi       a0, a3, 907
                  lbu        s10, -2046(s2)
                  lbu        a6, -650(s2)
                  lbu        t3, -1600(s2)
                  lb         t4, 803(s2)
                  auipc      t2, 229542
                  c.nop
                  lh         t2, 0(s2)
                  xori       s5, t1, -145
                  lui        a7, 6301
                  c.srai     a3, 2
                  c.srli     a1, 10
                  sb         s1, 869(s2)
                  sb         t1, 918(s2)
                  lui        s6, 189018
                  lhu        t4, 1816(s2)
                  lb         gp, 353(s2) #end riscv_load_store_rand_instr_stream_61
                  c.slli     s5, 26
                  auipc      s2, 551348
                  andi       t3, t5, -408
                  auipc      zero, 706677
                  c.addi     s5, 2
                  auipc      s1, 297993
                  fence
                  bge        t2, s7, 2682f
                  lui        s9, 1028582
                  and        s7, a4, a2
                  c.addi     a4, 8
                  c.srai     a1, 7
                  c.addi     a5, 8
                  c.or       a5, a1
                  c.addi     a4, -16
                  auipc      t5, 322131
                  beq        t6, t5, 2694f
                  c.addi     t6, 13
                  fence.i
                  c.addi     s11, -9
                  c.addi     a2, -4
                  auipc      s3, 738218
                  auipc      s6, 506319
                  c.addi     a1, -23
2682:             srli       gp, s6, 14
                  lui        s10, 170574
                  c.addi     a4, -26
                  c.srai     a0, 13
                  c.srai     s0, 10
                  c.srli     a3, 7
                  slli       a2, a7, 4
                  lui        s9, 491907
                  lui        t3, 862907
                  lui        s7, 297531
                  andi       s10, a6, 781
                  lui        t3, 1041433
2694:             c.addi     a3, 26
                  c.srai     s1, 13
                  c.addi     s11, 14
                  lui        t6, 909931
                  auipc      s9, 200616
                  c.sub      a1, a1
                  c.lui      a6, 17
                  auipc      a2, 162863
                  lui        s6, 641093
                  auipc      s0, 213529
                  c.addi     s1, 30
                  c.addi     s10, 27
                  xor        s4, a7, a5
                  auipc      t1, 163842
                  c.andi     a3, 26
                  lui        s9, 1008752
                  c.addi     t3, -18
                  mulh       s11, t3, a0
                  c.addi     s6, -4
                  c.slli     s5, 5
                  c.lui      t4, 5
                  c.slli     t3, 26
                  div        s2, a6, s8
                  auipc      t3, 211174
                  c.addi     t3, 28
                  lui        a7, 673468
                  c.srai     a2, 8
                  lui        a2, 589829
                  lui        s3, 988449
                  lui        s3, 135151
                  sll        s9, t6, a4
                  lui        t4, 575899
                  c.srli     a4, 11
                  c.addi     s7, -16
                  c.addi     a4, -20
                  c.slli     s9, 26
                  c.addi     t1, -5
                  auipc      t6, 549703
                  c.addi     s1, 11
                  c.addi     t5, 10
                  lui        a2, 655698
                  nop
                  auipc      s10, 565116
                  c.addi     a1, 9
                  c.lui      s10, 8
                  lui        s8, 501949
                  xori       s8, a0, -705
                  mul        a4, a2, sp
                  lui        s2, 871933
                  c.add      a4, a4
                  auipc      s8, 63719
                  c.addi     s9, 19
                  auipc      s7, 812065
                  auipc      s7, 361570
                  c.srli     a0, 5
                  c.srai     a5, 21
                  lui        t6, 22804
                  c.slli     a2, 29
                  c.addi     a6, 3
                  c.addi     t4, -13
                  beq        tp, s4, 2772f
                  c.srai     a1, 14
                  auipc      s9, 112328
                  c.xor      a0, a1
                  c.addi     a1, 13
                  c.addi     a2, 15
                  c.srai     a4, 16
                  c.addi     t6, 27
                  c.mv       t4, t3
                  lui        s9, 843665
                  c.mv       a2, s8
                  beq        a2, s0, 2784f
                  c.srai     s1, 4
                  c.srli     s0, 18
                  c.srli     a4, 12
                  c.and      a1, a1
                  bltu       t3, a1, 2780f
                  c.nop
2772:             c.srai     a5, 22
                  lui        s3, 192841
                  lui        s4, 982267
                  c.addi     s4, 13
                  c.li       s4, -12
                  bge        t5, t2, 2791f
                  c.addi     s0, -12
                  remu       s1, s1, ra
2780:             c.addi     a1, 23
                  c.slli     s10, 27
                  lui        s4, 793059
                  lui        s1, 856929
2784:             c.srli     a0, 31
                  c.slli     s11, 31
                  c.slli     s5, 2
                  c.slli     a2, 22
                  slti       a4, t2, -595
                  c.addi     s2, 18
                  c.andi     a1, -7
2791:             c.srli     s0, 10
                  auipc      t4, 579795
                  mulh       a0, t0, s5
                  c.addi     s11, 30
                  c.add      a1, s1
                  c.addi     s10, -4
                  lui        s2, 456639
                  la         gp, data_page_1+1826 #start riscv_load_store_rand_instr_stream_55
                  lbu        a5, 1910(gp)
                  lbu        t6, -1653(gp)
                  c.xor      a0, a2
                  lui        s9, 644750
                  lbu        a6, 299(gp)
                  lbu        s10, 968(gp)
                  c.slli     s7, 27
                  sb         s7, -515(gp)
                  sb         a1, 1045(gp)
                  auipc      t4, 636552
                  sb         sp, -981(gp)
                  c.slli     s10, 23
                  lb         s9, -1729(gp)
                  lhu        s2, 314(gp)
                  fence
                  lhu        a2, 1252(gp)
                  c.addi     t1, -16
                  c.lui      s1, 15
                  c.srli     s0, 25
                  c.srli     a2, 16
                  lb         a0, -1273(gp)
                  c.addi     a1, 17
                  srli       s5, zero, 2
                  sb         zero, -1647(gp)
                  c.srai     a4, 10
                  lbu        t3, 1367(gp)
                  sll        t2, a1, s0
                  c.addi     a4, 15
                  c.addi     t5, -9
                  auipc      a5, 144588
                  c.addi     a5, 15
                  sb         s8, 772(gp)
                  c.addi     a2, -25
                  lbu        t1, -1802(gp)
                  lbu        s5, -73(gp)
                  divu       s7, s7, s9
                  sb         s2, 967(gp)
                  sh         t5, 146(gp)
                  c.slli     s3, 23
                  lh         s9, -40(gp) #end riscv_load_store_rand_instr_stream_55
                  c.addi     a3, -9
                  remu       s7, t2, s2
                  c.addi     a3, -25
                  lui        s11, 78300
                  c.addi     s9, 28
                  c.srai     s0, 9
                  c.addi     s11, 18
                  lui        t5, 1013736
                  c.mv       t3, ra
                  lui        a3, 346460
                  c.srai     s0, 10
                  c.addi     a7, 24
                  c.slli     t6, 18
                  c.addi     s4, 6
                  auipc      s6, 553960
                  c.addi     s5, 7
                  c.srli     a2, 19
                  auipc      t2, 466109
                  c.or       a0, a3
                  c.srli     s0, 7
                  c.addi     s8, -1
                  lui        t6, 200609
                  slti       s4, s11, -683
                  c.lui      s7, 8
                  lui        s2, 209606
                  lui        s3, 998287
                  auipc      a1, 217922
                  c.slli     t6, 18
                  c.li       gp, -16
                  c.add      a3, a4
                  la         s2, data_page_10+2220 #start riscv_load_store_rand_instr_stream_37
                  add        a1, t4, tp
                  c.srli     a4, 13
                  ori        t6, t2, -623
                  lbu        s8, -1789(s2)
                  c.srli     a2, 30
                  auipc      a6, 504941
                  c.addi     t1, -23
                  lb         t6, -551(s2)
                  lb         a0, 1172(s2)
                  lui        t1, 53052
                  c.addi     a7, -17
                  sb         t4, -1135(s2)
                  lh         s7, 1268(s2)
                  sb         sp, 547(s2)
                  auipc      a4, 501497
                  c.srli     a1, 23
                  lbu        t2, 1365(s2)
                  srl        gp, s8, s0
                  c.slli     t6, 27
                  sb         a5, -16(s2)
                  sh         t6, -1104(s2)
                  lb         t3, 1048(s2)
                  lbu        s1, -265(s2)
                  fence
                  c.addi     t5, -23
                  lb         t1, -1214(s2)
                  lbu        a7, 959(s2)
                  lhu        gp, -608(s2)
                  lbu        a0, 1285(s2)
                  lhu        s8, 312(s2) #end riscv_load_store_rand_instr_stream_37
                  divu       s2, s8, tp
                  mul        s5, t4, s11
                  c.addi     s4, -5
                  c.addi     s11, -11
                  auipc      zero, 451361
                  c.addi     t3, 27
                  c.addi     a5, -20
                  c.srai     a0, 11
                  auipc      s5, 752879
                  xor        s4, s10, s5
                  addi       a5, sp, 518
                  c.lui      s0, 30
                  lui        s0, 579577
                  srai       s5, a0, 16
                  c.addi     s6, 20
                  sub        a4, t5, s8
                  xor        s4, t0, t5
                  auipc      t6, 758666
                  auipc      s5, 340144
                  slli       t3, a4, 11
                  c.addi     a4, -10
                  lui        a0, 706266
                  lui        t5, 212987
                  c.srli     a0, 25
                  c.addi     t1, 1
                  auipc      a7, 237374
                  c.addi     t1, -6
                  c.addi     t3, 12
                  c.addi     a6, -6
                  c.addi     s2, -20
                  c.addi     a7, 29
                  c.srli     a2, 10
                  lui        s6, 782631
                  nop
                  slt        t2, a0, t1
                  slti       gp, s10, -655
                  c.lui      a3, 6
                  c.addi     a5, -10
                  c.addi     s4, -24
                  c.lui      t5, 17
                  auipc      gp, 258890
                  c.add      s1, a4
                  auipc      t1, 457915
                  c.srai     a1, 11
                  c.srli     a2, 20
                  c.addi     a0, 29
                  xori       a7, a5, 695
                  rem        a2, t2, s2
                  c.add      a0, a1
                  c.srli     a4, 31
                  c.addi     s1, -28
                  auipc      t6, 307432
                  lui        a2, 824088
                  fence.i
                  and        s3, a5, a5
                  c.addi     s5, -8
                  auipc      s11, 88457
                  c.srli     a0, 28
                  lui        s11, 30545
                  c.addi     a0, 22
                  auipc      s4, 96594
                  srl        s2, tp, s9
                  c.lui      a5, 8
                  c.lui      a0, 15
                  c.addi     s4, 10
                  c.srai     a2, 25
                  c.srli     a0, 18
                  c.addi     s5, -22
                  c.addi     a7, 10
                  lui        s9, 5235
                  lui        t6, 700972
                  c.li       s6, 4
                  c.mv       gp, t4
                  c.addi     t6, 31
                  c.srai     a0, 23
                  auipc      s2, 488494
                  c.addi     a2, -6
                  lui        s5, 662233
                  c.andi     a4, 11
                  lui        a7, 248149
                  c.srai     a5, 28
                  c.addi     a7, 2
                  srli       a2, ra, 0
                  c.sub      a0, a0
                  sltu       t4, gp, t0
                  c.srai     a5, 1
                  c.addi     s7, 27
                  lui        s7, 653010
                  bge        s3, a4, 2920f
                  c.addi     s9, -18
                  c.slli     a1, 20
                  c.srai     a0, 15
2920:             c.xor      s1, s1
                  c.addi     s11, -14
                  divu       s5, a2, s10
                  lui        t5, 385855
                  lui        s6, 572925
                  c.slli     s1, 11
                  c.srai     a1, 2
                  c.addi     s6, 22
                  c.add      a2, a1
                  c.addi     a7, 20
                  c.lui      a2, 10
                  c.addi     s8, -14
                  c.addi     a0, 24
                  c.addi     t6, -31
                  c.lui      t5, 6
                  bge        s7, t0, 2953f
                  auipc      t5, 310764
                  c.addi     s7, 14
                  srli       t2, s7, 31
                  slt        a7, t3, s8
                  c.addi     a0, 25
                  c.addi     s2, -24
                  srli       s2, t6, 10
                  auipc      s3, 1012994
                  c.slli     s2, 4
                  c.srli     a5, 14
                  c.slli     s2, 31
                  lui        t6, 179583
                  c.addi     a5, 19
                  c.addi     a1, -4
                  c.addi     s9, 29
                  c.srai     a1, 25
                  c.addi     t6, 20
2953:             c.addi     s2, 5
                  auipc      a4, 925480
                  c.srai     a2, 15
                  c.addi     t5, -24
                  auipc      s10, 147051
                  lui        s1, 364357
                  remu       s7, s9, s0
                  auipc      s8, 657167
                  lui        a5, 804981
                  c.lui      s5, 28
                  c.srli     a3, 1
                  c.srai     s1, 25
                  auipc      a3, 467140
                  c.or       a4, a3
                  c.addi     a6, -7
                  c.addi     t4, -17
                  c.addi     s6, -4
                  c.addi     t5, -24
                  c.lui      s10, 20
                  auipc      t2, 399589
                  auipc      s11, 856240
                  c.addi     t6, 26
                  c.addi     s9, 29
                  c.slli     a5, 28
                  c.addi     s3, -24
                  c.srli     a4, 10
                  c.or       a2, s1
                  c.li       s11, -19
                  c.addi     s1, -16
                  add        s1, s3, s10
                  c.srli     a1, 21
                  c.srai     s1, 21
                  auipc      gp, 645966
                  auipc      s11, 533920
                  c.addi     gp, 3
                  auipc      t3, 965730
                  lui        t3, 205092
                  c.nop
                  c.srli     a4, 26
                  c.addi     t3, -25
                  c.addi     s3, -20
                  lui        s11, 1024783
                  c.srai     a0, 11
                  c.addi     s4, -30
                  nop
                  c.srli     a4, 10
                  auipc      t3, 655833
                  auipc      s3, 788937
                  auipc      t3, 632490
                  c.xor      a2, a5
                  c.addi     s7, -19
                  c.srai     a0, 24
                  c.lui      t6, 8
                  c.slli     a2, 17
                  remu       t3, t4, s11
                  c.and      a4, a0
                  c.addi     s0, 27
                  c.srai     a3, 27
                  c.addi     a6, -11
                  auipc      s10, 1018261
                  c.addi     a0, 29
                  lui        a4, 908091
                  c.lui      t5, 6
                  auipc      a2, 900968
                  srai       s1, s5, 25
                  srl        s10, zero, s9
                  lui        gp, 588766
                  auipc      a4, 793097
                  c.addi     s2, -11
                  auipc      a6, 674430
                  xor        zero, a3, s8
                  c.srai     a3, 9
                  auipc      a6, 493605
                  c.srai     a0, 3
                  and        s7, t5, s1
                  c.addi     s2, -29
                  c.srai     a5, 5
                  c.nop
                  c.addi     a3, 23
                  lui        s6, 1033511
                  c.li       a0, 5
                  add        t2, s10, a2
                  c.addi     t4, -8
                  c.lui      s5, 8
                  c.slli     t5, 28
                  c.or       a2, s1
                  c.addi     s8, -23
                  lui        zero, 771279
                  c.addi     t5, -8
                  c.addi     s8, -26
                  c.addi     s6, -2
                  c.addi     gp, 12
                  c.addi     t4, 17
                  c.addi     gp, 12
                  c.li       t4, 11
                  auipc      a2, 553150
                  c.addi     a7, -18
                  fence
                  c.addi     t6, 16
                  c.addi     s1, -11
                  rem        s3, s2, s0
                  c.srai     a2, 3
                  lui        s3, 391379
                  c.add      a5, s1
                  addi       a7, t2, -407
                  c.slli     s2, 10
                  xori       a1, t3, 227
                  c.srli     a1, 15
                  c.addi     gp, -7
                  slti       a7, zero, -593
                  lui        s2, 647404
                  c.lui      s10, 26
                  c.li       s0, 17
                  auipc      s10, 154735
                  c.srai     a3, 5
                  c.srli     a2, 18
                  c.slli     a5, 27
                  auipc      s7, 662206
                  c.slli     s5, 23
                  blt        t2, gp, 3079f
                  c.addi     s8, -11
                  lui        s10, 714651
                  c.slli     a5, 29
                  c.srai     a3, 7
                  and        s6, a2, gp
                  c.addi     a6, -25
3079:             c.srai     a2, 29
                  c.addi     a3, 12
                  c.srai     a0, 22
                  c.slli     a2, 29
                  c.addi     s4, 16
                  c.addi     s9, 11
                  c.addi     t5, 30
                  c.lui      t3, 11
                  c.lui      t6, 5
                  remu       gp, a5, tp
                  beq        gp, s6, 3105f
                  c.srai     a4, 17
                  c.slli     a6, 6
                  c.srai     a4, 6
                  c.addi     s2, 20
                  c.addi     s7, -22
                  bgeu       s1, s9, 3099f
                  c.lui      s5, 12
                  c.slli     s1, 22
                  and        s3, a0, ra
3099:             auipc      s10, 730837
                  auipc      t1, 443011
                  mulhu      t1, sp, zero
                  c.addi     s2, -3
                  bltu       t2, s3, 3116f
                  auipc      a2, 400899
3105:             auipc      s6, 57656
                  c.mv       a1, s6
                  c.nop
                  auipc      t5, 577912
                  auipc      s2, 874064
                  divu       s10, s11, t5
                  c.andi     a2, 12
                  c.lui      t4, 18
                  c.addi     a0, 11
                  and        s4, gp, t3
                  c.slli     a1, 24
3116:             c.addi     t4, 2
                  c.addi     t4, 19
                  c.srai     a4, 10
                  auipc      gp, 675734
                  div        a2, s8, t6
                  c.lui      s1, 28
                  c.addi     s1, 9
                  lui        a7, 350061
                  c.slli     gp, 20
                  lui        s5, 581130
                  auipc      s2, 400731
                  c.addi     s9, 22
                  auipc      s11, 114308
                  c.srli     a4, 4
                  c.srai     a3, 27
                  c.lui      s0, 7
                  srl        s3, s0, s10
                  xor        t2, zero, t3
                  c.lui      t3, 4
                  or         gp, tp, s7
                  c.nop
                  c.addi     s1, 31
                  auipc      zero, 244823
                  fence.i
                  auipc      t5, 661491
                  c.addi     t1, -4
                  c.addi     s11, -9
                  c.addi     a7, -26
                  lui        s9, 552388
                  c.lui      t5, 26
                  auipc      t3, 472849
                  lui        a3, 668289
                  c.sub      a5, s1
                  c.bnez     a2, 3152f
                  c.lui      t3, 29
                  nop
3152:             slt        s9, s11, s0
                  c.addi     s9, 12
                  c.xor      a5, s0
                  c.slli     a2, 21
                  c.srli     a1, 9
                  c.addi     a1, -14
                  c.addi     t3, -5
                  addi       s4, a7, -896
                  c.srli     a2, 4
                  c.addi     s3, -18
                  c.srli     a3, 29
                  c.srai     a3, 3
                  auipc      a6, 827472
                  c.srai     a4, 24
                  c.srai     a2, 30
                  c.srai     a4, 3
                  c.and      a0, a0
                  auipc      s11, 922524
                  c.and      a4, s1
                  bge        sp, s9, 3176f
                  div        s2, a5, s2
                  xori       s3, t5, -609
                  c.lui      s7, 8
                  c.slli     t5, 14
3176:             bgeu       s9, ra, 3177f
3177:             lui        s0, 141203
                  lui        t1, 483318
                  c.addi     gp, 15
                  c.srli     a1, 21
                  slli       s4, a6, 13
                  c.lui      t6, 26
                  fence.i
                  auipc      s9, 173359
                  lui        a5, 462664
                  div        a7, a5, s0
                  auipc      a4, 936864
                  lui        s5, 564169
                  c.nop
                  c.addi     s6, -14
                  auipc      t2, 792707
                  mulh       a7, s5, s2
                  c.addi     a7, 1
                  c.addi     s10, 5
                  beq        t0, a5, 3200f
                  c.addi     s5, 23
                  c.addi     s2, -2
                  c.srai     a2, 7
                  c.srai     a5, 6
3200:             c.srli     a5, 3
                  c.lui      s6, 25
                  lui        s0, 308669
                  auipc      s5, 710984
                  c.addi     t3, 23
                  c.lui      s9, 10
                  lui        t1, 814267
                  lui        s9, 628894
                  auipc      a7, 616342
                  c.addi     s6, -1
                  c.addi     s8, -3
                  lui        a4, 868650
                  srai       t3, a0, 18
                  lui        s0, 25645
                  c.addi     s5, 19
                  c.addi     a1, -19
                  c.srli     a4, 25
                  c.srli     a3, 24
                  fence
                  c.addi     gp, 29
                  c.srli     s1, 16
                  c.addi     a3, -9
                  auipc      s11, 141877
                  sltu       a6, zero, a2
                  c.srai     s0, 15
                  c.addi     s5, 5
                  c.addi     s8, -5
                  c.addi     a5, 26
                  auipc      s0, 352431
                  c.lui      t1, 30
                  c.lui      a5, 15
                  c.addi     a7, 17
                  sltu       s9, zero, s4
                  lui        t1, 590252
                  c.nop
                  lui        t3, 293502
                  nop
                  auipc      s8, 23186
                  auipc      a3, 593943
                  c.slli     a1, 2
                  c.addi     s10, 29
                  bne        s7, gp, 3243f
                  c.addi     s8, -4
3243:             c.lui      s11, 22
                  lui        s11, 321348
                  auipc      s7, 835611
                  mulhsu     s0, s6, s7
                  slt        t6, t1, t4
                  lui        s8, 368192
                  c.addi     t2, 7
                  auipc      t5, 293503
                  c.lui      s4, 16
                  c.slli     a7, 27
                  c.addi     t6, -28
                  c.addi     s10, 30
                  auipc      a6, 1013614
                  auipc      t2, 1030471
                  c.slli     s6, 16
                  c.bnez     a3, 3262f
                  lui        s9, 544288
                  lui        zero, 737895
                  lui        s8, 904557
3262:             c.addi     a4, -6
                  c.srli     a3, 27
                  c.srai     s0, 15
                  auipc      s1, 434105
                  c.srai     a5, 3
                  c.lui      t5, 2
                  bltu       t5, a3, 3286f
                  xor        a6, t6, s6
                  c.srai     a5, 7
                  c.add      s0, a3
                  lui        t4, 451829
                  c.lui      t6, 16
                  c.bnez     a4, 3285f
                  slti       s6, zero, 751
                  auipc      a2, 173241
                  c.slli     s1, 8
                  c.addi     a6, 6
                  c.addi     a3, -24
                  auipc      a7, 902921
                  c.srai     s0, 13
                  c.addi     gp, -23
                  c.slli     a2, 14
                  lui        s6, 1004191
3285:             slli       a3, s0, 27
3286:             auipc      a7, 57439
                  xori       s9, s0, -941
                  divu       s2, a2, t0
                  auipc      a5, 439408
                  auipc      t4, 165754
                  c.addi     t2, -23
                  bne        s3, s2, 3304f
                  lui        a7, 944417
                  c.addi     a1, -29
                  slt        t6, s7, s8
                  c.mv       a1, a5
                  c.lui      a4, 31
                  c.addi     t2, -26
                  auipc      t3, 866865
                  auipc      t3, 432444
                  c.li       s9, -28
                  auipc      t5, 590473
                  sltiu      s7, a7, 689
3304:             slli       a7, sp, 14
                  mulh       t2, s0, s11
                  c.srai     a1, 29
                  c.addi     a1, -31
                  lui        t1, 261295
                  c.lui      a0, 19
                  blt        s3, gp, 3324f
                  mul        s11, a7, t3
                  auipc      s9, 1018338
                  c.srli     a2, 24
                  slt        s6, sp, s4
                  c.addi     a0, -3
                  srl        s11, a0, a4
                  srai       s11, s3, 0
                  auipc      a3, 819524
                  c.addi     t5, -17
                  c.lui      a2, 19
                  c.srai     s0, 10
                  c.addi     t6, -14
                  c.addi     s1, 4
3324:             lui        s11, 398898
                  lui        a6, 605900
                  la         a4, data_page_6+2291 #start riscv_load_store_rand_instr_stream_45
                  lbu        t4, -728(a4)
                  lui        t4, 320362
                  auipc      t1, 29453
                  lhu        t5, -1095(a4)
                  lhu        t5, -725(a4)
                  c.addi     s4, 1
                  andi       a0, a7, -778
                  c.or       s1, a0
                  lui        t3, 495236
                  sltu       t3, gp, a0
                  sh         a2, -923(a4)
                  c.li       t5, 21
                  sh         gp, -827(a4)
                  c.addi     t2, -3
                  sh         t2, -831(a4)
                  c.addi     s9, 14
                  lui        t6, 1022649
                  lui        a3, 670228
                  sb         ra, 890(a4)
                  lui        t3, 70039
                  nop
                  sb         s3, 711(a4)
                  sh         s2, -517(a4)
                  lui        a6, 485885
                  c.lui      s4, 10
                  lbu        s8, 1574(a4)
                  lbu        gp, 325(a4)
                  sb         s3, -1790(a4)
                  lb         s1, 455(a4) #end riscv_load_store_rand_instr_stream_45
                  c.addi     s3, 29
                  auipc      s2, 367580
                  c.addi     t4, 8
                  c.addi     a2, -4
                  lui        t3, 208163
                  c.addi     a3, -29
                  bge        t1, t4, 3350f
                  mul        s8, s3, t0
                  fence
                  c.mv       s5, s3
                  bltu       a5, a7, 3354f
                  mulhsu     t6, s11, t1
                  lui        t2, 281901
                  slti       a3, t5, 434
                  auipc      a6, 286446
                  c.srai     a2, 14
                  c.or       s1, a4
                  auipc      s0, 237954
                  div        s7, a0, a0
                  c.addi     a1, 24
                  c.srai     a0, 9
                  c.addi     a5, 6
                  auipc      a1, 744686
                  c.addi     s5, 24
3350:             auipc      s7, 196293
                  c.addi     t3, -4
                  fence.i
                  lui        s1, 611411
3354:             c.lui      s1, 27
                  sll        a1, sp, t1
                  c.lui      s2, 1
                  c.addi     a5, -15
                  c.addi     a5, -22
                  slti       a2, s3, -310
                  c.slli     s8, 4
                  c.srli     a3, 12
                  srai       t2, s2, 18
                  slli       s9, a5, 24
                  c.srli     s0, 23
                  c.lui      s10, 19
                  c.mv       a3, s7
                  c.srai     s1, 27
                  c.lui      a4, 31
                  lui        s8, 207839
                  c.addi     s11, 2
                  c.addi     t1, -6
                  c.addi     t4, -32
                  c.slli     t6, 27
                  la         a7, data_page_19+2443 #start riscv_load_store_rand_instr_stream_56
                  lbu        a1, -1169(a7)
                  lb         a4, -868(a7)
                  auipc      a4, 642532
                  lh         t4, -1507(a7)
                  c.addi     s2, -8
                  lb         a5, 1245(a7)
                  c.srli     a1, 25
                  c.addi     s10, -5
                  auipc      s2, 572825
                  lb         a2, 137(a7)
                  c.addi     s9, -20
                  c.srai     a4, 27
                  fence
                  lui        a2, 306910
                  lbu        s4, 226(a7)
                  nop
                  c.addi     s11, -10
                  sb         t5, -1130(a7)
                  lb         a6, 252(a7)
                  lb         s4, -1014(a7)
                  c.addi     t3, -26
                  div        a4, a4, t5
                  lb         a0, 211(a7)
                  or         t1, t3, a5
                  lb         a1, -902(a7)
                  sb         a0, 239(a7)
                  lbu        s2, -204(a7)
                  divu       t4, a3, a0
                  sh         s10, -1589(a7)
                  auipc      s4, 862613
                  lb         a5, 872(a7)
                  lb         s1, 1400(a7)
                  lbu        t5, -2020(a7)
                  c.lui      t4, 23
                  lui        t2, 687709
                  sh         s6, -537(a7)
                  lb         a0, 1222(a7)
                  sb         s1, -646(a7)
                  lhu        a4, 395(a7)
                  lbu        s10, 464(a7)
                  sb         s2, -673(a7) #end riscv_load_store_rand_instr_stream_56
                  lui        s5, 67006
                  auipc      s0, 192366
                  c.srli     a3, 5
                  bgeu       t4, a2, 3396f
                  c.lui      s0, 19
                  c.addi     a6, 8
                  c.nop
                  c.nop
                  c.slli     s0, 10
                  auipc      s1, 613961
                  c.srai     a3, 16
                  c.srai     s1, 17
                  c.li       a0, 7
                  c.add      s1, a1
                  bge        a2, s0, 3395f
                  c.bnez     a2, 3397f
                  auipc      s2, 1040322
                  c.slli     a2, 10
                  slti       s11, s10, 352
                  addi       s0, a0, -17
                  auipc      s2, 278276
3395:             c.addi     t1, 9
3396:             lui        s10, 209127
3397:             c.addi     a7, -22
                  auipc      t5, 829126
                  c.lui      t6, 25
                  c.addi     a5, -21
                  c.addi     t4, 25
                  c.li       a1, -15
                  c.lui      s4, 17
                  c.addi     t3, -1
                  c.addi     s8, -15
                  c.addi     s8, 16
                  c.srai     a2, 31
                  auipc      s3, 915780
                  c.slli     s7, 27
                  auipc      a4, 248796
                  c.or       a0, a0
                  lui        a5, 510120
                  c.addi     a1, -20
                  c.addi     s4, 29
                  lui        t1, 485799
                  c.addi     s3, 20
                  c.slli     s3, 16
                  c.addi     s11, 25
                  auipc      a6, 537207
                  remu       a7, t4, s10
                  c.lui      a1, 21
                  lui        a5, 406226
                  auipc      t6, 653086
                  c.addi     a1, 13
                  c.srli     a4, 5
                  rem        zero, s11, t5
                  c.addi     t4, -11
                  c.lui      a6, 6
                  c.srai     a2, 1
                  srai       a6, tp, 21
                  fence
                  c.slli     t1, 6
                  c.addi     t4, 12
                  c.addi     a6, -9
                  c.addi     s11, -18
                  sra        s8, s9, s11
                  c.srai     a4, 27
                  c.addi     a4, 24
                  c.li       t2, -19
                  mulh       s4, a6, t3
                  auipc      gp, 494690
                  c.addi     a6, -12
                  auipc      a4, 443763
                  blt        a2, a3, 3456f
                  sltiu      a4, s8, -993
                  srli       t6, s7, 31
                  c.lui      a6, 16
                  auipc      a1, 474995
                  c.srai     a1, 26
                  mulhu      t4, t1, a4
                  fence.i
                  c.srai     a0, 15
                  c.addi     t6, -30
                  c.addi     a0, -16
                  c.addi     s11, -30
3456:             c.addi     a2, 23
                  c.slli     s3, 29
                  remu       s3, s3, a5
                  auipc      a3, 686741
                  bltu       t2, t1, 3471f
                  c.addi     a2, 5
                  auipc      t5, 901749
                  mulh       a5, s8, a0
                  c.addi     t4, -20
                  auipc      t1, 337420
                  c.or       a1, a3
                  auipc      s7, 223075
                  sltiu      a7, s0, -689
                  auipc      a7, 847757
                  c.andi     a2, -32
3471:             sra        a1, t4, a7
                  auipc      s8, 774408
                  c.bnez     s0, 3491f
                  fence
                  c.lui      s9, 24
                  add        s3, s2, t1
                  auipc      a3, 317995
                  sltu       a1, t1, s3
                  c.slli     a0, 11
                  c.slli     s4, 23
                  c.lui      s10, 5
                  srai       a5, s0, 4
                  c.srai     s1, 18
                  srli       s8, s3, 17
                  c.addi     s4, -18
                  lui        t5, 683201
                  srl        s4, s7, tp
                  c.srli     a5, 21
                  c.addi     s4, 6
                  auipc      a7, 163888
3491:             auipc      s2, 297232
                  c.addi     s6, -28
                  c.addi     s0, -15
                  c.addi     a4, 18
                  c.srli     a1, 14
                  c.addi     s10, 5
                  lui        s5, 550125
                  c.addi     s2, -4
                  bgeu       ra, s2, 3517f
                  c.srli     a2, 6
                  c.srli     a0, 16
                  la         a1, data_page_3+2902 #start riscv_load_store_rand_instr_stream_3
                  c.slli     a3, 6
                  c.lui      s5, 18
                  lui        t6, 531252
                  sb         a4, 1007(a1)
                  c.addi     gp, -32
                  rem        t1, a2, a6
                  lb         t6, -1177(a1)
                  andi       s1, s7, -764
                  lui        s7, 823823
                  lhu        a4, -2048(a1)
                  lui        s8, 155598
                  lh         t2, -1714(a1)
                  lui        a4, 798761
                  lb         t6, -1645(a1)
                  sh         s6, -528(a1)
                  c.lui      s6, 14
                  c.addi     a2, -28
                  c.lui      a4, 11
                  c.addi     s4, 17
                  lbu        s6, -785(a1)
                  lui        s5, 529740
                  sh         t0, -40(a1)
                  c.addi     s1, 20
                  fence
                  c.lui      s10, 3
                  sb         a5, 123(a1)
                  lw         a7, 1162(a1)
                  and        s5, s10, t0
                  sb         s2, -573(a1)
                  lui        a4, 945065
                  c.sub      a0, a1
                  lbu        s0, 815(a1)
                  c.lui      s4, 16
                  sb         sp, -182(a1)
                  auipc      a5, 29527
                  sb         s2, 561(a1)
                  sb         a6, 407(a1)
                  c.addi     s2, 15
                  lui        a7, 872619
                  lw         s6, -1878(a1)
                  lw         s5, -110(a1) #end riscv_load_store_rand_instr_stream_3
                  c.srli     s1, 5
                  c.addi     a3, 14
                  c.addi     a0, -27
                  lui        a0, 600950
                  c.nop
                  andi       s5, s6, -627
                  auipc      a4, 719241
                  lui        s11, 103618
                  sltu       t5, a7, a4
                  c.srai     a0, 18
                  lui        a6, 796882
                  c.addi     s7, -30
                  c.addi     s11, -2
                  lui        a1, 216874
                  c.lui      s4, 2
3517:             auipc      s6, 1019032
                  c.lui      a3, 29
                  c.addi     s4, -32
                  lui        a7, 128394
                  c.slli     s4, 28
                  slli       s7, t1, 23
                  mulh       s8, s8, s11
                  c.lui      s0, 25
                  c.addi     a0, -14
                  c.addi     a1, -24
                  c.slli     s7, 20
                  bne        s2, a3, 3538f
                  srai       a0, t0, 7
                  auipc      s10, 989126
                  c.lui      t5, 24
                  c.and      a5, s1
                  c.addi     s10, 24
                  lui        a3, 193139
                  srl        a4, t0, t0
                  c.andi     a2, -12
                  la         s0, data_page_3+1990 #start riscv_load_store_rand_instr_stream_1
                  lbu        t3, -281(s0)
                  lui        s10, 499132
                  c.srai     a2, 11
                  lbu        t1, -1731(s0)
                  lui        a2, 336553
                  lbu        gp, 43(s0)
                  auipc      a0, 642756
                  c.add      a0, a0
                  sb         a5, 1043(s0)
                  c.srli     a3, 26
                  lbu        a0, 1556(s0)
                  lbu        t1, -97(s0)
                  auipc      s2, 899751
                  lui        a5, 624357
                  lb         gp, -622(s0)
                  c.srai     a1, 25
                  c.addi     a5, -1
                  lbu        a5, -1437(s0)
                  lui        s11, 667604
                  sb         s3, 1295(s0)
                  c.addi     a0, 31
                  c.addi     s1, 13
                  c.srai     a2, 5
                  lbu        t5, 2007(s0)
                  lbu        t5, -437(s0)
                  c.addi     a2, -11
                  lh         s3, -644(s0)
                  sb         a1, 58(s0)
                  c.lui      s1, 9
                  sh         a0, 1164(s0)
                  lbu        s3, 1735(s0)
                  c.srli     s1, 4
                  sb         s8, 1933(s0)
                  lb         a5, -1367(s0)
                  lbu        s4, 425(s0)
                  lbu        zero, -53(s0)
                  c.addi     a0, -4
                  lbu        s10, 191(s0)
                  c.srai     a3, 6
                  c.srai     a0, 20
                  c.lui      a3, 26
                  c.add      a3, s0
                  mul        s3, a5, a7
                  lbu        t5, -273(s0)
                  c.addi     s10, 5
                  nop
                  c.slli     a0, 17
                  auipc      gp, 476391
                  sll        t3, s1, s5
                  c.addi     s5, -22
                  sh         t0, -1970(s0)
                  lbu        a4, -564(s0)
                  sh         a4, 46(s0)
                  sb         a1, -1168(s0) #end riscv_load_store_rand_instr_stream_1
                  c.srai     s1, 15
3538:             c.addi     t4, -9
                  c.slli     s1, 17
                  c.addi     s5, 25
                  c.addi     s8, -16
                  fence.i
                  lui        s2, 80746
                  srai       s3, t1, 0
                  c.slli     s2, 15
                  c.addi     t5, 31
                  la         s3, data_page_4+1876 #start riscv_load_store_rand_instr_stream_25
                  c.slli     a5, 8
                  sra        s4, a0, gp
                  lh         a1, 868(s3)
                  mul        a1, t2, s5
                  lui        a5, 247481
                  sh         tp, 1590(s3)
                  sra        a0, t0, t6
                  c.addi     t4, 8
                  lhu        t2, 1918(s3)
                  c.srai     a5, 9
                  c.srai     a5, 18
                  slti       a1, t1, -196
                  c.addi     s5, -4
                  sb         a0, 1973(s3)
                  lui        t1, 876092
                  nop
                  lui        s10, 145238
                  c.srli     a1, 18
                  or         s9, s6, t2
                  lb         a1, -597(s3)
                  auipc      a5, 309178
                  lbu        t5, 649(s3)
                  sub        a4, s8, gp
                  c.lui      t4, 16
                  lui        s10, 897986
                  c.slli     s10, 16
                  lui        s7, 937843
                  lbu        t2, -1576(s3)
                  c.slli     a7, 26
                  c.slli     a5, 28
                  c.and      s1, a1
                  sb         s3, -1085(s3)
                  c.srli     a5, 1
                  lbu        a2, -487(s3)
                  c.addi     a1, 23
                  lb         s10, -1234(s3) #end riscv_load_store_rand_instr_stream_25
                  auipc      a0, 951703
                  bne        s11, t5, 3556f
                  c.lui      a7, 25
                  lui        a5, 1003822
                  andi       zero, a0, 924
                  c.slli     a3, 16
                  lui        gp, 847564
                  c.sub      s1, a2
                  auipc      t3, 1003090
3556:             c.addi     t6, 3
                  bne        s6, s8, 3559f
                  c.addi     a1, 25
3559:             c.addi     s0, -11
                  c.addi     s4, 20
                  c.srai     s0, 26
                  auipc      a4, 685925
                  c.addi     s4, -20
                  c.addi     s6, 6
                  lui        a7, 53506
                  c.srai     a0, 18
                  c.srai     a2, 12
                  c.addi     s4, -2
                  c.addi     t4, 24
                  bne        a1, s11, 3589f
                  c.addi     a5, -20
                  auipc      a3, 537891
                  c.addi     s8, 1
                  c.addi     a4, -4
                  c.andi     a2, 1
                  c.addi     a2, 19
                  lui        t3, 370318
                  bgeu       a4, a0, 3591f
                  c.addi     t4, 22
                  c.addi     s11, -8
                  lui        s1, 796015
                  beq        a6, s4, 3587f
                  auipc      a2, 68349
                  xori       t6, t6, 881
                  c.addi     gp, 30
                  c.addi     a4, 30
3587:             auipc      t1, 597889
                  c.addi     t2, 23
3589:             c.xor      a0, a3
                  lui        a0, 615082
3591:             c.srai     a2, 9
                  add        s3, a6, s7
                  c.srai     a2, 2
                  c.lui      gp, 2
                  c.lui      s3, 2
                  c.nop
                  auipc      s1, 551305
                  c.addi     a6, -15
                  lui        s1, 336881
                  c.slli     gp, 22
                  lui        s3, 396344
                  div        s0, a2, a2
                  c.addi     s6, 11
                  lui        t4, 662972
                  c.slli     t2, 6
                  c.addi     s7, -25
                  auipc      t4, 1007889
                  addi       s9, s8, 394
                  lui        t5, 696636
                  lui        s5, 554878
                  c.addi     a3, 21
                  c.addi     s1, -2
                  bne        t2, a7, 3614f
3614:             sll        a2, a3, t2
                  c.srai     a1, 6
                  c.addi     a5, -17
                  auipc      t2, 979639
                  c.addi     t5, -31
                  andi       t3, tp, -986
                  bltu       t5, s0, 3625f
                  lui        gp, 504220
                  c.srli     a4, 10
                  auipc      s8, 722919
                  c.addi     s3, 5
3625:             c.lui      s2, 13
                  c.lui      s8, 17
                  c.lui      s9, 19
                  c.addi     a1, -21
                  lui        a5, 358571
                  c.lui      s6, 28
                  lui        t1, 994817
                  c.addi     s9, 22
                  c.andi     s1, -16
                  c.slli     a0, 14
                  c.slli     a0, 26
                  c.srli     a2, 16
                  bltu       s7, tp, 3641f
                  c.andi     a5, -12
                  c.slli     s9, 26
                  c.addi     a3, 26
3641:             c.slli     s6, 16
                  c.srai     a0, 10
                  auipc      t4, 182205
                  auipc      t6, 358395
                  auipc      a7, 471618
                  c.lui      a7, 28
                  xori       s8, s5, -850
                  c.srai     s1, 11
                  c.lui      t3, 31
                  c.slli     s1, 4
                  c.sub      a1, a4
                  c.addi     s2, 5
                  bne        s3, s8, 3665f
                  and        t3, s10, t5
                  auipc      t3, 228872
                  c.andi     a2, -1
                  c.srli     a2, 24
                  auipc      t5, 233042
                  lui        s2, 972319
                  c.addi     s11, 8
                  c.addi     s0, 17
                  lui        s5, 688710
                  c.addi     s6, -15
                  c.srai     a5, 5
3665:             slli       a5, s11, 24
                  auipc      s11, 827994
                  c.addi     s10, 24
                  c.addi     s7, -29
                  c.srai     s0, 4
                  c.addi     t1, 27
                  c.srli     s0, 6
                  c.addi     gp, 20
                  sll        a0, tp, a5
                  auipc      s10, 300657
                  lui        a5, 687268
                  c.addi     t2, -14
                  c.li       t5, 20
                  c.srai     a1, 5
                  c.addi     gp, 24
                  lui        t4, 5106
                  c.addi     a6, -5
                  c.andi     a4, -17
                  fence
                  c.addi     s0, 18
                  c.addi     a3, 1
                  c.addi     s1, 3
                  c.addi     s5, 31
                  c.addi     s2, -19
                  c.addi     a3, 18
                  c.bnez     a0, 3696f
                  c.lui      t2, 23
                  c.addi     t5, 8
                  rem        s8, a5, t5
                  c.slli     s1, 12
                  c.addi     s11, 23
3696:             c.addi     s10, 10
                  c.srai     s0, 31
                  auipc      s5, 369716
                  auipc      s3, 816149
                  c.slli     a4, 31
                  c.addi     a7, -29
                  or         s6, s9, a4
                  c.srai     s0, 7
                  lui        a1, 79702
                  slti       t1, a7, -836
                  c.srai     a1, 15
                  c.lui      a2, 5
                  c.addi     s1, 22
                  auipc      s8, 945048
                  lui        t5, 440604
                  c.slli     s3, 30
                  lui        t2, 821838
                  c.addi     s6, 6
                  c.addi     a1, -5
                  c.srli     a2, 7
                  lui        zero, 741382
                  c.addi     s7, 7
                  c.addi     t1, -23
                  blt        s5, gp, 3735f
                  lui        a2, 497623
                  remu       t2, t1, s1
                  srl        t6, gp, s8
                  c.lui      a3, 29
                  c.srli     a1, 9
                  andi       zero, a3, 988
                  c.srli     a4, 14
                  c.srli     a3, 22
                  c.addi     s1, -1
                  ori        t2, t3, -827
                  and        s4, s5, a4
                  c.addi     s11, -15
                  xori       s8, a6, 375
                  sltiu      a6, t5, 705
                  c.addi     t4, -10
3735:             andi       s5, sp, 408
                  auipc      a6, 146421
                  c.lui      s10, 30
                  c.slli     a6, 31
                  c.srli     a1, 14
                  c.addi     a5, -4
                  div        a4, s10, a4
                  c.addi     t3, -31
                  c.srli     a2, 28
                  ori        a6, t4, -839
                  lui        a1, 935323
                  c.addi     s11, -31
                  c.srai     s1, 3
                  c.addi     s11, 24
                  auipc      t5, 277513
                  c.slli     t2, 30
                  c.addi     a2, 6
                  c.srai     a2, 24
                  auipc      gp, 1040024
                  c.srli     s1, 23
                  c.xor      a5, a0
                  rem        a4, s3, s4
                  c.addi     t1, 26
                  c.addi     s5, 23
                  slli       t3, s6, 20
                  lui        s10, 676902
                  auipc      a7, 876556
                  auipc      a1, 185585
                  slli       s10, s0, 30
                  c.lui      s7, 16
                  lui        a7, 900376
                  c.srai     a0, 3
                  lui        a6, 118797
                  auipc      a1, 130563
                  c.slli     s3, 15
                  blt        s7, tp, 3788f
                  auipc      s4, 159145
                  auipc      s5, 758862
                  c.srli     a0, 28
                  lui        s5, 208991
                  auipc      t4, 392977
                  c.slli     gp, 22
                  c.addi     s2, -16
                  c.addi     s9, 13
                  add        t1, s0, a0
                  auipc      a4, 169695
                  c.addi     s9, 9
                  c.addi     a7, 11
                  auipc      a3, 279196
                  c.lui      s8, 3
                  c.lui      t4, 26
                  lui        s4, 732573
                  sll        s3, a6, t3
3788:             c.slli     a4, 4
                  c.srai     a5, 8
                  c.addi     s1, -5
                  c.bnez     a3, 3807f
                  c.addi     s3, -17
                  c.sub      a0, s0
                  c.slli     a2, 7
                  addi       a2, a1, -522
                  c.addi     s4, -17
                  c.lui      a3, 4
                  c.srli     s0, 29
                  c.addi     a1, -5
                  c.addi     s9, 26
                  c.slli     t4, 17
                  and        a2, t6, s11
                  c.addi     s1, 16
                  c.slli     t1, 18
                  lui        a5, 448054
                  c.sub      s0, a2
3807:             lui        s3, 999302
                  c.slli     t4, 10
                  c.li       a7, -30
                  lui        s2, 331869
                  c.addi     s11, -15
                  c.addi     s6, -2
                  la         a7, data_page_13+2783 #start riscv_load_store_rand_instr_stream_13
                  sb         t4, -1058(a7)
                  sb         s8, -1569(a7)
                  sb         a2, -1853(a7)
                  lbu        a2, -1426(a7)
                  sb         s7, 363(a7)
                  lui        s9, 402083
                  sh         a4, 1269(a7)
                  lb         s3, 44(a7)
                  lbu        gp, -1082(a7)
                  auipc      t2, 845972
                  c.addi     a6, -13
                  sb         t1, -1274(a7)
                  sub        t3, a3, s10
                  lbu        s5, 943(a7)
                  sb         t0, -52(a7)
                  c.addi     a4, 17
                  lb         s10, 550(a7)
                  mulhsu     t2, s10, s11
                  c.addi     s6, -1
                  lb         s9, 187(a7)
                  lb         s9, 810(a7)
                  sh         t4, 1011(a7)
                  sw         sp, 361(a7)
                  lui        s8, 327374
                  lh         a6, -1403(a7)
                  lhu        a1, 991(a7)
                  and        s3, a6, s8
                  sb         t0, -59(a7)
                  c.lui      s8, 27
                  sh         a5, 915(a7)
                  lb         s7, -1809(a7)
                  lui        a3, 1036710
                  c.sub      a4, a1
                  lw         a4, -1767(a7)
                  mulhsu     a0, ra, t2
                  c.addi     a4, 22
                  lh         t6, -841(a7) #end riscv_load_store_rand_instr_stream_13
                  c.mv       s3, gp
                  c.srai     s1, 25
                  auipc      s10, 992949
                  lui        t5, 667471
                  remu       gp, a0, a6
                  c.addi     t1, 14
                  auipc      s6, 1009036
                  c.addi     a5, 31
                  fence
                  slti       t2, t1, 426
                  c.slli     a4, 17
                  c.lui      a3, 19
                  c.slli     s9, 13
                  lui        s5, 482503
                  auipc      s1, 634132
                  c.nop
                  auipc      t2, 150059
                  remu       gp, s1, zero
                  fence.i
                  c.and      a5, a2
                  c.xor      a5, a0
                  c.slli     t2, 17
                  c.addi     s2, 13
                  auipc      a3, 155700
                  c.addi     s10, -31
                  bltu       s3, a0, 3854f
                  bne        s8, s11, 3854f
                  c.lui      a5, 6
                  c.addi     t4, 23
                  lui        t2, 70018
                  auipc      t6, 597844
                  c.srai     s0, 28
                  c.srli     a1, 29
                  c.addi     s9, -29
                  c.lui      s2, 2
                  c.sub      s1, a5
                  sll        s5, s2, s1
                  c.lui      s9, 26
                  c.lui      t5, 12
                  c.lui      t2, 1
                  c.addi     s3, 4
3854:             c.srli     a4, 1
                  bne        a5, a3, 3872f
                  c.addi     s0, 23
                  bge        a0, t1, 3858f
3858:             c.srli     a3, 9
                  addi       s7, t0, -924
                  c.lui      a3, 2
                  slti       zero, a1, 633
                  lui        s9, 1045847
                  la         a3, data_page_7+2048 #start riscv_load_store_rand_instr_stream_12
                  add        t5, a3, a1
                  lbu        t1, -229(a3)
                  c.srli     a4, 20
                  slt        a0, s7, t2
                  lb         a5, 889(a3)
                  c.add      s1, s0
                  c.srli     a5, 20
                  c.andi     a5, -32
                  lui        a2, 915920
                  lh         t6, 798(a3)
                  c.srai     a0, 1
                  or         s0, a0, t5
                  lbu        a4, 937(a3)
                  lui        s6, 652475
                  xor        t5, s7, t3
                  c.xor      a0, a1
                  add        t6, s10, a5
                  c.addi     s1, -28
                  sb         s2, -512(a3)
                  lhu        a1, -1474(a3)
                  auipc      s3, 136561
                  lbu        a4, 1786(a3)
                  sb         s11, 1751(a3)
                  lh         zero, 160(a3)
                  lui        s2, 712232
                  lhu        t4, 1564(a3)
                  c.lui      s3, 31
                  sw         a7, 1192(a3)
                  lb         gp, -1313(a3)
                  c.addi     s3, 27
                  lb         s6, -1911(a3)
                  c.srli     a0, 20
                  auipc      s3, 235304
                  c.srai     a1, 12
                  lui        zero, 1008468
                  c.srai     a5, 13
                  sb         t5, 507(a3)
                  c.addi     s0, -2
                  lb         a7, -345(a3)
                  lb         s6, 770(a3)
                  c.srai     a5, 10
                  lb         s3, -1438(a3)
                  lbu        s2, 1301(a3)
                  sb         a2, 189(a3) #end riscv_load_store_rand_instr_stream_12
                  c.addi     a4, -13
                  c.addi     a2, 20
                  c.addi     s1, 20
                  c.srli     s1, 26
                  lui        s9, 152670
                  c.addi     s5, -16
                  c.addi     s3, -24
                  c.addi     t1, -30
                  c.addi     t1, 9
3872:             c.lui      t3, 6
                  lui        a0, 116938
                  c.lui      t6, 18
                  lui        s11, 413009
                  beq        t2, s3, 3883f
                  lui        a3, 698169
                  c.addi     a5, 20
                  sra        s9, a6, a3
                  c.lui      s6, 22
                  auipc      a7, 670722
                  add        s1, ra, gp
3883:             lui        s2, 204354
                  c.addi     a0, -7
                  auipc      a2, 669010
                  c.slli     t2, 1
                  add        t5, a7, s6
                  auipc      a2, 2393
                  c.lui      a4, 18
                  auipc      s8, 691507
                  auipc      a2, 793358
                  la         s5, data_page_19+2322 #start riscv_load_store_rand_instr_stream_47
                  lbu        s9, 1477(s5)
                  lbu        s4, -1725(s5)
                  c.addi     a3, 6
                  c.srli     a3, 11
                  add        zero, gp, a1
                  lw         s4, 162(s5)
                  lb         t4, -765(s5)
                  divu       s3, s3, s7
                  c.addi     t4, -12
                  c.sub      s0, s1
                  sb         tp, 1521(s5)
                  c.srli     a0, 28
                  lb         s10, 769(s5)
                  c.slli     s6, 17
                  lw         a3, -1510(s5)
                  sh         t3, -760(s5)
                  c.addi     s4, -6
                  c.lui      t5, 5
                  sltiu      s1, zero, 444
                  auipc      zero, 742034
                  lh         s4, 724(s5)
                  lbu        a6, 1465(s5)
                  c.sub      a4, a0
                  c.li       t6, 31
                  c.addi     a1, 31
                  c.srli     a2, 20
                  lhu        s2, -1270(s5) #end riscv_load_store_rand_instr_stream_47
                  blt        t4, s10, 3906f
                  lui        a4, 517722
                  c.slli     s0, 3
                  c.srai     s1, 23
                  addi       a2, t5, 303
                  c.addi     s9, 31
                  c.addi     s11, -17
                  c.lui      a0, 13
                  bge        s8, a6, 3905f
                  c.slli     s8, 7
                  c.srai     a5, 4
                  c.lui      s2, 23
                  ori        s3, a2, -329
3905:             c.srai     a1, 22
3906:             c.slli     s3, 7
                  auipc      t1, 149573
                  lui        a1, 612166
                  c.addi     t1, -22
                  c.slli     a5, 2
                  c.addi     t4, -20
                  c.li       a0, 31
                  lui        s6, 349520
                  lui        s6, 217973
                  c.addi     s10, -3
                  auipc      a7, 429384
                  c.addi     a3, 27
                  fence.i
                  auipc      s11, 872464
                  c.addi     s5, -21
                  lui        a4, 693597
                  lui        a5, 422462
                  c.addi     a2, -21
                  c.addi     a1, 21
                  c.addi     t5, 1
                  c.lui      s10, 11
                  c.addi     a2, 30
                  c.srli     a0, 28
                  c.srai     s0, 5
                  bge        t1, gp, 3935f
                  c.lui      a2, 20
                  auipc      a2, 565936
                  c.andi     s0, 11
                  c.srli     s1, 24
3935:             rem        s3, s5, s10
                  c.slli     a7, 20
                  c.srli     a2, 11
                  c.srai     s1, 8
                  auipc      s5, 282827
                  auipc      t6, 168697
                  c.xor      s1, a1
                  c.srai     s0, 10
                  la         t4, data_page_5+1947 #start riscv_load_store_rand_instr_stream_22
                  c.slli     a1, 2
                  c.addi     s5, -24
                  sb         zero, -540(t4)
                  srai       a1, gp, 4
                  c.srli     a1, 18
                  mulh       a7, s9, gp
                  c.srai     a4, 3
                  lb         a4, -224(t4)
                  auipc      s10, 873506
                  c.li       a6, 1
                  c.addi     s3, 5
                  sb         s7, -688(t4)
                  lui        zero, 954228
                  lb         zero, 244(t4)
                  lbu        t2, 1230(t4)
                  sltiu      s9, t3, -980
                  lb         a2, -1809(t4)
                  c.srli     a5, 27
                  lbu        s10, 1787(t4)
                  lhu        s6, 1041(t4)
                  lui        s10, 645143
                  or         s1, a3, a7
                  lw         s11, -899(t4)
                  c.addi     s1, -25
                  lbu        a1, 1238(t4)
                  lui        a4, 962793
                  c.srli     a3, 16
                  c.slli     s9, 30
                  sll        s8, a5, s8
                  sb         t1, 838(t4)
                  c.lui      t2, 13
                  add        a3, a5, s3
                  lb         t6, -406(t4)
                  c.srli     a3, 20
                  lbu        a6, -1292(t4)
                  lui        t1, 359839
                  auipc      s8, 366870
                  c.addi     s8, 21
                  sll        t2, t5, zero
                  c.lui      a5, 20
                  sb         a2, 172(t4)
                  sb         s11, 1074(t4)
                  sh         ra, -1843(t4) #end riscv_load_store_rand_instr_stream_22
                  c.addi     a5, -31
                  auipc      t6, 137011
                  c.addi     t5, -6
                  fence.i
                  lui        a2, 672688
                  c.addi     a1, -9
                  ori        s1, a5, 1020
                  lui        a6, 108752
                  c.lui      a3, 22
                  slti       s2, s4, -674
                  c.srai     a4, 17
                  bltu       s10, a2, 3960f
                  divu       a6, a6, t0
                  auipc      s10, 1035725
                  c.srai     s1, 27
                  auipc      s5, 304512
                  c.addi     a5, 3
3960:             c.srai     a2, 3
                  andi       a4, s7, -483
                  c.addi     t2, 16
                  auipc      s1, 372288
                  c.srli     a2, 13
                  lui        s3, 802264
                  c.addi     s8, 11
                  lui        a4, 177377
                  c.addi     gp, -15
                  c.slli     s2, 30
                  c.srli     s0, 5
                  lui        t2, 687115
                  c.addi     s1, 7
                  c.addi     s6, -31
                  c.slli     a5, 26
                  c.slli     s2, 17
                  c.addi     a2, 11
                  auipc      a4, 957133
                  c.addi     a6, -1
                  lui        a1, 649422
                  c.addi     t1, 12
                  sll        s10, s2, gp
                  c.srli     a4, 27
                  bgeu       a5, s11, 3994f
                  c.addi     s3, 13
                  div        t3, s2, s7
                  c.srai     a0, 27
                  lui        s0, 575662
                  c.srai     a0, 3
                  c.srai     a0, 28
                  c.add      a5, a4
                  c.beqz     a5, 4005f
                  c.slli     a6, 10
                  c.lui      s10, 27
3994:             auipc      a5, 318165
                  c.addi     a5, -9
                  c.addi     a7, 7
                  lui        t2, 477766
                  c.lui      t1, 12
                  bge        s9, ra, 4018f
                  fence.i
                  c.addi     s0, 31
                  beq        s2, tp, 4022f
                  auipc      t4, 442896
                  c.addi     s7, -25
4005:             fence
                  beq        t3, t0, 4015f
                  c.addi     s7, 29
                  auipc      t4, 532961
                  c.slli     s5, 15
                  ori        t4, t1, 67
                  lui        a1, 508326
                  lui        a1, 993176
                  addi       zero, t3, -679
                  auipc      zero, 380829
4015:             c.addi     t3, -14
                  c.srai     s0, 21
                  c.srli     a3, 6
4018:             c.srai     s0, 31
                  c.addi     s1, 1
                  slli       s0, a0, 3
                  c.addi     s3, 22
4022:             auipc      t3, 115687
                  c.lui      s11, 29
                  xor        s4, tp, a3
                  c.addi     t3, 2
                  c.slli     t5, 18
                  c.addi     t2, -30
                  sra        t4, t3, s6
                  c.addi     s5, -16
                  c.addi     s11, -7
                  mul        s10, s11, gp
                  mul        s8, s0, a7
                  c.beqz     a2, 4051f
                  c.addi     s7, -29
                  lui        s7, 259104
                  lui        t1, 128850
                  c.lui      s6, 10
                  c.addi     a6, 5
                  auipc      s10, 357426
                  c.slli     a2, 13
                  lui        gp, 1044911
                  c.lui      a4, 17
                  c.addi     a0, 25
                  c.slli     t4, 2
                  c.addi     a6, -21
                  lui        zero, 129082
                  lui        a4, 147695
                  c.srai     a1, 16
                  auipc      a1, 458918
                  lui        s6, 498931
4051:             c.addi     a0, 11
                  lui        s6, 444350
                  lui        a7, 809854
                  c.addi     s1, 7
                  mulhu      a4, s1, t2
                  auipc      t3, 939273
                  auipc      s11, 287593
                  lui        t5, 88290
                  c.srli     a3, 12
                  slti       s0, s0, 96
                  c.addi     a7, 12
                  c.addi     s8, -31
                  auipc      a0, 386670
                  auipc      a4, 511492
                  c.addi     t4, -28
                  c.addi     s11, -16
                  c.addi     a2, 17
                  auipc      t2, 721980
                  c.slli     a2, 25
                  c.slli     t4, 1
                  fence.i
                  c.srai     a1, 18
                  c.addi     s7, 6
                  c.li       s1, -14
                  auipc      zero, 996921
                  c.addi     s3, 1
                  c.srai     a4, 19
                  auipc      t1, 700006
                  c.lui      a0, 7
                  auipc      s3, 576321
                  c.slli     a0, 31
                  c.mv       s10, a4
                  srai       s9, a4, 17
                  xor        t3, t5, s10
                  lui        s3, 695038
                  mulh       s3, a0, s9
                  c.lui      s8, 17
                  auipc      a0, 964724
                  c.srli     a4, 15
                  c.addi     t1, -12
                  c.addi     a7, -3
                  c.srli     a5, 28
                  c.slli     s0, 2
                  c.addi     s7, 17
                  c.srai     s1, 31
                  lui        s8, 888452
                  lui        s6, 398545
                  auipc      t4, 845050
                  auipc      a6, 4204
                  lui        s10, 682032
                  auipc      s6, 273031
                  c.lui      t4, 10
                  c.srai     a1, 5
                  c.addi     s7, 17
                  c.addi     a2, 3
                  c.addi     s7, -32
                  auipc      s4, 612170
                  c.lui      a0, 17
                  c.addi     s11, 29
                  lui        s7, 55491
                  and        s4, s6, a2
                  or         a5, s11, gp
                  c.lui      s5, 11
                  c.srli     a5, 20
                  c.addi     a4, -8
                  auipc      s0, 1003004
                  c.slli     s2, 5
                  c.addi     t2, -10
                  c.addi     t6, -7
                  auipc      s3, 762068
                  auipc      a6, 729246
                  c.slli     a0, 7
                  c.addi     s8, -10
                  la         s5, data_page_15+2573 #start riscv_load_store_rand_instr_stream_34
                  lui        t5, 815093
                  c.srli     a3, 29
                  divu       t6, tp, s2
                  c.srli     a3, 31
                  c.addi     s9, 11
                  sb         s0, 624(s5)
                  lb         s8, -1668(s5)
                  c.addi     a5, 12
                  lhu        a5, -1579(s5)
                  auipc      gp, 433835
                  lui        gp, 57534
                  c.slli     s4, 5
                  lb         a4, -19(s5)
                  lui        a0, 1011884
                  auipc      s2, 859902
                  lh         s4, -891(s5)
                  lb         s2, -821(s5)
                  c.slli     s2, 16
                  lbu        s8, -1696(s5)
                  srl        a1, a7, t0
                  c.slli     a6, 27
                  auipc      s7, 626500
                  remu       zero, t4, s10
                  lbu        t3, 1460(s5)
                  lh         a5, -1039(s5)
                  c.addi     s8, -30
                  c.srai     a1, 26
                  slli       a5, t4, 0
                  sb         a1, 1185(s5)
                  c.addi     t6, 15
                  c.addi     s1, -6
                  c.addi     s1, -28
                  sh         tp, -1383(s5) #end riscv_load_store_rand_instr_stream_34
                  srli       a0, tp, 3
                  c.addi     s5, 26
                  c.addi     a6, 27
                  c.srai     s0, 6
                  lui        t3, 571052
                  auipc      a7, 529551
                  slt        t5, s6, s6
                  nop
                  mul        a6, a3, s3
                  c.slli     a7, 11
                  auipc      t5, 551142
                  slli       a5, gp, 15
                  c.srai     a1, 20
                  nop
                  lui        s2, 533832
                  c.slli     a1, 7
                  c.lui      t6, 28
                  la         t5, data_page_1+2088 #start riscv_load_store_rand_instr_stream_16
                  c.addi     s1, -31
                  c.lui      a5, 22
                  sb         zero, -1469(t5)
                  lbu        s9, 473(t5)
                  c.srai     a3, 15
                  lui        s3, 464789
                  c.sub      s0, a4
                  c.slli     s1, 30
                  auipc      a5, 711984
                  auipc      s8, 703828
                  sb         s0, 1439(t5)
                  sltiu      s7, t2, -83
                  c.addi     a0, 8
                  sltiu      s8, s6, 643
                  c.addi     t3, 25
                  auipc      s8, 850458
                  slli       a7, t1, 3
                  auipc      a1, 2924
                  sh         tp, 698(t5)
                  c.li       t3, -25
                  sb         s9, -818(t5)
                  c.lui      s1, 26
                  c.slli     a7, 10
                  c.addi     a7, 20
                  lb         s8, -57(t5)
                  lbu        a6, -786(t5)
                  srl        s0, t0, s0
                  c.lui      t4, 6
                  lb         a4, -517(t5)
                  c.lui      t6, 13
                  sb         a6, 523(t5)
                  add        a4, gp, a4
                  auipc      a0, 483835
                  c.or       a5, a2
                  lui        s0, 1020498
                  sb         t1, 235(t5)
                  mul        t4, s9, a5
                  sh         a2, 884(t5) #end riscv_load_store_rand_instr_stream_16
                  c.bnez     a1, 4158f
                  c.addi     s4, 18
                  auipc      s1, 771464
                  c.lui      s2, 9
                  auipc      s1, 1014007
                  c.srai     a5, 29
                  c.slli     a7, 15
                  mul        a0, s0, s6
                  lui        s2, 846729
                  c.beqz     a1, 4167f
                  lui        s5, 988694
                  c.srli     a1, 15
                  lui        a3, 770481
                  c.lui      s10, 25
                  slti       a3, s11, -336
                  c.slli     a0, 9
                  lui        t6, 189898
4158:             auipc      s0, 80966
                  auipc      s3, 748568
                  slli       a7, zero, 25
                  ori        s10, t5, -733
                  c.srli     a5, 4
                  ori        s8, s9, 107
                  c.srai     a3, 16
                  c.addi     s8, -1
                  c.beqz     s1, 4170f
4167:             c.addi     s5, -24
                  c.lui      a5, 4
                  slli       a2, t1, 3
4170:             c.lui      t2, 28
                  c.addi     gp, 26
                  c.slli     t2, 29
                  c.lui      t1, 22
                  lui        a7, 1019963
                  c.mv       s11, s1
                  c.addi     s0, 27
                  c.addi     a1, 29
                  addi       t6, s7, -789
                  c.addi     t2, -4
                  c.lui      s3, 28
                  remu       a1, a1, a6
                  lui        s2, 729837
                  slt        a2, ra, a5
                  c.slli     gp, 2
                  c.nop
                  lui        a4, 1011889
                  c.addi     t1, 6
                  c.srai     a3, 19
                  bge        tp, a2, 4192f
                  c.addi     s11, -31
                  c.addi     s2, 4
4192:             slt        t1, s1, s1
                  c.beqz     s1, 4200f
                  auipc      t3, 324097
                  auipc      t4, 474314
                  c.lui      a3, 20
                  c.srli     a0, 16
                  lui        s5, 923963
                  c.addi     s7, 26
4200:             remu       s9, sp, s3
                  auipc      a5, 479149
                  addi       a6, s11, -285
                  c.srli     a3, 18
                  rem        t3, s7, s11
                  auipc      s4, 121112
                  c.srai     a5, 11
                  c.slli     a2, 21
                  rem        a1, a4, a4
                  c.slli     s10, 23
                  c.srli     a1, 18
                  lui        t3, 364975
                  c.lui      t2, 18
                  c.lui      a7, 31
                  c.addi     t5, -31
                  la         t6, data_page_6+2125 #start riscv_load_store_rand_instr_stream_44
                  lw         t3, -265(t6)
                  lb         s4, -1303(t6)
                  c.addi     a6, 24
                  lb         s10, -914(t6)
                  c.addi     t5, -29
                  auipc      t1, 120627
                  lbu        t5, 1324(t6)
                  sh         sp, -473(t6)
                  lb         t4, -86(t6)
                  sb         s5, -2026(t6)
                  c.addi     s10, 24
                  lbu        t5, -561(t6)
                  lh         a2, 1695(t6)
                  lb         a4, 971(t6)
                  c.addi     s10, 30
                  sb         gp, 1602(t6)
                  lui        t4, 923299
                  lhu        a7, 1465(t6)
                  lw         s0, 1439(t6)
                  c.srai     s1, 28
                  sb         a1, -2036(t6)
                  c.addi     s4, 17
                  c.addi     t3, 26
                  lbu        t5, -1913(t6)
                  sll        s9, s1, s0
                  lb         s7, 423(t6)
                  c.srli     a1, 4
                  lb         s1, -1310(t6)
                  c.addi     t1, -8
                  c.srli     a0, 11
                  c.addi     s11, 21
                  c.lui      t1, 4
                  lhu        s7, 819(t6)
                  lw         s10, -2037(t6)
                  sh         t0, -1169(t6)
                  lw         a4, 1171(t6)
                  c.slli     gp, 20
                  sb         t1, 1516(t6)
                  lhu        a7, -839(t6)
                  c.addi     s1, 30
                  lui        a6, 69946
                  lhu        s0, 1049(t6)
                  lb         a3, -1236(t6)
                  sb         t3, 1582(t6)
                  sb         s1, -938(t6)
                  c.srai     a5, 26
                  c.addi     s1, -20
                  lhu        s3, 1415(t6)
                  sb         s11, -1622(t6)
                  lb         s7, -1139(t6) #end riscv_load_store_rand_instr_stream_44
                  c.srai     a2, 23
                  c.addi     a6, -29
                  c.addi     t6, -16
                  slli       s7, t0, 1
                  c.addi     s2, -16
                  auipc      gp, 291790
                  c.addi     s9, 6
                  auipc      a2, 387614
                  auipc      t3, 779622
                  lui        zero, 822729
                  c.addi     s8, -4
                  c.slli     s5, 29
                  srai       s1, t5, 8
                  remu       a7, tp, gp
                  auipc      t4, 384941
                  andi       a0, s3, 805
                  c.addi     a5, 9
                  c.sub      s1, a0
                  c.lui      s7, 22
                  nop
                  add        t1, t6, a6
                  lui        a3, 29435
                  c.add      a5, a0
                  c.andi     a0, -9
                  remu       zero, s8, gp
                  c.srli     a0, 7
                  c.slli     s1, 12
                  mulhsu     a1, s8, a5
                  c.addi     a7, -8
                  c.slli     t5, 5
                  c.srai     s0, 13
                  c.srai     s1, 20
                  c.slli     s10, 27
                  lui        s7, 593334
                  c.addi     gp, -21
                  slti       a7, t4, -513
                  auipc      a5, 59022
                  c.addi     a5, -11
                  auipc      s9, 658138
                  lui        a4, 874361
                  auipc      s11, 985381
                  c.addi     s6, 12
                  auipc      s11, 147140
                  c.addi     t5, -1
                  fence.i
                  c.slli     a6, 1
                  auipc      a1, 248720
                  xori       t2, s9, -254
                  add        a7, s10, zero
                  c.srli     s0, 6
                  and        s3, s11, a3
                  addi       s1, a1, 418
                  c.srli     a2, 10
                  mul        a6, s9, s9
                  auipc      s4, 83414
                  c.addi     t3, 29
                  xor        s8, a3, s11
                  c.srli     a4, 29
                  c.lui      a2, 4
                  c.srai     a2, 5
                  c.slli     a0, 19
                  nop
                  c.addi     t3, 22
                  c.srli     a2, 1
                  sra        s2, ra, a0
                  auipc      t1, 723947
                  c.lui      a2, 28
                  mulh       s11, s6, a1
                  auipc      a3, 231331
                  c.addi     s10, 27
                  c.lui      s9, 29
                  c.addi     a0, -5
                  xori       t3, tp, -443
                  sra        s2, ra, a5
                  rem        t3, t3, a2
                  auipc      s3, 141987
                  lui        s11, 993312
                  mulhsu     t5, s5, s1
                  auipc      s10, 873125
                  lui        s1, 55914
                  c.addi     s8, -8
                  c.addi     t1, 1
                  auipc      a6, 890897
                  c.srli     a3, 21
                  c.addi     a4, 14
                  slli       a0, s0, 3
                  c.beqz     a4, 4309f
                  c.srli     a5, 14
                  c.addi     s5, -27
                  auipc      s1, 72964
                  lui        s0, 976843
                  auipc      a3, 341822
                  c.addi     t4, -6
                  auipc      a7, 762922
4309:             c.addi     s8, 28
                  c.srai     a5, 4
                  mulhsu     s5, s4, s0
                  and        a0, s5, a7
                  c.srai     s1, 4
                  c.addi     gp, -25
                  c.nop
                  lui        a1, 225917
                  auipc      t4, 631163
                  c.addi     s7, -31
                  c.addi     a4, 24
                  auipc      t4, 676961
                  bne        t5, s5, 4324f
                  auipc      t3, 388077
                  auipc      s10, 31265
4324:             c.addi     s3, -6
                  and        a1, gp, s9
                  lui        t4, 816288
                  c.addi     t1, -16
                  c.slli     t5, 17
                  c.slli     s5, 21
                  add        t6, ra, t6
                  c.addi     a7, -25
                  div        t4, a3, a3
                  c.lui      a6, 9
                  c.addi     s5, 22
                  c.srai     a0, 12
                  c.addi     t3, -12
                  c.lui      t4, 8
                  c.addi     t2, -5
                  c.addi     s1, 16
                  c.srai     a0, 31
                  lui        t5, 796312
                  c.srai     a2, 14
                  c.addi     s0, 26
                  c.srli     a4, 23
                  and        s10, t1, s9
                  c.srli     s0, 15
                  slti       s0, t3, 389
                  c.addi     a0, -21
                  lui        a3, 1014673
                  c.addi     s10, -1
                  fence
                  c.slli     a5, 26
                  slti       a6, t2, 716
                  auipc      a3, 861151
                  c.addi     a1, 8
                  sltu       s7, a7, s8
                  c.srli     a4, 10
                  c.srai     a5, 6
                  mulhu      s0, s11, s10
                  c.lui      s9, 17
                  c.addi     a5, 24
                  c.srli     a3, 5
                  lui        s3, 606985
                  auipc      zero, 1011110
                  mulhsu     t1, t3, a3
                  c.addi     s0, -31
                  lui        a1, 6400
                  lui        a0, 443953
                  c.srai     a3, 24
                  c.addi     s0, 13
                  c.addi     t1, 27
                  c.srli     a5, 4
                  xor        gp, a1, zero
                  mulhu      s10, t5, s1
                  c.srai     a4, 9
                  c.slli     s2, 10
                  auipc      t3, 145106
                  lui        a2, 230282
                  sra        a0, s10, s8
                  auipc      a2, 283426
                  lui        a5, 207359
                  c.addi     a5, 30
                  c.add      a5, s1
                  c.addi     s7, 21
                  c.addi     s0, -29
                  rem        s3, a3, s4
                  nop
                  c.add      a5, a5
                  c.srai     a4, 25
                  sra        s2, zero, a7
                  lui        t3, 582730
                  c.lui      t4, 11
                  ori        a3, t1, -32
                  c.srli     a4, 4
                  c.lui      s2, 25
                  beq        a1, s3, 4414f
                  c.addi     a2, 10
                  c.addi     s6, 7
                  c.addi     a4, 2
                  auipc      a2, 840778
                  bge        t3, a7, 4405f
                  c.srli     a0, 22
                  srai       t6, a4, 10
                  auipc      s8, 699310
4405:             or         s10, s1, t5
                  c.addi     s9, 5
                  c.addi     s9, -24
                  c.addi     t4, -8
                  c.mv       gp, s0
                  c.lui      a5, 5
                  c.nop
                  auipc      s11, 30214
                  auipc      s5, 280226
4414:             auipc      t4, 851418
                  auipc      t2, 744163
                  lui        s5, 902376
                  remu       a1, s7, t1
                  fence
                  c.slli     s4, 4
                  auipc      s2, 734632
                  slt        s6, t5, t5
                  bltu       t4, zero, 4432f
                  xor        zero, s7, zero
                  slli       s2, s8, 5
                  srl        s3, s9, zero
                  c.addi     s5, 16
                  lui        a0, 472024
                  c.addi     t1, 8
                  c.addi     t6, -31
                  lui        s2, 724004
                  slti       a5, s3, 272
4432:             c.addi     s7, -26
                  c.addi     t1, 7
                  slt        a4, s1, t0
                  slt        gp, t4, s9
                  sll        gp, a7, s4
                  divu       s10, a0, ra
                  addi       s5, s11, 138
                  lui        s2, 420567
                  c.slli     a0, 24
                  c.addi     a2, 18
                  auipc      t3, 47286
                  c.addi     s1, -7
                  c.srli     a5, 28
                  c.addi     s0, -13
                  c.addi     t2, -32
                  auipc      a0, 199552
                  c.addi     gp, -12
                  c.srai     a5, 11
                  c.addi     t3, -7
                  c.addi     s4, -32
                  c.lui      t6, 11
                  c.addi     a4, -14
                  mul        a2, s11, s5
                  auipc      a5, 636745
                  c.addi     s6, 26
                  lui        a1, 533414
                  c.slli     a6, 20
                  mulh       t3, sp, t5
                  c.lui      s7, 2
                  xori       s4, t5, 271
                  mul        t6, s10, t1
                  mulhu      gp, s10, a7
                  c.addi     s9, -21
                  c.addi     s0, 29
                  c.srai     s0, 22
                  c.addi     a7, -7
                  c.slli     t3, 29
                  c.lui      t4, 29
                  c.srli     a5, 12
                  c.srai     a2, 5
                  lui        s6, 835969
                  c.srli     a4, 23
                  c.srli     a0, 7
                  sll        s6, gp, s11
                  c.srai     a5, 11
                  auipc      a3, 652411
                  auipc      t4, 930274
                  srl        s0, s3, a2
                  c.srai     a0, 3
                  c.addi     s2, 4
                  c.lui      a3, 9
                  c.addi     gp, -15
                  bge        a0, s5, 4494f
                  c.srai     a0, 11
                  bge        s8, t6, 4491f
                  auipc      s8, 563934
                  c.slli     t3, 5
                  c.addi     s7, -22
                  c.addi     s4, 1
4491:             blt        t6, a2, 4507f
                  c.addi     a2, 16
                  c.addi     s10, -22
4494:             c.slli     gp, 16
                  c.addi     t4, 27
                  lui        s6, 408265
                  c.addi     s9, -25
                  c.srli     a3, 21
                  c.addi     a0, 24
                  slti       a7, a0, -861
                  c.addi     t6, 9
                  c.and      a4, s0
                  nop
                  auipc      t1, 913741
                  lui        a1, 648746
                  lui        s11, 904945
4507:             c.srai     a1, 22
                  c.srai     a2, 25
                  c.addi     s8, 6
                  c.slli     a5, 28
                  lui        a1, 756121
                  auipc      s4, 136290
                  slt        s5, a4, s7
                  c.addi     a7, 14
                  c.addi     t5, 21
                  c.lui      t3, 7
                  c.xor      s0, a4
                  c.lui      s9, 4
                  bne        s2, t5, 4530f
                  xori       s9, t2, 595
                  la         s11, data_page_6+2335 #start riscv_load_store_rand_instr_stream_66
                  lb         s4, 628(s11)
                  sh         s6, -365(s11)
                  lb         a0, 1498(s11)
                  sb         a7, 831(s11)
                  c.nop
                  sb         gp, 1284(s11)
                  sb         t1, 998(s11)
                  lhu        s9, 1747(s11)
                  lbu        t3, 1299(s11)
                  auipc      a5, 644480
                  c.srai     s0, 20
                  lb         s3, -1841(s11)
                  lbu        t2, -274(s11)
                  srl        s7, a0, sp
                  c.addi     a5, 31
                  sw         a1, 309(s11)
                  remu       s2, a3, s7
                  lbu        a3, 140(s11)
                  sb         a3, -1328(s11)
                  mul        s9, tp, s8
                  lb         s1, -1846(s11)
                  lhu        s7, -1657(s11)
                  lh         s4, -1829(s11)
                  addi       a5, s9, 166
                  lui        s9, 82216
                  sb         s10, -1246(s11)
                  c.srai     a0, 23
                  c.lui      a1, 26
                  auipc      a2, 560078
                  sh         a6, 941(s11)
                  sb         s11, -341(s11)
                  c.lui      s4, 5
                  sb         t3, 1406(s11)
                  sb         t2, 1749(s11)
                  lb         s5, 1400(s11)
                  lbu        a1, 1118(s11)
                  c.slli     t3, 20
                  lh         a3, 297(s11)
                  lbu        a6, -1484(s11)
                  lui        a4, 978621
                  fence
                  c.addi     t6, 28
                  lb         a3, 1735(s11)
                  auipc      a5, 277471
                  sb         gp, -1166(s11) #end riscv_load_store_rand_instr_stream_66
                  c.lui      a3, 21
                  c.slli     t2, 12
                  la         s7, data_page_18+1982 #start riscv_load_store_rand_instr_stream_68
                  c.addi     a1, -13
                  sb         s1, 1889(s7)
                  c.addi     s11, -5
                  lb         a4, -963(s7)
                  auipc      a5, 599389
                  c.or       a2, a2
                  mul        t5, s5, t5
                  fence
                  lb         s1, -525(s7)
                  c.and      a5, a2
                  lbu        s6, -667(s7)
                  c.srli     s1, 2
                  c.addi     a3, 23
                  auipc      t1, 168119
                  lui        t1, 1043390
                  c.slli     t1, 22
                  lhu        s5, -364(s7)
                  lb         s0, -1665(s7)
                  div        a2, sp, a3
                  sb         a6, -828(s7)
                  c.lui      a6, 7
                  c.addi     s5, -7
                  c.addi     t5, -31
                  add        a6, a6, sp
                  c.add      a1, a5
                  lhu        t6, -792(s7)
                  c.slli     t2, 22
                  lui        t5, 126243
                  lbu        a6, -760(s7)
                  lui        a0, 1043503
                  c.slli     s3, 22
                  auipc      t2, 571002
                  lw         t2, 1586(s7)
                  slt        t3, s9, zero
                  auipc      s5, 96094
                  auipc      s6, 255165
                  lbu        s10, -403(s7)
                  lui        s9, 970464
                  c.lui      t3, 20
                  c.addi     s1, 16
                  sb         a5, 1220(s7)
                  c.addi     t6, 17
                  lbu        s2, 77(s7)
                  sw         a1, 1950(s7) #end riscv_load_store_rand_instr_stream_68
                  srli       s7, tp, 4
                  c.addi     s9, 12
                  sltu       t1, tp, s9
                  c.addi     s1, -23
                  c.srai     a1, 16
                  sltiu      a0, s8, 610
                  c.srli     a3, 2
4530:             c.addi     s2, -23
                  c.srli     a0, 21
                  auipc      s8, 651943
                  c.lui      a3, 14
                  c.srli     a3, 20
                  auipc      s7, 465333
                  c.addi     a3, -11
                  c.srai     a2, 12
                  lui        t3, 982559
                  c.addi     s4, 29
                  xori       s8, zero, -493
                  nop
                  auipc      s8, 956215
                  la         s11, data_page_15+1831 #start riscv_load_store_rand_instr_stream_58
                  or         t4, a6, s10
                  c.and      a2, a5
                  c.addi     s1, -8
                  sb         a6, 737(s11)
                  lui        gp, 575660
                  divu       t4, ra, a4
                  lb         s9, 1414(s11)
                  sb         t2, -1428(s11)
                  lb         t3, 274(s11)
                  mulhu      a0, t1, a7
                  lb         s8, 90(s11)
                  c.li       s9, 2
                  sb         a2, 618(s11)
                  sh         s7, 931(s11)
                  lb         t2, 138(s11)
                  lh         a4, 1011(s11)
                  auipc      a2, 335282
                  c.add      s1, a3
                  c.addi     gp, -31
                  c.addi     a6, 21
                  auipc      zero, 923122
                  lbu        a5, 231(s11)
                  lhu        t2, 879(s11)
                  sw         t6, -707(s11)
                  c.slli     s0, 20
                  mulhu      s4, t0, sp
                  lui        s5, 511311
                  lb         t6, 442(s11)
                  lh         s0, -815(s11)
                  c.li       t5, -9
                  lbu        a6, -1313(s11)
                  lhu        s10, 1963(s11)
                  c.srai     a2, 30
                  auipc      a7, 566302
                  auipc      a5, 646040
                  lw         a7, -1279(s11)
                  fence.i
                  c.li       s2, 30
                  auipc      a0, 317318
                  lh         s7, -1459(s11)
                  lb         s0, 446(s11) #end riscv_load_store_rand_instr_stream_58
                  auipc      s0, 325999
                  c.addi     a5, 31
                  lui        a3, 132916
                  c.srai     s1, 9
                  c.lui      s5, 5
                  c.srli     a2, 31
                  c.srli     a3, 29
                  c.srai     a1, 8
                  c.addi     a5, -12
                  bne        ra, s3, 4554f
                  c.addi     a5, -13
4554:             c.addi     s3, -2
                  lui        t2, 236932
                  c.addi     a6, -31
                  c.slli     a3, 28
                  la         s10, data_page_11+1971 #start riscv_load_store_rand_instr_stream_6
                  nop
                  sb         t6, -629(s10)
                  c.addi     s9, -32
                  auipc      s3, 925628
                  lbu        zero, -1817(s10)
                  c.slli     s6, 3
                  or         a7, t2, sp
                  c.addi     s0, 28
                  xor        a0, a4, s4
                  lbu        a0, -1536(s10)
                  lb         t1, -1182(s10)
                  xori       a4, s11, 127
                  lbu        s7, -338(s10)
                  c.addi     s3, -22
                  lbu        a5, -807(s10)
                  c.mv       s2, a5
                  c.srai     s0, 25
                  lb         a3, 1420(s10)
                  c.xor      a3, a1
                  sb         a4, -638(s10)
                  lui        a3, 360054
                  c.addi     a6, -24
                  lui        s1, 1025620
                  c.sub      a1, a3
                  lb         s2, -208(s10)
                  sb         s2, -457(s10)
                  lbu        s7, -816(s10)
                  sb         s11, 1123(s10)
                  lb         a2, 695(s10)
                  c.addi     t3, 25
                  lui        s2, 874784
                  lhu        a5, 883(s10)
                  sb         s4, 708(s10)
                  lb         s6, -53(s10)
                  lui        t6, 891818
                  lh         s3, 1157(s10)
                  c.addi     a5, 9
                  c.addi     t6, 17
                  c.lui      t6, 3
                  lhu        t4, 571(s10)
                  sb         zero, 814(s10)
                  lui        s3, 557897
                  lb         s6, 444(s10)
                  c.addi     s6, -6
                  lb         t6, -1412(s10)
                  c.slli     s9, 14
                  lb         a3, 1252(s10)
                  c.srli     a3, 2
                  lb         t5, -1753(s10) #end riscv_load_store_rand_instr_stream_6
                  auipc      s5, 399855
                  c.addi     s2, 11
                  c.slli     s3, 8
                  beq        s7, t0, 4575f
                  c.lui      s11, 4
                  c.addi     gp, -7
                  c.addi     s0, 31
                  c.addi     s3, -22
                  c.slli     a1, 6
                  auipc      a7, 660917
                  auipc      a1, 28151
                  auipc      s0, 110551
                  c.andi     a2, 3
                  c.addi     s7, -15
                  lui        gp, 794557
                  auipc      a3, 832147
                  lui        s7, 348548
4575:             c.addi     a0, -5
                  c.srli     a2, 3
                  bne        s3, a3, 4591f
                  lui        a3, 313988
                  lui        a4, 40263
                  mul        t1, tp, zero
                  nop
                  c.addi     s11, 9
                  c.andi     a4, -28
                  c.addi     a2, -2
                  c.addi     t5, -8
                  mulhsu     zero, s8, t6
                  auipc      a7, 140559
                  c.lui      a5, 24
                  slt        a7, s10, s6
                  c.addi     s2, -12
4591:             c.srli     a3, 1
                  c.srli     a5, 7
                  c.slli     t4, 29
                  fence
                  auipc      t3, 996736
                  lui        t1, 890615
                  c.or       a3, a5
                  lui        s10, 188815
                  fence.i
                  c.slli     t4, 21
                  c.addi     a6, -5
                  c.xor      a1, s0
                  lui        a7, 430332
                  auipc      a7, 109331
                  c.srli     a0, 4
                  c.srai     s1, 28
                  sll        a3, t2, sp
                  c.lui      t1, 2
                  c.addi     s5, 7
                  lui        s0, 567848
                  lui        s2, 329753
                  div        a1, zero, sp
                  c.srai     a1, 20
                  c.slli     s4, 1
                  lui        s2, 640068
                  slt        a7, zero, ra
                  auipc      s10, 371638
                  lui        s10, 45665
                  c.addi     s0, -2
                  c.srai     a3, 25
                  auipc      t3, 255572
                  c.addi     t3, -23
                  mulh       s9, s4, a2
                  add        s7, t5, a6
                  c.addi     t5, -13
                  c.slli     a4, 16
                  c.addi     t4, 22
                  c.srli     a3, 13
                  c.addi     s11, 12
                  c.or       a2, a1
                  c.sub      a0, a3
                  addi       s9, t3, -249
                  lui        a1, 238451
                  lui        t6, 365134
                  lui        a6, 887286
                  c.lui      a0, 17
                  c.mv       s8, a1
                  lui        zero, 712323
                  addi       s8, s0, -18
                  c.lui      s5, 23
                  srl        t5, a6, s1
                  c.srli     s1, 20
                  c.srai     a4, 24
                  lui        a4, 165270
                  lui        s5, 282653
                  c.addi     s1, -18
                  c.addi     s4, -8
                  c.addi     t1, 28
                  c.addi     a5, -30
                  c.addi     s7, -20
                  c.slli     s9, 17
                  c.srai     s0, 4
                  beq        ra, a3, 4661f
                  add        t3, a1, s1
                  c.srli     a1, 1
                  c.addi     s9, -19
                  c.lui      s11, 16
                  c.addi     gp, -11
                  c.srli     a3, 24
                  bne        a5, t1, 4677f
4661:             auipc      zero, 90440
                  c.srai     s1, 27
                  c.addi     a1, 9
                  c.addi     a0, 11
                  c.lui      s2, 13
                  divu       a2, s2, t2
                  c.addi     s6, -9
                  c.srai     s0, 21
                  c.srai     a5, 20
                  c.addi     a5, -4
                  c.addi     t1, -14
                  c.addi     s10, 23
                  c.addi     s1, 5
                  c.srli     a2, 16
                  nop
                  c.srai     a3, 6
4677:             c.addi     t2, 31
                  auipc      s8, 504364
                  c.srli     a2, 27
                  c.addi     s4, 27
                  c.or       a2, a4
                  mulhsu     a1, s11, t5
                  c.lui      a7, 23
                  c.srai     a4, 14
                  c.addi     a5, -27
                  lui        s7, 937973
                  c.slli     a2, 13
                  c.xor      s1, a5
                  rem        a1, t1, s0
                  c.xor      a4, a0
                  auipc      a7, 180322
                  c.addi     s11, 20
                  c.lui      s6, 31
                  c.addi     t1, -13
                  slt        a2, s4, t2
                  lui        a4, 332318
                  sltiu      a1, s2, 883
                  auipc      t1, 860042
                  c.and      a5, a3
                  c.srai     a2, 7
                  c.addi     t1, 3
                  c.addi     s7, -12
                  auipc      t6, 833854
                  lui        a1, 5711
                  auipc      gp, 1014400
                  lui        s3, 999928
                  c.addi     a7, -13
                  mulh       a6, t6, s2
                  fence.i
                  auipc      s3, 465351
                  c.addi     a7, 29
                  c.addi     t6, -17
                  lui        a5, 315945
                  c.or       a5, a0
                  lui        s1, 169703
                  c.addi     s3, -7
                  or         a7, gp, s10
                  c.addi     a4, 26
                  c.slli     s3, 23
                  c.srli     a0, 24
                  c.addi     a4, 16
                  c.srai     a2, 26
                  c.addi     t1, 29
                  c.srai     a5, 5
                  c.addi     gp, 20
                  c.lui      s4, 23
                  auipc      s11, 311221
                  fence.i
                  c.addi     a2, -28
                  sll        t4, zero, t5
                  sll        a0, gp, a4
                  c.addi     t4, 25
                  c.and      a2, a2
                  c.srai     a2, 2
                  c.addi     a4, -21
                  c.addi     t4, -22
                  c.addi     t6, -8
                  c.addi     s0, 26
                  c.addi     a7, -15
                  c.srai     a1, 28
                  c.srai     a3, 13
                  slt        s6, tp, gp
                  or         a3, s5, s8
                  c.addi     a1, -17
                  c.addi     a4, -10
                  c.addi     s5, -29
                  auipc      a1, 502577
                  c.addi     a3, -17
                  c.lui      t2, 21
                  lui        a4, 304520
                  c.addi     t3, 14
                  lui        s7, 889348
                  div        a0, ra, s9
                  c.srai     a0, 8
                  c.addi     s9, -9
                  c.or       s0, s0
                  c.srli     a4, 28
                  lui        a5, 219914
                  lui        a0, 316260
                  c.lui      a0, 31
                  auipc      t3, 859197
                  c.mv       s1, s3
                  c.addi     s9, 25
                  c.addi     s10, -24
                  fence.i
                  c.addi     a0, -32
                  nop
                  lui        a7, 463008
                  c.srai     a5, 22
                  c.addi     s3, 7
                  c.srai     a5, 19
                  xori       t2, gp, -1009
                  c.addi     s10, -8
                  mulhu      s11, s0, ra
                  c.addi     s9, -20
                  c.slli     s7, 9
                  c.srli     a0, 7
                  c.slli     a3, 16
                  and        a0, a5, t5
                  c.srai     a4, 19
                  lui        t2, 466581
                  c.lui      s11, 15
                  bge        a6, s6, 4792f
                  c.slli     s3, 19
                  c.slli     s11, 4
                  c.addi     a6, -1
                  srli       a4, a3, 22
                  c.slli     t3, 11
                  c.and      s0, a2
                  c.lui      t2, 1
                  c.addi     t1, -14
4792:             c.addi     t2, -5
                  sll        s6, t4, a4
                  c.addi     s4, 24
                  auipc      s6, 563201
                  lui        a3, 292051
                  c.slli     s10, 3
                  bne        sp, s9, 4799f
4799:             c.addi     s8, -14
                  c.li       a1, 5
                  or         s2, sp, s6
                  lui        a1, 250240
                  c.addi     s6, -14
                  c.addi     t6, 26
                  c.slli     s9, 19
                  c.addi     s5, 13
                  and        gp, t2, t1
                  c.lui      t1, 7
                  c.addi     s10, -15
                  srli       t2, t4, 12
                  c.lui      a3, 26
                  c.addi     a2, 1
                  lui        gp, 996606
                  c.slli     t6, 20
                  c.lui      a3, 14
                  c.srli     a0, 30
                  c.addi     t2, -21
                  nop
                  c.addi     t2, 29
                  slli       t5, a6, 26
                  c.addi     s6, 30
                  lui        s4, 659953
                  c.addi     gp, 29
                  c.srli     a5, 18
                  c.srai     a5, 7
                  auipc      t5, 1033850
                  lui        s5, 81019
                  addi       s7, t0, -849
                  c.slli     s5, 2
                  c.or       a3, a3
                  c.srai     a0, 3
                  c.lui      t4, 19
                  c.addi     a6, 17
                  c.addi     s5, 16
                  c.srli     a2, 10
                  lui        s8, 766742
                  c.addi     a6, 28
                  c.nop
                  lui        a4, 225744
                  lui        t2, 190057
                  c.srli     a4, 24
                  mulh       s11, a6, t1
                  c.srai     s1, 17
                  auipc      a4, 816702
                  c.addi     s3, 10
                  auipc      a0, 68611
                  c.mv       s2, ra
                  fence
                  beq        ra, sp, 4867f
                  mul        s1, t3, a5
                  auipc      s4, 869470
                  c.slli     t5, 3
                  c.addi     t3, 3
                  lui        a4, 793230
                  c.lui      s1, 12
                  c.addi     a3, -2
                  sra        a3, a5, a0
                  c.addi     a0, 21
                  beq        a6, a3, 4866f
                  auipc      a2, 319873
                  lui        a2, 304187
                  c.lui      a4, 19
                  c.addi     a3, -13
                  c.addi     t3, 20
                  c.addi     s5, 22
4866:             c.addi     a6, -14
4867:             c.srli     a1, 10
                  auipc      zero, 551031
                  fence
                  c.addi     s1, -17
                  lui        a2, 71385
                  c.andi     a5, 3
                  c.srai     s1, 18
                  slti       s11, s6, 283
                  c.addi     s2, 13
                  lui        t6, 791507
                  la         s3, data_page_9+1954 #start riscv_load_store_rand_instr_stream_9
                  ori        s2, a2, -189
                  lb         a6, 1579(s3)
                  auipc      a7, 898302
                  lb         a1, -681(s3)
                  auipc      t3, 412787
                  lhu        s4, 1612(s3)
                  sb         t6, 29(s3)
                  c.srai     a0, 26
                  auipc      s1, 339851
                  c.addi     t4, 13
                  xori       a4, gp, -633
                  divu       t4, a0, a5
                  lbu        t5, 859(s3)
                  c.slli     s5, 25
                  c.mv       s1, s10
                  lh         gp, -1560(s3)
                  c.addi     a4, -7
                  lb         s10, -1723(s3)
                  srli       s1, s11, 10
                  xor        s1, s8, s1
                  sltiu      s4, s3, 491
                  lw         t3, -470(s3)
                  lbu        t2, 1121(s3)
                  slli       a5, gp, 12
                  c.slli     t4, 24
                  c.addi     s9, 6
                  sltiu      t4, s9, 646
                  sb         s5, 579(s3)
                  lbu        s11, 1208(s3)
                  sb         s7, -296(s3)
                  sb         a5, 921(s3)
                  lbu        a2, -127(s3)
                  sb         zero, 543(s3)
                  c.addi     a2, -7
                  lui        a6, 289915
                  sb         s1, 977(s3)
                  lw         t1, 598(s3)
                  lb         s7, -968(s3)
                  lb         s1, 1407(s3)
                  mul        a7, t6, s11
                  sh         tp, 440(s3)
                  lbu        s11, -1945(s3)
                  auipc      a1, 99547
                  lb         s5, 241(s3)
                  c.addi     s1, 10
                  lui        a6, 1008720
                  c.addi     a6, 23
                  c.nop
                  slt        s4, gp, t0
                  lbu        s11, -107(s3)
                  lui        s9, 665050
                  sb         t1, 1053(s3)
                  sb         s7, 243(s3)
                  lh         a1, 128(s3) #end riscv_load_store_rand_instr_stream_9
                  auipc      a3, 275463
                  sub        s11, sp, t6
                  srai       gp, a6, 22
                  c.addi     a6, 15
                  c.lui      t1, 20
                  c.lui      s4, 26
                  c.addi     t1, 30
                  c.andi     a4, 17
                  c.lui      a1, 22
                  auipc      a0, 349323
                  auipc      s3, 754968
                  c.sub      a1, s1
                  lui        s3, 1585
                  lui        t2, 811924
                  c.lui      a7, 5
                  c.addi     s8, 8
                  c.addi     t2, -17
                  c.srai     a4, 29
                  c.xor      s0, s0
                  c.addi     s6, 22
                  c.srli     a0, 2
                  sltiu      a7, s2, -917
                  c.lui      a7, 26
                  c.addi     s8, 12
                  c.mv       a4, ra
                  lui        t2, 467925
                  c.addi     s9, -23
                  c.srai     a4, 16
                  auipc      zero, 553705
                  c.srli     a0, 9
                  sll        s2, s1, a7
                  c.addi     t1, 28
                  c.addi     s6, 2
                  lui        a7, 820104
                  slti       s7, ra, -212
                  c.andi     a1, -17
                  auipc      a7, 99103
                  auipc      s9, 567717
                  lui        a1, 760470
                  c.addi     a1, 9
                  auipc      s8, 603303
                  lui        t6, 781280
                  c.srai     s0, 22
                  lui        a7, 519407
                  auipc      t1, 100859
                  c.addi     a0, -2
                  lui        s6, 172029
                  c.addi     a2, -23
                  c.addi     s6, 22
                  c.addi     t2, 6
                  c.addi     a1, 14
                  auipc      t5, 706283
                  auipc      s5, 343012
                  c.slli     t5, 12
                  c.lui      s0, 24
                  auipc      s9, 950928
                  c.and      a4, a3
                  c.srli     s1, 19
                  lui        a2, 447292
                  auipc      t6, 28004
                  auipc      zero, 37888
                  auipc      t1, 566584
                  c.srai     a3, 15
                  c.addi     s4, 4
                  auipc      s10, 920842
                  xor        s6, t2, s0
                  c.srai     s0, 18
                  auipc      a4, 720670
                  c.srai     a0, 15
                  c.addi     s1, 13
                  c.nop
                  lui        s11, 65000
                  lui        s8, 446185
                  c.addi     a2, 15
                  c.or       a2, a1
                  mul        t4, s7, s4
                  auipc      s5, 988581
                  div        s0, a6, ra
                  srl        t1, zero, s8
                  lui        t4, 923755
                  c.addi     s11, -5
                  auipc      a3, 731520
                  fence.i
                  addi       gp, t5, 424
                  c.addi     s8, -15
                  c.slli     t5, 31
                  lui        a7, 679813
                  c.addi     s4, 15
                  c.srai     a2, 29
                  c.addi     t5, -15
                  c.slli     a5, 24
                  div        s9, s9, a7
                  c.addi     a2, 24
                  c.srai     a1, 22
                  auipc      s6, 783877
                  c.addi     t6, -12
                  c.srli     s1, 2
                  auipc      t1, 178850
                  bne        t2, s0, 4980f
                  c.addi     s11, 19
                  c.lui      gp, 7
                  lui        zero, 318426
                  c.addi     s6, 23
4980:             c.srli     a2, 3
                  auipc      zero, 122050
                  c.lui      t6, 5
                  c.bnez     s1, 4998f
                  c.srli     a5, 28
                  c.addi     t3, 14
                  or         a6, s5, t3
                  addi       a7, a2, -645
                  lui        t3, 624335
                  c.srli     a3, 20
                  lui        a7, 105917
                  bge        s10, tp, 4997f
                  fence
                  c.srai     s1, 6
                  c.lui      t2, 2
                  c.addi     t6, 26
                  lui        s1, 755816
4997:             lui        a3, 395594
4998:             lui        a3, 526044
                  srai       s8, s4, 4
                  c.sub      a3, a2
                  c.lui      s4, 24
                  sltiu      gp, s10, 442
                  la         s11, data_page_2+2354 #start riscv_load_store_rand_instr_stream_18
                  sb         t5, 1523(s11)
                  lui        s0, 542801
                  lbu        s6, -1360(s11)
                  c.addi     a0, -28
                  lui        a7, 453107
                  lb         a5, -1858(s11)
                  lb         s2, -1863(s11)
                  c.slli     a1, 2
                  sw         s3, 1410(s11)
                  sh         zero, -1290(s11)
                  c.addi     t2, 27
                  sb         a2, -1927(s11)
                  c.slli     s0, 1
                  lb         s5, 1691(s11)
                  sb         s4, 967(s11)
                  lui        s10, 251240
                  c.or       a4, s0
                  lbu        s1, 1045(s11)
                  c.addi     gp, 18
                  sh         a5, -152(s11)
                  c.li       t4, 6
                  c.lui      t6, 3
                  lb         a3, -489(s11)
                  lhu        s8, -568(s11)
                  sh         t0, -1480(s11)
                  lhu        s7, 220(s11)
                  sb         t4, 1553(s11)
                  lhu        s10, -1004(s11)
                  c.lui      a3, 19
                  lbu        t4, -1159(s11)
                  lb         a5, -745(s11)
                  sb         a7, -1277(s11)
                  c.slli     a7, 23
                  lh         s8, -782(s11)
                  lbu        s3, 263(s11)
                  lb         s1, 739(s11)
                  lbu        t4, -1347(s11)
                  sw         gp, 574(s11)
                  sw         zero, -242(s11)
                  lbu        s5, -1339(s11) #end riscv_load_store_rand_instr_stream_18
                  c.srai     a1, 12
                  mul        a2, a0, t2
                  nop
                  c.srli     a4, 19
                  mulhsu     a6, s11, s11
                  c.srai     a2, 15
                  c.addi     s7, -5
                  lui        s4, 598921
                  c.addi     s3, 1
                  c.lui      s6, 21
                  c.srli     a5, 17
                  c.addi     s5, -14
                  c.srli     s0, 15
                  c.addi     a7, -5
                  mulhsu     a4, s10, ra
                  lui        s9, 907628
                  lui        gp, 1042829
                  c.addi     a5, -9
                  lui        s5, 577314
                  lui        s5, 524637
                  lui        a6, 538829
                  c.lui      t6, 15
                  c.srli     a2, 3
                  c.slli     a2, 24
                  c.addi     a3, 12
                  auipc      t5, 269684
                  c.addi     t6, -27
                  c.addi     s3, -13
                  c.addi     a0, -26
                  mulhu      s3, a6, s7
                  c.slli     t3, 1
                  lui        s7, 702027
                  c.addi     t2, -7
                  c.srai     s0, 18
                  addi       s0, t3, -915
                  andi       a3, s0, 587
                  c.slli     a6, 15
                  srli       t1, s3, 17
                  auipc      a2, 227992
                  c.srai     a5, 19
                  c.addi     s10, -11
                  auipc      gp, 333151
                  sll        a4, s2, a4
                  c.addi     a3, -9
                  c.addi     a0, 19
                  lui        a7, 720979
                  auipc      s2, 529174
                  c.addi     s11, 11
                  c.addi     a4, 27
                  c.srli     s0, 25
                  c.lui      s9, 15
                  auipc      s4, 401120
                  c.srai     a1, 4
                  c.beqz     a3, 5071f
                  c.slli     t2, 11
                  la         gp, data_page_4+1814 #start riscv_load_store_rand_instr_stream_27
                  c.addi     s10, -12
                  sh         t4, -272(gp)
                  lb         a6, 1653(gp)
                  c.addi     s10, -24
                  c.addi     s0, 22
                  c.addi     s5, 11
                  ori        t6, s1, 1011
                  auipc      t6, 563090
                  lui        s1, 429013
                  sb         t4, -1163(gp)
                  c.addi     a1, 16
                  lui        s2, 668978
                  lbu        s10, -709(gp)
                  lb         s8, -522(gp)
                  c.srli     s1, 29
                  c.addi     s11, -8
                  lui        zero, 3671
                  c.srli     s0, 17
                  c.mv       s3, t0
                  sb         a2, -56(gp)
                  srai       t6, a0, 14
                  fence
                  sb         tp, -1531(gp)
                  mulhu      t1, a0, sp
                  remu       a7, s1, s1
                  lbu        t2, 798(gp)
                  auipc      t6, 229513
                  c.lui      t5, 11
                  lbu        s0, -1172(gp)
                  lb         a2, 1032(gp) #end riscv_load_store_rand_instr_stream_27
                  fence.i
                  c.srli     a5, 13
                  remu       gp, s9, s8
                  c.addi     gp, -23
                  lui        s10, 713972
                  c.addi     s1, -7
                  c.addi     s1, 2
                  c.srli     a3, 24
                  c.srli     a1, 1
                  c.srli     a1, 9
                  c.addi     s6, 22
                  or         s9, s10, gp
                  lui        t5, 754140
5071:             c.srli     a2, 20
                  sra        a2, t0, t0
                  lui        s11, 122626
                  c.addi     a4, 7
                  mul        t6, a0, t0
                  lui        t5, 798975
                  fence.i
                  c.addi     t5, -11
                  c.add      a3, s1
                  c.add      s0, a4
                  bltu       tp, t5, 5091f
                  lui        a1, 103973
                  srli       a6, s6, 5
                  auipc      t5, 813332
                  lui        a4, 155722
                  fence
                  auipc      t4, 326660
                  c.slli     s4, 18
                  addi       s7, s5, -973
                  auipc      s1, 1020772
5091:             slti       s0, s2, -326
                  bne        s2, a3, 5097f
                  c.slli     s3, 8
                  lui        s0, 1048015
                  c.addi     s0, -5
                  auipc      a6, 459818
5097:             mulh       s0, a1, a4
                  c.srai     s1, 25
                  auipc      gp, 306262
                  c.addi     s1, 10
                  auipc      s5, 478931
                  c.addi     t2, 25
                  c.addi     s4, -24
                  c.addi     s1, -20
                  c.addi     gp, 30
                  lui        s4, 365009
                  andi       a1, t2, -33
                  lui        a3, 318987
                  lui        t5, 620716
                  c.srli     a1, 27
                  c.addi     a1, 9
                  c.addi     a3, -32
                  lui        a0, 303348
                  c.slli     a7, 20
                  c.addi     a0, 10
                  auipc      s3, 137555
                  c.addi     s2, 19
                  auipc      a2, 709727
                  remu       a2, a3, t1
                  lui        s7, 484661
                  lui        a5, 883040
                  c.and      s0, a4
                  c.addi     a2, -1
                  fence.i
                  lui        s9, 920008
                  addi       s9, s2, 920
                  divu       s4, a6, a6
                  c.addi     s1, 16
                  lui        a0, 922162
                  c.addi     s0, -22
                  bltu       a6, a6, 5133f
                  c.srai     a5, 16
5133:             c.addi     a7, 4
                  srli       a0, a6, 11
                  c.addi     a2, -2
                  auipc      s7, 32546
                  c.lui      a7, 9
                  auipc      zero, 54333
                  c.beqz     s1, 5146f
                  c.addi     s11, -3
                  auipc      s5, 862873
                  c.lui      s3, 26
                  c.beqz     a4, 5158f
                  addi       s4, s3, -400
                  auipc      a3, 922009
5146:             bgeu       ra, a0, 5163f
                  lui        t3, 508266
                  c.addi     a7, -4
                  bltu       a1, s8, 5159f
                  c.srli     a5, 12
                  c.or       s1, a1
                  sub        a7, t1, t3
                  auipc      gp, 246838
                  mulhsu     t6, s6, s0
                  c.andi     a5, 24
                  c.addi     a2, -24
                  slli       a1, a3, 21
5158:             lui        a4, 851980
5159:             lui        t6, 728960
                  auipc      a2, 719883
                  rem        t1, ra, sp
                  sub        s10, t2, sp
5163:             srai       a4, s8, 26
                  lui        t1, 690351
                  c.addi     s9, -12
                  auipc      a3, 443749
                  c.addi     s2, -28
                  add        t4, a4, tp
                  c.addi     s2, 22
                  c.lui      s8, 12
                  c.addi     a5, -5
                  divu       zero, s1, gp
                  c.addi     a1, 3
                  c.addi     t4, 24
                  c.addi     a0, -28
                  auipc      a5, 730203
                  auipc      s9, 107987
                  c.addi     t2, 24
                  c.lui      a0, 15
                  beq        s3, s6, 5194f
                  c.lui      a1, 12
                  beq        t0, s9, 5202f
                  c.srli     a2, 4
                  lui        a1, 227759
                  c.lui      a5, 18
                  c.addi     a7, -23
                  c.lui      s2, 11
                  sltu       zero, t0, gp
                  c.lui      t6, 22
                  c.addi     a2, 10
                  c.slli     a6, 19
                  c.lui      s2, 23
                  slli       s7, t5, 10
5194:             addi       t4, s4, -143
                  c.addi     t1, -14
                  auipc      gp, 687633
                  lui        s6, 631959
                  srai       a6, s5, 26
                  c.addi     t2, -21
                  xor        t6, a1, a3
                  lui        a7, 968854
5202:             mulhu      s3, t0, a0
                  auipc      a7, 286318
                  srli       gp, s7, 30
                  srl        t6, s7, t1
                  xori       s4, a3, 332
                  sub        t1, s2, t0
                  c.addi     s10, -4
                  c.slli     s4, 24
                  divu       t5, a7, a2
                  auipc      t1, 90801
                  c.li       a5, 20
                  c.xor      a4, a3
                  auipc      s10, 358164
                  c.lui      s1, 1
                  c.xor      a5, a2
                  c.addi     t4, 7
                  c.srli     s1, 6
                  auipc      t1, 467726
                  c.mv       a5, t4
                  lui        a6, 403960
                  auipc      s11, 1021220
                  c.addi     gp, -17
                  c.srai     a1, 15
                  bltu       s0, a7, 5232f
                  bne        s4, s1, 5237f
                  c.slli     s6, 18
                  c.addi     s1, -17
                  c.addi     s3, 3
                  auipc      zero, 455709
                  lui        a1, 354633
5232:             c.addi     s6, 29
                  auipc      s11, 570461
                  lui        a7, 664342
                  c.addi     s7, 29
                  mul        s5, gp, a0
5237:             c.addi     s1, -23
                  xor        a0, s7, tp
                  c.srai     s1, 27
                  c.lui      a3, 1
                  lui        t5, 132062
                  c.addi     a3, 27
                  c.addi     t6, -28
                  c.srai     a3, 4
                  c.slli     s11, 25
                  c.addi     t1, 28
                  rem        a4, zero, gp
                  c.slli     s2, 2
                  c.andi     a3, 28
                  c.addi     s10, -25
                  c.addi     s7, 11
                  c.lui      t3, 10
                  div        s2, s0, a3
                  lui        s3, 591615
                  c.srli     a4, 17
                  lui        a0, 712408
                  c.addi     s10, -8
                  lui        s9, 234500
                  c.addi     s0, 29
                  c.slli     t3, 22
                  c.addi     a4, -16
                  c.and      a3, a3
                  c.addi     t5, -14
                  auipc      t3, 231942
                  c.lui      a6, 3
                  slti       a7, s1, 865
                  c.addi     s6, -20
                  rem        a1, a3, a2
                  la         a7, data_page_9+2263 #start riscv_load_store_rand_instr_stream_65
                  sb         s7, -1524(a7)
                  lw         zero, -567(a7)
                  auipc      s5, 713840
                  c.addi     t5, -16
                  sb         a4, -8(a7)
                  c.srai     s1, 12
                  c.srli     a5, 2
                  lbu        s11, -466(a7)
                  c.addi     s10, 24
                  lb         a2, -2002(a7)
                  auipc      a0, 320817
                  sw         t4, -1935(a7)
                  c.slli     a4, 13
                  sb         t0, 1800(a7)
                  lbu        s0, 3(a7)
                  lb         s3, 320(a7)
                  lb         t3, -766(a7)
                  lh         t1, 1765(a7)
                  auipc      t4, 117758
                  lbu        t6, -1730(a7)
                  lb         s4, -1284(a7)
                  lbu        t5, 927(a7)
                  lui        t2, 834018
                  lhu        s9, -467(a7)
                  lbu        s11, 738(a7)
                  lw         s10, -247(a7)
                  lb         t3, -593(a7)
                  sb         zero, 1437(a7)
                  c.addi     s9, 28
                  lbu        t1, -178(a7)
                  auipc      s3, 38290
                  sb         a5, 1176(a7)
                  lbu        gp, 1472(a7)
                  sh         ra, -897(a7)
                  addi       s1, t1, 853
                  sb         t6, 170(a7)
                  c.addi     s10, 16
                  lb         t2, 1542(a7)
                  lhu        gp, 1779(a7)
                  sh         s4, 561(a7)
                  lh         t3, 781(a7)
                  lb         t3, 1679(a7) #end riscv_load_store_rand_instr_stream_65
                  auipc      a2, 497299
                  srai       t1, s0, 26
                  c.slli     s7, 18
                  sub        a0, t0, t5
                  c.srli     s0, 2
                  sra        a1, zero, s8
                  slti       a1, s3, 196
                  auipc      a5, 270955
                  mulh       a0, t3, a4
                  auipc      a0, 376150
                  c.addi     s7, -24
                  c.srli     a3, 18
                  c.lui      t1, 14
                  auipc      s5, 876885
                  c.srli     a5, 23
                  c.srli     a1, 17
                  auipc      s7, 412135
                  c.slli     a1, 9
                  auipc      s6, 5210
                  c.addi     s5, -18
                  auipc      a0, 257487
                  auipc      t5, 653900
                  c.addi     s5, -30
                  c.lui      s2, 25
                  c.srai     s0, 12
                  c.srai     s1, 2
                  lui        s3, 736367
                  c.addi     s8, 2
                  c.srli     a0, 27
                  c.srai     a4, 8
                  and        s7, ra, gp
                  add        a1, s5, s9
                  c.srai     a4, 1
                  c.addi     s10, 7
                  or         t2, s5, t0
                  c.slli     s6, 29
                  c.addi     t5, -18
                  fence.i
                  c.srai     a1, 4
                  c.srli     a3, 19
                  c.srli     a5, 26
                  c.and      a0, s0
                  auipc      t3, 152265
                  c.addi     t2, -31
                  c.addi     a1, 25
                  auipc      t2, 624278
                  c.slli     s5, 28
                  c.slli     a6, 28
                  beq        sp, s0, 5333f
                  auipc      s0, 819747
                  slt        a4, sp, a6
                  sub        s2, s7, a7
                  c.sub      s0, s0
                  lui        s10, 104624
                  la         s11, data_page_8+1167 #start riscv_load_store_rand_instr_stream_29
                  sb         s5, 46(s11)
                  lb         s10, 428(s11)
                  c.lui      s1, 9
                  lb         s9, 999(s11)
                  lb         s7, 683(s11)
                  lbu        t5, 992(s11)
                  lbu        zero, 260(s11)
                  sh         a7, -1089(s11)
                  srai       a3, t3, 0
                  sb         ra, 27(s11)
                  auipc      a3, 703150
                  sb         s9, 367(s11)
                  lh         a4, 1849(s11)
                  sb         s10, 1700(s11)
                  lb         s9, 362(s11)
                  c.srai     a0, 26
                  sb         a7, 1796(s11)
                  c.andi     a0, -19
                  c.srli     s0, 31
                  rem        s4, t5, a7
                  lui        gp, 786240
                  lhu        t2, 1369(s11)
                  lw         s0, 385(s11)
                  lui        s4, 945939
                  sb         s11, 913(s11)
                  lui        s8, 853793
                  lbu        a7, 1358(s11)
                  lbu        a5, -406(s11) #end riscv_load_store_rand_instr_stream_29
                  lui        gp, 112295
                  c.mv       s6, t3
                  c.srli     a0, 30
                  c.slli     a3, 15
                  c.addi     t3, 26
                  c.slli     s2, 27
                  c.addi     s3, -21
                  c.addi     s5, 6
                  c.addi     s0, -16
                  c.bnez     a0, 5339f
5333:             auipc      a1, 131317
                  c.slli     a3, 12
                  c.xor      a4, a0
                  auipc      s11, 17861
                  sub        s0, a1, a2
                  c.slli     gp, 14
5339:             lui        zero, 307184
                  c.add      a1, a3
                  c.srai     s1, 9
                  auipc      t6, 754568
                  and        a3, t3, s0
                  c.lui      a2, 19
                  c.or       a2, a2
                  c.addi     s11, 5
                  lui        s5, 454852
                  auipc      zero, 1007352
                  c.srai     a5, 26
                  auipc      a3, 439487
                  auipc      s8, 469339
                  andi       zero, s2, -902
                  c.lui      a2, 29
                  c.lui      t5, 27
                  auipc      s9, 145447
                  c.sub      s0, s1
                  c.xor      a2, a4
                  c.addi     t1, -9
                  sltu       t6, tp, s3
                  c.addi     a0, -19
                  lui        t1, 1037414
                  c.mv       s4, t6
                  c.lui      gp, 28
                  lui        t3, 968328
                  nop
                  c.sub      a3, a1
                  addi       t1, s2, 517
                  c.addi     gp, -18
                  c.srli     a5, 11
                  auipc      s4, 254654
                  c.lui      s0, 28
                  auipc      t4, 777825
                  c.slli     a0, 25
                  c.addi     s9, -4
                  mulhsu     a4, s6, s9
                  auipc      a4, 1025193
                  c.addi     t5, -1
                  c.slli     a2, 29
                  sltiu      t6, a2, -304
                  slli       zero, t0, 27
                  c.addi     s2, 16
                  lui        t1, 1032707
                  c.lui      s10, 25
                  c.xor      s1, s0
                  c.addi     t3, -28
                  c.addi     a7, -20
                  c.beqz     a4, 5390f
                  auipc      a7, 567191
                  lui        t1, 990121
5390:             or         s6, tp, t5
                  c.addi     s0, 10
                  c.addi     a0, -20
                  c.mv       gp, tp
                  auipc      s3, 219421
                  c.or       a5, a2
                  c.addi     s1, 4
                  bgeu       t3, s4, 5408f
                  c.lui      t4, 9
                  c.addi     a4, 20
                  c.addi     a4, -30
                  lui        t2, 194675
                  c.srai     a2, 13
                  auipc      a2, 1036905
                  c.li       s4, 9
                  c.lui      a4, 14
                  sub        a2, s8, s2
                  lui        s8, 876613
5408:             mulhsu     s5, s3, tp
                  c.srai     a5, 7
                  c.addi     s6, -2
                  slli       t1, gp, 27
                  srai       s0, a4, 1
                  lui        s6, 715539
                  la         a3, data_page_19+1288 #start riscv_load_store_rand_instr_stream_32
                  mul        a4, a4, t5
                  c.addi     a0, -29
                  lbu        a0, -519(a3)
                  sb         s2, -530(a3)
                  c.srai     a1, 30
                  c.srai     a0, 25
                  c.addi     s10, 30
                  lui        a7, 955161
                  sb         a1, 799(a3)
                  c.addi     s9, 13
                  auipc      t3, 174229
                  sw         tp, 1712(a3)
                  lhu        a0, 726(a3)
                  slli       a2, t3, 15
                  auipc      s4, 55303
                  sh         t1, 1330(a3)
                  add        t6, s8, sp
                  c.addi     s1, -8
                  auipc      a4, 786770
                  ori        a2, sp, -961
                  lui        zero, 806788
                  c.addi     a5, -26
                  lb         t4, 441(a3)
                  c.addi     t6, -20
                  auipc      t3, 26776
                  c.slli     s0, 31
                  sb         s1, -104(a3)
                  lui        a6, 1011858
                  sb         sp, -1043(a3)
                  c.addi     s7, 18
                  lui        t1, 600904
                  lui        s10, 506360
                  sltu       s0, a2, a6
                  sb         a1, 347(a3)
                  c.li       s1, 5
                  divu       zero, t6, t4
                  lui        s10, 944380
                  c.slli     a1, 15
                  slli       s11, zero, 30
                  lbu        s4, -1125(a3) #end riscv_load_store_rand_instr_stream_32
                  lui        a6, 506859
                  c.srai     a4, 31
                  lui        s0, 867586
                  c.addi     a3, -28
                  c.and      a3, a1
                  c.or       a4, a3
                  c.srai     a2, 21
                  c.addi     gp, -25
                  auipc      s0, 1007907
                  c.slli     t1, 1
                  c.lui      a6, 16
                  lui        s6, 418377
                  c.srli     s0, 19
                  c.bnez     s1, 5439f
                  c.addi     a2, 27
                  c.addi     t2, -3
                  auipc      s5, 152600
                  c.lui      s4, 23
                  sll        a3, a0, s10
                  mulh       s11, s8, a6
                  c.addi     s2, -16
                  lui        s3, 634438
                  c.srai     a2, 25
                  slt        t5, t1, gp
                  rem        s10, s4, zero
5439:             c.lui      a4, 26
                  xor        t4, t6, a0
                  c.srai     a1, 31
                  lui        t1, 1041849
                  div        t2, s6, a0
                  c.addi     t4, -25
                  auipc      t3, 489540
                  c.lui      t4, 3
                  c.srai     s1, 4
                  c.lui      s9, 3
                  c.lui      s8, 13
                  auipc      a6, 498061
                  c.and      a0, a0
                  mulh       s0, t0, a4
                  slli       a2, s1, 3
                  c.addi     s0, 29
                  c.addi     s0, -11
                  c.and      a1, a1
                  mul        s6, s9, a0
                  c.addi     a2, 25
                  c.addi     s3, 7
                  auipc      s3, 1002815
                  c.bnez     s1, 5476f
                  auipc      s4, 318027
                  c.srli     a3, 5
                  c.slli     t2, 23
                  auipc      s10, 563174
                  sra        t1, a3, s11
                  sub        a2, t1, a0
                  c.srli     a0, 2
                  auipc      s9, 798693
                  c.lui      s10, 13
                  c.slli     a3, 4
                  auipc      s11, 408224
                  la         t6, data_page_18+1282 #start riscv_load_store_rand_instr_stream_17
                  lb         gp, -362(t6)
                  sra        s7, t2, s9
                  c.addi     t3, -31
                  auipc      s10, 62509
                  c.addi     a2, -20
                  sb         a6, -671(t6)
                  slli       t3, t6, 5
                  lw         s2, 2018(t6)
                  lbu        s8, 554(t6)
                  c.slli     s7, 27
                  mulh       s6, tp, gp
                  lhu        t3, 460(t6)
                  c.addi     a4, -7
                  c.addi     s4, 19
                  lui        s4, 1041916
                  lbu        a4, -1081(t6)
                  sb         t5, -777(t6)
                  sb         t5, 1928(t6)
                  c.lui      s7, 28
                  c.lui      s1, 19
                  c.or       a4, a1
                  lb         s8, -1121(t6)
                  lbu        s10, -147(t6)
                  lhu        s9, 630(t6)
                  c.lui      s2, 10
                  lb         a5, 1901(t6)
                  lbu        a4, 557(t6)
                  lhu        s3, -776(t6)
                  auipc      a2, 390098
                  sb         sp, -789(t6) #end riscv_load_store_rand_instr_stream_17
                  c.srai     a3, 6
                  c.addi     gp, -2
                  c.addi     s10, 21
5476:             auipc      a7, 777473
                  auipc      t6, 956047
                  ori        s9, a1, 1004
                  c.addi     s8, 20
                  c.srli     s1, 2
                  c.addi     t5, -15
                  c.lui      t4, 24
                  mul        s11, sp, a7
                  srl        a4, zero, t2
                  c.addi     s8, 5
                  sub        s3, s4, t3
                  nop
                  auipc      s4, 314242
                  c.addi     s2, 19
                  andi       t5, s5, -934
                  sltiu      s9, t1, 251
                  divu       s10, s8, t1
                  c.or       a0, s0
                  c.lui      s10, 7
                  c.addi     s9, -14
                  c.srli     s0, 1
                  c.srai     a3, 15
                  auipc      s5, 243733
                  auipc      s8, 258131
                  c.addi     s11, 26
                  c.slli     t1, 28
                  lui        t5, 802054
                  auipc      zero, 29498
                  c.srli     a4, 21
                  c.addi     gp, -7
                  lui        t3, 389699
                  sltu       t2, a1, t0
                  c.or       a5, a0
                  c.slli     s10, 15
                  bgeu       s1, t2, 5515f
                  c.addi     a0, 26
                  c.or       a3, a2
                  c.addi     t4, 10
                  c.addi     t6, 20
5515:             c.slli     s9, 17
                  auipc      a1, 573006
                  lui        s0, 949563
                  lui        s0, 59504
                  c.srli     s0, 21
                  c.slli     s4, 1
                  c.srli     a5, 10
                  xori       s7, a6, 887
                  sub        s3, a5, sp
                  c.addi     a1, -22
                  c.lui      a6, 25
                  c.addi     s10, -18
                  c.lui      a2, 2
                  c.srai     s1, 14
                  slti       t2, t0, 693
                  auipc      t5, 107648
                  c.srli     a4, 3
                  c.addi     s4, -2
                  remu       s4, t1, a7
                  c.srai     s0, 10
                  c.lui      s1, 3
                  c.addi     gp, 6
                  c.slli     t6, 13
                  and        a6, a0, t0
                  c.addi     s10, 31
                  c.srli     s1, 12
                  c.addi     gp, -17
                  c.addi     s7, -30
                  lui        a4, 120062
                  c.addi     t6, -3
                  lui        s4, 959950
                  c.slli     a5, 15
                  c.addi     t1, 19
                  and        s6, t4, a4
                  la         a6, data_page_12+2330 #start riscv_load_store_rand_instr_stream_15
                  lbu        a2, 1247(a6)
                  c.addi     a5, -31
                  lhu        s5, -288(a6)
                  lbu        s3, 771(a6)
                  sb         s3, 1407(a6)
                  sh         s9, -1304(a6)
                  fence.i
                  lbu        t6, 245(a6)
                  lh         t6, -204(a6)
                  lbu        s4, -78(a6)
                  c.or       a0, a3
                  c.srli     a5, 17
                  auipc      s5, 568869
                  lbu        t1, -171(a6)
                  lui        a5, 822434
                  auipc      a0, 674677
                  auipc      s0, 959320
                  c.lui      t3, 15
                  mul        gp, s2, a4
                  sb         a6, 1560(a6)
                  lhu        t4, -1178(a6)
                  sb         s11, 351(a6)
                  c.addi     a2, 3
                  auipc      t4, 822590
                  c.addi     t2, -16
                  slli       s10, a2, 12
                  lbu        t5, 744(a6)
                  or         a3, s6, a5
                  lb         a3, -599(a6)
                  lb         s5, 1313(a6)
                  divu       s8, s11, s0
                  lbu        t5, -1582(a6)
                  lui        s6, 337557
                  div        s5, sp, t4
                  sb         s3, 1721(a6)
                  auipc      a5, 871182
                  lb         a4, 7(a6)
                  lbu        t5, 1056(a6)
                  lb         s0, 715(a6)
                  divu       s0, s2, ra
                  lui        a4, 848897
                  lui        a3, 45377
                  sb         t2, -1659(a6)
                  c.lui      t6, 16
                  c.srai     a3, 5
                  c.lui      s3, 28
                  c.addi     a0, 8
                  lb         a0, 1572(a6)
                  sb         s9, 344(a6)
                  remu       a1, t6, s11
                  auipc      s2, 730598
                  nop
                  lhu        t3, -316(a6)
                  sb         s5, -225(a6)
                  sb         s7, -1336(a6)
                  sb         t1, 1289(a6) #end riscv_load_store_rand_instr_stream_15
                  c.addi     s4, 10
                  c.addi     a1, -19
                  c.addi     s9, -1
                  c.lui      t1, 18
                  la         s0, sub_2
                  c.addi     a5, 15
                  c.addi     a4, 8
                  addi       s0, s0, -526
                  c.addi     t1, -23
                  c.srli     a2, 6
                  blt        s7, t5, j__main_sub_2_3 #branch to jump instr
                  c.addi     a3, -31
                  c.slli     s7, 4
                  c.slli     a1, 8
                  c.addi     s11, -11
j__main_sub_2_3:  jalr       ra, s0, 526
                  xor        t4, a0, s6
                  c.addi     s8, 26
                  c.srli     a1, 15
                  auipc      a3, 258425
                  c.addi     s6, 14
                  c.xor      a3, a4
                  c.srli     a0, 1
                  c.addi     a6, -6
                  c.addi     t4, -9
                  c.addi     s1, 16
                  xor        s11, t5, s11
                  c.lui      s6, 18
                  auipc      a5, 66964
                  c.sub      a2, a0
                  slti       s2, sp, -653
                  auipc      s7, 931678
                  mulh       a2, s5, sp
                  beq        gp, t0, 5585f
                  c.addi     s10, -16
                  c.addi     s10, 24
                  auipc      t5, 942350
                  c.lui      s7, 4
                  lui        t4, 787529
                  c.slli     s11, 27
                  lui        s11, 707275
                  c.addi     a5, -17
                  c.lui      s1, 28
                  c.addi     a0, -19
                  c.srli     a0, 5
                  c.addi     a3, -29
                  c.addi     a5, -29
                  c.addi     a3, -22
5585:             c.slli     s10, 17
                  c.addi     a1, 19
                  c.srli     s0, 16
                  remu       s9, tp, s6
                  bge        a2, zero, 5603f
                  auipc      s4, 211037
                  c.addi     a2, 23
                  c.addi     s9, 14
                  mul        s6, s7, t3
                  c.slli     a3, 29
                  beq        s9, s5, 5598f
                  c.srai     a3, 20
                  auipc      a6, 919133
5598:             c.addi     s7, 6
                  auipc      t5, 963808
                  c.addi     s0, 19
                  nop
                  slti       s3, a0, 181
5603:             remu       s3, t5, t0
                  c.srai     s1, 15
                  sltu       t1, t3, t0
                  sltu       t5, ra, s2
                  or         t1, s4, a6
                  c.addi     t4, 2
                  auipc      t5, 445082
                  c.srai     a2, 11
                  lui        s2, 426795
                  srl        s11, a5, t3
                  c.addi     a2, -11
                  c.xor      a3, s1
                  c.addi     a4, 8
                  c.addi     s0, 16
                  slti       s8, t2, -903
                  c.srli     s0, 16
                  la         s8, data_page_17+1572 #start riscv_load_store_rand_instr_stream_24
                  sb         s9, 362(s8)
                  c.li       s10, -27
                  lbu        s9, 1793(s8)
                  or         a1, s8, s7
                  sb         t4, -43(s8)
                  c.li       t2, 4
                  c.addi     s5, 31
                  xor        s7, s11, sp
                  auipc      t4, 669301
                  auipc      s4, 679465
                  slli       a5, a6, 23
                  c.addi     a2, 24
                  ori        a5, zero, -511
                  remu       t5, a3, a1
                  sh         a6, -960(s8)
                  auipc      s9, 10545
                  sb         s10, 1231(s8)
                  auipc      s4, 211043
                  lbu        a5, 829(s8)
                  sb         a0, -1478(s8)
                  auipc      a2, 786337
                  sb         a0, -67(s8)
                  lb         a2, -1505(s8)
                  c.srai     s0, 2
                  mulh       t1, s2, s5
                  c.lui      a7, 3
                  c.srli     a3, 19
                  lh         s1, 1214(s8)
                  auipc      a3, 358009
                  nop
                  divu       t4, s3, s7
                  sb         a4, 961(s8)
                  auipc      s3, 344860
                  c.addi     t5, 20
                  lbu        a6, 347(s8) #end riscv_load_store_rand_instr_stream_24
                  sra        a1, t1, s0
                  c.lui      s11, 30
                  c.lui      s0, 28
                  lui        t1, 730833
                  c.lui      s8, 8
                  lui        s11, 66787
                  auipc      gp, 170666
                  auipc      t1, 840659
                  c.srai     a5, 7
                  c.li       s3, 13
                  lui        t4, 671924
                  c.lui      t6, 19
                  lui        a3, 614894
                  auipc      t6, 928607
                  lui        t2, 545579
                  c.addi     t3, 20
                  c.srli     a2, 29
                  c.slli     t5, 22
                  c.srai     a2, 23
                  c.addi     s1, 1
                  c.and      s0, a2
                  c.addi     t1, 30
                  auipc      s10, 350885
                  add        s9, a0, a4
                  c.lui      a1, 19
                  auipc      s1, 371749
                  auipc      a4, 674376
                  c.slli     t4, 31
                  c.slli     gp, 2
                  ori        a5, t6, 359
                  c.slli     t1, 1
                  c.addi     s7, 1
                  and        s0, sp, s0
                  c.addi     gp, 12
                  c.srai     a3, 17
                  auipc      t4, 588827
                  c.addi     a7, -8
                  c.addi     s8, -25
                  auipc      a4, 332898
                  auipc      a0, 145691
                  fence
                  auipc      s10, 434817
                  c.addi     a6, -32
                  c.addi     s1, 30
                  auipc      t6, 649745
                  c.xor      a3, s1
                  c.addi     t3, -30
                  c.srai     a5, 15
                  c.addi     s3, -5
                  c.lui      s2, 23
                  c.addi     t3, -13
                  c.lui      s6, 10
                  lui        a6, 337913
                  c.slli     s5, 8
                  auipc      s3, 120491
                  c.srli     s1, 20
                  auipc      a0, 246660
                  c.addi     t5, 11
                  auipc      s5, 279602
                  c.lui      a1, 20
                  c.slli     a1, 31
                  auipc      t3, 729718
                  c.addi     gp, 6
                  c.addi     t1, -15
                  c.sub      a4, a1
                  c.srli     a0, 10
                  c.addi     s7, -25
                  c.addi     t1, -18
                  c.srai     a1, 7
                  c.slli     s4, 28
                  andi       t5, a5, 106
                  lui        t6, 762178
                  bgeu       t3, s6, 5710f
                  c.srli     a5, 16
                  c.srli     a0, 4
                  c.lui      s9, 22
                  lui        s5, 311876
                  lui        s1, 84674
                  c.srli     s1, 10
                  andi       zero, a0, -427
                  auipc      s7, 269466
                  c.addi     t4, 31
                  nop
                  andi       t5, a5, 999
                  c.andi     a5, -18
                  c.addi     t1, -4
                  c.srli     a5, 3
                  c.addi     t4, -29
                  la         a1, data_page_11+2074 #start riscv_load_store_rand_instr_stream_59
                  lb         s10, -1322(a1)
                  lui        s9, 767422
                  c.srai     a3, 27
                  and        s1, s11, a1
                  c.srli     a5, 6
                  lb         t6, -1227(a1)
                  lhu        t2, -1480(a1)
                  sb         a5, 877(a1)
                  fence
                  lui        s5, 80513
                  lbu        t2, -41(a1)
                  rem        t2, t1, s3
                  auipc      a7, 239104
                  c.addi     a5, -3
                  auipc      s8, 167409
                  sb         s9, 1892(a1)
                  auipc      s4, 114386
                  auipc      s8, 764381
                  lh         a7, 400(a1)
                  c.lui      a2, 4
                  lb         s0, 1501(a1)
                  sb         s4, 1458(a1)
                  auipc      s5, 724406
                  lhu        t5, -1526(a1)
                  c.srli     a3, 11
                  lhu        a5, -1064(a1)
                  c.addi     t4, 15
                  sub        a3, a1, s3
                  auipc      t5, 779984
                  xor        s5, a4, s9
                  lb         a5, 945(a1)
                  lbu        zero, 1607(a1)
                  c.addi     s0, 17
                  sltu       t3, t0, s5
                  lb         a7, -1097(a1)
                  lbu        s0, 1493(a1)
                  c.addi     a6, 3
                  auipc      a6, 650770
                  lui        s0, 227171
                  c.addi     s4, -1
                  sb         a0, -1085(a1) #end riscv_load_store_rand_instr_stream_59
                  c.lui      a1, 29
                  c.srai     a0, 25
                  c.and      a0, a4
5710:             c.addi     a1, 16
                  auipc      s3, 1013246
                  auipc      s10, 952274
                  auipc      t1, 840655
                  c.srai     s0, 6
                  auipc      a2, 43269
                  auipc      s4, 990482
                  c.addi     a7, -14
                  c.slli     s8, 7
                  c.addi     a4, -2
                  divu       t1, s5, s8
                  lui        a4, 167303
                  mul        t6, s10, t2
                  c.srai     a2, 18
                  c.addi     t4, -7
                  lui        t3, 671375
                  fence
                  auipc      s11, 809159
                  lui        s3, 31936
                  c.srai     a0, 23
                  c.addi     a6, -8
                  c.addi     s1, -21
                  mulhsu     t5, s0, ra
                  c.srli     s1, 23
                  c.addi     s5, 24
                  c.addi     gp, -21
                  c.srli     s0, 30
                  c.slli     s3, 23
                  c.slli     a1, 18
                  c.addi     s10, 25
                  slli       t4, s2, 9
                  c.srai     a4, 25
                  slt        s8, t5, a6
                  nop
                  or         s9, s8, t3
                  lui        s1, 661577
                  c.addi     t3, 17
                  beq        a1, zero, 5756f
                  auipc      s5, 217787
                  lui        a0, 367270
                  sub        s10, s7, s10
                  lui        s4, 1000211
                  c.addi     s0, 30
                  lui        s0, 183158
                  la         s3, data_page_9+2026 #start riscv_load_store_rand_instr_stream_40
                  lbu        s8, 1346(s3)
                  c.addi     s5, -28
                  sb         a1, -1620(s3)
                  c.srai     s1, 10
                  c.addi     s7, -29
                  fence
                  fence
                  lbu        t2, -264(s3)
                  lhu        a7, -1098(s3)
                  lb         a1, 1547(s3)
                  lb         t3, 449(s3)
                  auipc      t5, 662946
                  sb         s1, 1195(s3)
                  sb         a3, 289(s3)
                  c.srli     a3, 18
                  lbu        s4, -1757(s3)
                  auipc      t1, 840751
                  auipc      t4, 389335
                  lbu        t1, -1439(s3)
                  auipc      t4, 187582
                  auipc      t1, 553096
                  div        gp, a3, s11
                  c.mv       t4, s10
                  sb         a2, -783(s3)
                  c.slli     s11, 23
                  c.lui      s4, 29
                  c.sub      s0, a1
                  lhu        a1, 758(s3)
                  xori       gp, s5, -191
                  lh         s11, -1756(s3)
                  sb         s9, -611(s3)
                  sh         a1, -742(s3) #end riscv_load_store_rand_instr_stream_40
                  lui        a1, 362042
                  c.addi     t3, 19
5756:             c.and      s1, a0
                  c.addi     a4, 30
                  c.srai     s1, 18
                  auipc      s9, 965541
                  c.srai     a0, 28
                  fence.i
                  c.addi     t5, -11
                  andi       t2, t2, 579
                  add        s11, a3, s4
                  lui        s4, 330188
                  c.bnez     s0, 5779f
                  auipc      s1, 800655
                  or         gp, a3, a5
                  c.addi     gp, 7
                  slti       a6, s1, 302
                  c.addi     a4, -20
                  c.srli     a0, 16
                  c.addi     a4, -3
                  bltu       gp, a2, 5794f
                  div        s7, s2, t4
                  bge        t6, s10, 5783f
                  c.slli     a5, 12
                  c.addi     a3, -30
5779:             sra        s9, s6, a3
                  c.addi     s11, 2
                  sltu       t2, s4, s3
                  auipc      s3, 477866
5783:             c.slli     t4, 22
                  c.addi     a6, 21
                  c.beqz     a2, 5791f
                  c.addi     s9, 8
                  xori       a0, t5, 101
                  c.addi     a5, -2
                  auipc      s9, 425454
                  lui        s8, 643372
5791:             c.srli     s0, 28
                  c.addi     t6, -26
                  c.addi     s5, -10
5794:             c.lui      s11, 5
                  or         a5, s7, s11
                  c.srli     a3, 7
                  lui        s4, 25390
                  c.addi     a3, -22
                  la         t1, data_page_2+1854 #start riscv_load_store_rand_instr_stream_26
                  c.slli     t2, 31
                  sb         a1, 946(t1)
                  c.slli     s0, 24
                  c.addi     t3, -12
                  c.addi     s2, 4
                  c.srli     a5, 12
                  lbu        s8, 750(t1)
                  c.addi     s6, 5
                  sb         a3, -1297(t1)
                  add        t6, t3, s5
                  lbu        s2, -263(t1)
                  lh         zero, 812(t1)
                  sub        t3, zero, gp
                  lui        a1, 409392
                  lb         a7, -517(t1)
                  sb         s10, 1323(t1)
                  c.addi     t3, 5
                  lbu        s2, 529(t1)
                  sb         s2, -243(t1)
                  lb         a1, 1665(t1)
                  add        a7, a2, zero
                  lui        a5, 167586
                  fence
                  lb         s9, 1329(t1)
                  lbu        a0, -1059(t1)
                  sb         t0, 233(t1)
                  lhu        a7, -1230(t1)
                  c.lui      a6, 23
                  sb         t5, 132(t1)
                  c.addi     s7, 19
                  c.addi     s5, -16
                  lbu        t4, 533(t1)
                  c.addi     s8, 13
                  lui        zero, 561182
                  mulhsu     s1, a3, tp
                  lbu        a7, -1107(t1)
                  lbu        s4, 1908(t1)
                  lb         s4, -5(t1)
                  lbu        s0, 2029(t1)
                  c.srli     s0, 31
                  sb         a3, 645(t1)
                  c.li       a2, -22
                  c.lui      gp, 7
                  lb         s5, -87(t1)
                  lbu        t3, -1568(t1)
                  sh         s1, -552(t1)
                  sb         s8, -1473(t1)
                  lh         s9, -360(t1)
                  ori        t5, a3, -293
                  lb         t4, 1336(t1) #end riscv_load_store_rand_instr_stream_26
                  c.addi     s10, -5
                  auipc      a0, 810265
                  c.slli     a5, 16
                  c.li       s7, 1
                  c.bnez     a4, 5805f
                  c.addi     s7, 26
5805:             lui        a0, 939771
                  c.addi     t6, 31
                  auipc      t3, 406221
                  lui        a5, 177812
                  lui        s8, 981863
                  c.addi     gp, -13
                  auipc      t4, 452180
                  c.andi     a2, -28
                  c.add      a5, a0
                  c.addi     s2, 3
                  c.lui      t2, 25
                  c.addi     s0, -18
                  c.srai     a5, 14
                  lui        s2, 812202
                  lui        s8, 483486
                  auipc      a1, 419804
                  c.addi     s5, 9
                  la         a0, data_page_18+1989 #start riscv_load_store_rand_instr_stream_21
                  c.slli     s10, 14
                  mul        a4, t6, t0
                  lui        gp, 76207
                  lbu        a6, -1715(a0)
                  srl        a3, t0, t3
                  c.addi     s0, 20
                  lb         a6, -850(a0)
                  lb         a1, -1760(a0)
                  lb         s3, -309(a0)
                  sb         t3, -1946(a0)
                  lhu        a5, 1557(a0)
                  c.slli     a4, 14
                  auipc      s8, 920092
                  lh         a7, 311(a0)
                  c.addi     t5, 8
                  lbu        t6, 1200(a0)
                  lh         a4, 869(a0)
                  auipc      s10, 122501
                  lb         s8, 196(a0)
                  lui        s9, 721785
                  c.addi     t1, 13
                  mulhu      s0, t6, a4
                  sb         t1, -1071(a0)
                  c.addi     s9, 28
                  lui        s1, 982955
                  fence
                  lh         a3, 697(a0)
                  xori       s4, s4, -340
                  lb         s9, 1850(a0)
                  auipc      s6, 709197
                  c.addi     s10, -17
                  c.srai     s1, 27
                  sb         a7, -302(a0)
                  c.addi     gp, 4
                  lb         s3, 826(a0)
                  c.srli     a3, 20
                  c.lui      a2, 4
                  lh         a5, 597(a0)
                  c.addi     t6, 16
                  sb         a0, 1911(a0)
                  lbu        s9, -1987(a0)
                  c.addi     t5, -7
                  lh         s11, 25(a0)
                  srli       gp, a4, 29
                  lui        a1, 870066
                  sb         a6, -420(a0)
                  auipc      a7, 756681
                  lb         s10, 244(a0)
                  sb         a0, 457(a0)
                  lbu        s3, -1612(a0)
                  lbu        a3, 961(a0) #end riscv_load_store_rand_instr_stream_21
                  beq        ra, tp, 5841f
                  auipc      t4, 471453
                  c.srli     s0, 11
                  sra        s11, a7, gp
                  c.lui      s2, 26
                  lui        s8, 497376
                  c.addi     t4, -20
                  c.slli     a7, 2
                  c.slli     a3, 12
                  c.slli     t1, 8
                  lui        a0, 814999
                  c.srai     a0, 10
                  slt        zero, s5, a4
                  c.addi     t4, -9
                  lui        s9, 212593
                  c.srai     a2, 31
                  slt        gp, t0, s8
                  blt        a3, t2, 5841f
                  lui        t1, 261873
5841:             c.srli     a4, 4
                  c.lui      s8, 11
                  c.addi     s11, -4
                  lui        a4, 702999
                  lui        s3, 191860
                  lui        a2, 826480
                  auipc      s4, 915644
                  auipc      s3, 549994
                  auipc      s5, 458374
                  c.addi     s4, -30
                  c.slli     t3, 23
                  lui        s9, 647471
                  auipc      a5, 650168
                  c.srli     s1, 13
                  c.addi     t5, 21
                  auipc      a3, 561378
                  c.addi     s6, -7
                  c.sub      a5, s1
                  mulh       a3, a2, ra
                  lui        s3, 309145
                  auipc      s9, 480706
                  sub        s9, a2, s6
                  c.addi     a5, -17
                  c.addi     s2, 24
                  auipc      s10, 612945
                  slti       a0, a4, -872
                  c.addi     a6, 7
                  c.srai     a1, 23
                  c.addi     a1, -5
                  c.addi     s6, 17
                  auipc      a4, 330597
                  auipc      t4, 74354
                  lui        s7, 584591
                  c.srai     s1, 23
                  c.srai     a5, 26
                  c.lui      a7, 16
                  auipc      s1, 1022375
                  auipc      t1, 391773
                  lui        t4, 342087
                  lui        zero, 57046
                  c.srli     a2, 26
                  c.addi     s7, 10
                  la         s8, data_page_3+1834 #start riscv_load_store_rand_instr_stream_5
                  lh         t5, -412(s8)
                  sb         t1, 1052(s8)
                  c.addi     s1, 10
                  sh         s11, 1594(s8)
                  lb         a3, 1682(s8)
                  remu       s11, t3, s0
                  c.lui      s0, 25
                  lhu        s6, -1712(s8)
                  lbu        s11, 896(s8)
                  lh         a2, -676(s8)
                  c.slli     a7, 4
                  c.srai     a4, 24
                  sb         a6, 1697(s8)
                  auipc      a3, 620417
                  lhu        s6, -742(s8)
                  lbu        a1, 1607(s8)
                  c.addi     a6, 31
                  c.nop
                  sb         a0, 869(s8)
                  c.addi     s10, -10
                  auipc      t5, 495807
                  c.addi     a4, -27
                  lbu        t3, 428(s8)
                  sw         gp, 1006(s8)
                  lb         s7, 1326(s8)
                  c.addi     t3, 28
                  lbu        s7, -1523(s8)
                  sb         s4, 1130(s8)
                  srl        a2, tp, s1
                  auipc      t2, 509289
                  lb         t6, 1899(s8)
                  c.lui      gp, 16
                  auipc      s1, 627362
                  sh         a3, -506(s8)
                  sb         tp, -385(s8)
                  lh         t6, 486(s8)
                  lb         t5, 501(s8) #end riscv_load_store_rand_instr_stream_5
                  lui        s7, 151835
                  c.addi     s7, -10
                  c.addi     a4, 5
                  c.mv       s2, t3
                  c.addi     a3, -3
5888:             fence
                  slti       t6, t6, -887
                  mulhsu     t1, tp, t6
                  c.lui      a4, 11
                  auipc      a6, 213263
                  c.addi     a4, 25
                  c.sub      a3, a0
                  lui        s8, 381917
                  c.lui      s8, 14
                  mulhsu     t1, s9, s2
                  c.slli     t1, 26
                  bge        a2, sp, 5901f
                  c.srai     a0, 28
5901:             c.lui      s8, 17
                  auipc      a6, 468042
                  sll        a7, s10, a2
                  srai       t6, a4, 9
                  c.addi     s5, -19
                  c.addi     t4, 6
                  c.addi     gp, 15
                  lui        a3, 757358
                  c.and      a1, s1
                  c.addi     t2, -26
                  lui        s11, 987299
                  c.lui      t5, 14
                  c.srli     a5, 29
                  c.slli     s4, 17
                  c.and      a5, a2
                  c.lui      s1, 2
                  lui        gp, 210423
                  auipc      t1, 9379
                  remu       s10, t4, s11
                  auipc      s10, 855532
                  lui        s11, 72716
                  auipc      t3, 698568
                  c.addi     s5, -30
                  c.srli     a4, 29
                  auipc      s4, 612073
                  nop
                  auipc      t1, 592327
                  c.srli     a4, 19
                  c.addi     a7, -12
                  c.addi     a5, 20
                  c.addi     t4, -11
                  lui        s6, 102983
                  sll        s11, a2, s0
                  c.lui      t3, 10
                  c.addi     s7, -30
                  lui        a1, 78852
                  c.addi     s9, -28
                  sub        s1, t3, s2
                  c.srli     a5, 9
                  divu       t1, s6, gp
                  div        a4, sp, sp
                  c.addi     gp, 27
                  c.addi     t6, -31
                  c.mv       t5, t6
                  c.beqz     a1, 5947f
                  lui        t4, 747707
5947:             c.xor      a0, a5
                  auipc      a7, 219579
                  srl        a0, s9, s8
                  c.addi     t6, 31
                  c.addi     s5, -14
                  mulh       s1, s0, s0
                  lui        s2, 563521
                  c.addi     s7, -7
                  c.slli     t4, 11
                  c.addi     s0, 27
                  c.addi     s9, -3
                  c.srai     a4, 11
                  c.addi     gp, 31
                  xor        a5, s5, a2
                  c.bnez     a0, 5965f
                  c.addi     t2, 6
                  c.mv       s1, s5
                  c.slli     s7, 7
5965:             lui        s4, 555740
                  c.andi     a4, -7
                  c.lui      t1, 7
                  c.sub      s0, a3
                  c.srli     a4, 10
                  c.add      a3, a2
                  lui        s3, 405666
                  c.srai     s1, 4
                  c.srli     a4, 4
                  c.addi     a1, -30
                  lui        s0, 918418
                  c.addi     a4, -28
                  sra        s10, a7, s6
                  add        a5, s11, a6
                  c.sub      a4, a2
                  div        s9, t3, a0
                  lui        s4, 1017366
                  add        t3, a1, s2
                  c.srli     a3, 5
                  c.addi     s7, 28
                  c.addi     t2, -17
                  c.addi     a7, 5
                  auipc      t6, 923611
                  c.beqz     a3, 6004f
                  lui        a7, 814659
                  c.addi     t5, 1
                  div        a7, a5, zero
                  add        zero, s11, s2
                  la         t4, data_page_8+2089 #start riscv_load_store_rand_instr_stream_43
                  mulh       a7, s5, s9
                  lh         t5, 29(t4)
                  lhu        a6, 1047(t4)
                  sb         s10, -1659(t4)
                  lh         s2, 589(t4)
                  sb         t2, -1075(t4)
                  lui        s2, 968660
                  lui        t2, 874617
                  c.addi     s4, -22
                  mulhu      s1, s2, s3
                  nop
                  lui        s7, 636578
                  sb         s9, -762(t4)
                  c.sub      a3, a4
                  c.addi     s0, 8
                  lb         s7, 979(t4)
                  c.slli     t5, 30
                  lb         t1, 1042(t4)
                  lh         a7, 567(t4)
                  lui        zero, 132591
                  auipc      s3, 643553
                  lui        s2, 354559
                  lb         a0, 172(t4)
                  divu       s4, t2, a1
                  auipc      s7, 4127
                  lb         a1, 1667(t4)
                  lui        s9, 286921
                  xori       t6, a2, -654
                  c.slli     a3, 4
                  lbu        a7, 154(t4)
                  mulhsu     s9, zero, s8
                  lb         s3, -314(t4)
                  sh         tp, -1887(t4)
                  c.srai     a3, 12
                  c.addi     s10, 24
                  sb         a7, -357(t4)
                  c.lui      s5, 16
                  c.slli     s11, 3
                  c.addi     a1, -32
                  sb         a2, -1407(t4)
                  lb         s7, 1256(t4)
                  lbu        t1, -512(t4)
                  lui        a1, 430464
                  lbu        a2, -1105(t4)
                  auipc      s3, 942294
                  c.addi     gp, -14
                  sh         a6, -2043(t4)
                  lb         a1, -1955(t4)
                  lb         s7, 589(t4)
                  lbu        a2, -1076(t4)
                  lui        t1, 880230
                  c.addi     gp, -23
                  sb         t3, -277(t4)
                  lbu        a7, -1739(t4)
                  lh         a3, -1687(t4)
                  lb         s10, -1948(t4)
                  sb         s5, 84(t4)
                  lh         s2, -423(t4)
                  auipc      a1, 674691
                  lb         zero, -834(t4) #end riscv_load_store_rand_instr_stream_43
                  c.srli     a0, 15
                  sltiu      a0, s0, -95
                  lui        s0, 774614
                  srli       s2, t4, 7
                  addi       t1, s7, 325
                  add        s10, a5, ra
                  c.slli     t4, 24
                  xor        a4, s11, a2
                  lui        t4, 56405
                  c.lui      gp, 25
                  c.addi     s4, -32
6004:             c.slli     a7, 13
                  c.srai     a3, 22
                  c.slli     a0, 4
                  auipc      s3, 897699
                  lui        a0, 85458
                  divu       t3, t3, tp
                  lui        a3, 460354
                  bne        t5, a6, 6020f
                  c.addi     a5, -4
                  c.srai     a3, 18
                  lui        s7, 575426
                  c.slli     s6, 10
                  c.sub      a4, a4
                  c.srli     a3, 24
                  lui        a2, 713058
                  div        zero, a1, s3
6020:             c.addi     s2, -22
                  lui        s1, 336786
                  sra        t1, t6, s0
                  c.addi     t3, -9
                  c.xor      a5, s1
                  lui        s1, 384743
                  c.addi     a6, 6
                  c.slli     s0, 16
                  c.addi     t3, 24
                  ori        s5, s3, -241
                  auipc      a4, 897622
                  c.addi     a1, -30
                  c.addi     a3, 5
                  c.addi     t5, 12
                  lui        zero, 648550
                  srli       t4, t5, 19
                  la         s2, data_page_4+1758 #start riscv_load_store_rand_instr_stream_33
                  lb         zero, -81(s2)
                  c.lui      a0, 13
                  lbu        a7, -281(s2)
                  lb         s9, -1221(s2)
                  lhu        zero, 618(s2)
                  c.srai     a0, 15
                  sw         t4, 134(s2)
                  lb         s9, 582(s2)
                  sh         s5, 362(s2)
                  lh         t5, 442(s2)
                  c.lui      s9, 13
                  c.addi     s5, 18
                  sb         s6, -113(s2)
                  sb         tp, -182(s2)
                  lbu        s11, 1539(s2)
                  sb         t6, 1872(s2)
                  lb         t5, 1591(s2)
                  lh         a1, 926(s2)
                  sb         a1, 252(s2)
                  auipc      s8, 677348
                  lui        a4, 148047
                  c.sub      a2, a0
                  xor        t6, t6, s8
                  c.srai     a1, 23
                  lb         a1, 1538(s2)
                  lbu        a6, 211(s2)
                  c.li       s9, 9
                  c.lui      gp, 22
                  c.srli     a5, 9
                  lbu        t3, 1666(s2)
                  c.slli     s3, 24
                  sb         a4, 952(s2)
                  lbu        t4, -175(s2)
                  c.addi     a7, -27
                  sb         tp, -1279(s2)
                  c.lui      t1, 2
                  lhu        s8, -256(s2)
                  sw         ra, 630(s2)
                  c.lui      t5, 18
                  sh         a5, 826(s2)
                  lb         a4, 567(s2) #end riscv_load_store_rand_instr_stream_33
                  c.addi     s9, 12
                  auipc      s8, 890975
                  srai       s11, t4, 8
                  c.addi     a7, 21
                  lui        a2, 974554
                  c.addi     t5, -6
                  slli       a4, s9, 13
                  c.srli     a3, 20
                  and        s4, t5, t3
                  lui        t3, 903160
                  c.srai     a5, 19
                  c.addi     a7, -28
                  slli       a1, s5, 18
                  auipc      s8, 645900
                  c.xor      s0, s1
                  c.srai     a4, 9
                  lui        s8, 768480
                  mul        s0, tp, s11
                  lui        s9, 598218
                  mul        a4, a5, s5
                  c.addi     t6, -19
                  c.addi     s6, 2
                  c.slli     s11, 27
                  c.nop
                  c.srli     a5, 27
                  c.addi     s5, 8
                  c.addi     t4, 27
                  auipc      zero, 508603
                  c.xor      s0, a5
                  c.lui      s3, 13
                  c.addi     s5, -6
                  c.lui      a7, 25
                  ori        a2, gp, -443
                  c.slli     a6, 19
                  srli       t6, a3, 6
                  c.srai     a0, 2
                  c.addi     t6, 29
                  c.addi     a0, -26
                  xori       a4, zero, 264
                  c.addi     a2, 26
                  c.addi     s1, -5
                  lui        t5, 808417
                  c.addi     a1, -16
                  auipc      a2, 852965
                  ori        gp, zero, -304
                  c.srli     a0, 21
                  auipc      t6, 685089
                  c.lui      a2, 30
                  lui        s10, 744503
                  lui        s6, 898879
                  c.addi     gp, 11
                  auipc      s3, 73157
                  mulhsu     t2, s5, a0
                  c.addi     s5, -18
                  nop
                  c.slli     a1, 12
                  c.lui      gp, 13
                  mulhu      s5, a0, s1
                  c.srli     a1, 20
                  c.lui      t3, 29
                  c.srai     a0, 18
                  c.srli     s1, 1
                  andi       gp, s9, 198
                  c.lui      t5, 13
                  c.addi     s4, -9
                  c.srli     a0, 24
                  c.addi     s9, 15
                  c.lui      t3, 12
                  c.srli     a1, 24
                  auipc      s5, 726446
                  c.and      a1, a3
                  remu       a2, s11, s4
                  c.andi     a0, -2
                  c.srli     a4, 1
                  c.addi     t5, -2
                  auipc      s7, 570581
                  c.addi     a7, 15
                  auipc      t1, 903463
                  c.slli     s7, 31
                  lui        t4, 237561
                  c.lui      t5, 4
                  c.li       s1, 23
                  mul        s10, s8, tp
                  c.addi     a5, -11
                  c.addi     s9, -18
                  c.andi     s0, -20
                  c.srai     a0, 22
                  auipc      s9, 549229
                  lui        s3, 775720
                  lui        s1, 211642
                  c.addi     t6, -10
                  c.xor      a1, s0
                  c.li       s11, -30
                  c.srli     a5, 15
                  addi       t1, tp, -81
                  c.srai     a4, 27
                  auipc      a1, 150357
                  sra        gp, s9, a2
                  divu       s10, a3, s10
                  c.addi     t2, 23
                  c.srli     s1, 4
                  c.slli     t2, 8
                  c.lui      s7, 17
                  la         s1, data_page_14+2749 #start riscv_load_store_rand_instr_stream_54
                  lui        a5, 560312
                  c.addi     s6, 6
                  c.addi     t3, -12
                  auipc      a2, 630373
                  rem        a7, t2, a1
                  c.addi     t4, -9
                  c.slli     t3, 10
                  lbu        zero, -868(s1)
                  lbu        s3, -270(s1)
                  lhu        t1, 505(s1)
                  lb         gp, -1395(s1)
                  c.srli     s0, 20
                  c.srli     a2, 13
                  sb         s6, -1964(s1)
                  lb         t2, -881(s1)
                  lbu        s5, 856(s1)
                  c.srai     s0, 1
                  and        s6, s8, a4
                  lbu        a4, 1132(s1)
                  c.lui      gp, 10
                  lbu        a1, 1044(s1)
                  c.addi     t3, 22
                  lb         s9, 614(s1)
                  sb         a0, 237(s1)
                  sb         t3, -561(s1)
                  sb         t6, -1188(s1)
                  lbu        t3, 230(s1)
                  c.mv       s11, s1
                  lbu        gp, 665(s1)
                  lbu        a3, -1332(s1)
                  lui        s5, 194324
                  sra        s10, t1, s0
                  c.addi     a1, 11
                  sb         tp, -1128(s1)
                  c.addi     s11, 14
                  lb         a2, 245(s1)
                  lb         a1, -80(s1)
                  sh         s4, 1189(s1)
                  lb         t4, 778(s1)
                  nop
                  lbu        a2, -1976(s1)
                  sw         a3, -717(s1)
                  lb         s11, 1220(s1)
                  auipc      zero, 960622
                  sh         a3, 1003(s1)
                  auipc      a3, 996092
                  auipc      a2, 740825
                  c.addi     a2, 2
                  sb         s7, -782(s1)
                  c.and      a3, s0
                  c.addi     s3, -5
                  lui        t1, 741759
                  lb         a7, -8(s1)
                  lbu        a0, -1739(s1)
                  c.addi     s7, -13
                  c.srli     a1, 31
                  lui        s11, 1027909
                  rem        a1, tp, t5
                  lbu        s7, 1052(s1) #end riscv_load_store_rand_instr_stream_54
                  lui        t2, 346099
                  c.or       a4, s1
                  c.addi     t3, 25
                  nop
                  lui        gp, 215211
                  c.addi     s10, -3
                  lui        a3, 288166
                  c.beqz     s0, 6158f
                  c.srli     s0, 29
                  lui        a2, 697203
                  lui        s3, 449582
                  c.addi     a0, 3
                  xori       s6, a0, -647
                  lui        a4, 812365
                  c.srli     a5, 16
                  c.srai     s1, 27
                  c.bnez     a5, 6170f
                  c.addi     a2, -12
                  c.srli     a2, 18
6158:             lui        t4, 587724
                  c.addi     s11, -30
                  auipc      s8, 830759
                  c.addi     s2, -2
                  mulhsu     s10, gp, a6
                  auipc      t3, 611486
                  c.srai     s0, 23
                  c.addi     s9, 16
                  auipc      s11, 648359
                  c.srai     a4, 31
                  c.srai     a2, 26
                  slli       s10, sp, 10
6170:             auipc      s4, 352247
                  ori        a1, s0, -565
                  c.slli     s2, 16
                  lui        s0, 91260
                  sll        s2, a4, s3
                  c.addi     a2, -3
                  auipc      t4, 930413
                  c.slli     s6, 24
                  auipc      t3, 918857
                  c.andi     a4, -2
                  auipc      a5, 521883
                  c.addi     s1, 31
                  auipc      a4, 929475
                  add        s5, s11, t0
                  c.addi     a1, 28
                  c.addi     s2, 27
                  c.slli     a7, 22
                  c.srli     s0, 17
                  c.addi     a7, -14
                  c.addi     s8, 11
                  auipc      s4, 374343
                  c.srai     a2, 4
                  mulhsu     s7, s7, t5
                  c.addi     s2, -23
                  c.addi     t3, 23
                  c.bnez     a4, 6206f
                  c.lui      s11, 8
                  c.addi     a3, 23
                  slt        s9, a6, a1
                  auipc      s3, 223168
                  srl        t2, ra, s0
                  lui        t1, 189886
                  c.addi     s11, 24
                  c.addi     s10, 8
                  c.addi     gp, -20
                  auipc      s0, 719847
6206:             c.beqz     a2, 6207f
6207:             c.addi     s8, -15
                  ori        s11, ra, 631
                  lui        t2, 915472
                  c.addi     s2, 29
                  c.addi     a5, 13
                  lui        t5, 392494
                  c.addi     t4, 12
                  c.addi     t5, 19
                  c.addi     s10, -32
                  auipc      a2, 390536
                  lui        s0, 64511
                  lui        a4, 665591
                  bne        gp, s3, 6233f
                  c.addi     s3, -28
                  c.srli     a4, 28
                  c.addi     t2, 9
                  c.addi     t3, -27
                  c.addi     t6, -22
                  fence
                  auipc      s4, 914059
                  slli       a6, a3, 0
                  c.addi     t4, -1
                  c.addi     a7, -10
                  c.addi     s6, 28
                  srl        s3, a6, s1
                  lui        t2, 756220
6233:             remu       s2, t6, ra
                  c.srli     a3, 12
                  auipc      a3, 25933
                  la         s1, data_page_15+1360 #start riscv_load_store_rand_instr_stream_8
                  lh         t6, -102(s1)
                  slli       gp, a3, 16
                  c.addi     a2, -5
                  c.slli     s4, 21
                  c.srai     a2, 26
                  c.srli     a4, 20
                  c.srli     a0, 31
                  sb         s10, 2030(s1)
                  lui        s5, 480856
                  lui        t4, 786976
                  c.srli     a0, 17
                  auipc      s8, 957605
                  c.and      s0, a2
                  sh         s11, -436(s1)
                  lb         a5, -1213(s1)
                  sb         s2, 1559(s1)
                  lh         s10, 444(s1)
                  sb         a3, 12(s1)
                  lui        a5, 464908
                  lbu        t6, 949(s1)
                  c.srli     a5, 7
                  sh         s10, 252(s1)
                  c.addi     t5, 26
                  auipc      s10, 36453
                  c.srli     s0, 29
                  c.addi     s4, -31
                  srl        s0, a5, t6
                  lui        t4, 658143
                  lui        a4, 780050
                  lbu        t1, -143(s1)
                  c.addi     a2, -31
                  sll        a6, a5, s4
                  lb         a7, -94(s1)
                  lb         a2, 1854(s1)
                  lh         s3, 156(s1)
                  c.addi     s6, -30
                  lbu        t6, -145(s1)
                  lbu        s8, -93(s1)
                  lhu        a2, -10(s1) #end riscv_load_store_rand_instr_stream_8
                  auipc      s0, 117747
                  lui        s3, 759405
                  c.addi     s10, -29
                  c.lui      t2, 31
                  c.srli     a4, 13
                  c.addi     s7, 3
                  c.addi     t4, -1
                  lui        s9, 499270
                  lui        t1, 207199
                  c.addi     gp, -25
                  c.srli     a2, 10
                  divu       a1, t4, s11
                  c.nop
                  auipc      s4, 357441
                  c.addi     s7, -26
                  c.slli     a7, 26
                  c.addi     t6, -20
                  c.li       t1, 5
                  c.addi     s9, 13
                  auipc      a6, 699841
                  auipc      t4, 10917
                  c.add      a5, a2
                  auipc      t2, 443800
                  c.sub      a5, a2
                  bltu       t0, s1, 6277f
                  c.addi     t1, 27
                  c.srli     a5, 7
                  lui        a3, 461561
                  c.addi     s11, -24
                  sltu       t4, s1, s3
                  c.srli     a4, 31
                  lui        a3, 829387
                  c.srai     s0, 10
                  c.srai     a2, 11
                  c.addi     s8, 26
                  c.lui      a3, 12
                  c.addi     s6, 2
                  auipc      s3, 1013522
                  c.srli     a0, 3
                  auipc      s1, 960682
                  auipc      s0, 755759
6277:             lui        zero, 902527
                  c.srli     a1, 17
                  rem        s7, s5, ra
                  c.addi     s9, -25
                  c.slli     s9, 24
                  c.addi     t4, -31
                  xori       a4, s3, 541
                  blt        s3, s6, 6288f
                  c.addi     t2, -28
                  bge        a5, zero, 6298f
                  c.addi     t5, -20
6288:             c.addi     s0, -10
                  auipc      s3, 782574
                  sll        a7, t3, s0
                  c.addi     s1, -14
                  c.addi     a7, 1
                  c.addi     a3, -9
                  c.addi     t5, -10
                  c.addi     s11, -1
                  divu       a6, s11, s4
                  div        a4, a0, zero
6298:             c.addi     s9, 7
                  c.addi     a2, 18
                  c.addi     s10, 28
                  auipc      a4, 789256
                  srli       s2, s4, 14
                  c.srli     s0, 5
                  auipc      s3, 270620
                  lui        s10, 52244
                  c.addi     a6, 31
                  c.slli     a4, 5
                  c.addi     s9, -19
                  rem        t4, s2, a2
                  lui        a4, 77149
                  c.slli     a7, 17
                  c.and      a5, a2
                  c.addi     s3, -26
                  c.slli     a5, 9
                  lui        s11, 826012
                  c.addi     a4, 6
                  lui        s9, 706772
                  c.slli     s7, 19
                  c.slli     s1, 13
                  sll        s9, s7, s4
                  c.srai     s1, 27
                  c.srli     a0, 2
                  auipc      s3, 855020
                  c.addi     s5, -32
                  lui        zero, 265981
                  c.slli     t4, 27
                  srli       t5, ra, 12
                  c.addi     s11, 9
                  c.srai     a5, 10
                  srli       s3, s8, 19
                  and        t3, s7, s10
                  auipc      s8, 795375
                  c.lui      s7, 3
                  c.and      a4, a0
                  blt        t0, s10, 6338f
                  c.addi     s4, 20
                  c.slli     t3, 26
6338:             auipc      t1, 918674
                  c.srli     s1, 4
                  c.srli     a3, 23
                  lui        zero, 777047
                  c.addi     s10, -1
                  c.beqz     a3, 6351f
                  lui        s0, 75992
                  c.srli     a1, 29
                  c.srli     a0, 2
                  auipc      t5, 776612
                  srli       s9, t4, 27
                  c.lui      a4, 13
                  c.slli     s4, 21
6351:             auipc      s5, 237098
                  c.lui      s3, 23
                  c.addi     s4, 17
                  la         a7, data_page_4+2287 #start riscv_load_store_rand_instr_stream_36
                  lui        s4, 410336
                  lui        a5, 563446
                  lh         s7, -917(a7)
                  c.li       s10, -23
                  c.addi     a2, 13
                  lui        s6, 460563
                  c.addi     s6, -16
                  c.slli     s6, 15
                  c.addi     t2, 18
                  fence.i
                  auipc      s5, 389991
                  c.add      a4, s1
                  auipc      s5, 354794
                  sb         a0, -1840(a7)
                  lh         a4, -969(a7)
                  c.addi     s8, 18
                  fence
                  c.and      s1, s1
                  c.slli     s5, 26
                  lbu        t3, -1362(a7)
                  lb         a5, -2015(a7)
                  sb         a6, 432(a7)
                  c.or       a4, a4
                  lbu        s11, 430(a7)
                  lb         s7, 1567(a7)
                  lb         a5, 78(a7)
                  c.addi     s10, -16
                  c.lui      a5, 30
                  c.lui      s11, 17
                  lbu        a6, -1214(a7)
                  lbu        s9, -1954(a7)
                  lb         s9, -822(a7)
                  lui        s7, 948747
                  c.srli     a4, 14
                  c.addi     t5, 17
                  lui        t1, 177905
                  c.addi     gp, 19
                  lbu        t1, 1135(a7)
                  lbu        s10, -1401(a7)
                  c.mv       s3, gp
                  lbu        s10, 1794(a7)
                  lb         t1, -1125(a7)
                  auipc      t4, 605809
                  lb         s8, 795(a7)
                  sh         t4, 1047(a7) #end riscv_load_store_rand_instr_stream_36
                  c.addi     a5, 21
                  lui        gp, 278634
                  c.lui      t1, 27
                  c.lui      t5, 23
                  lui        gp, 126356
                  c.srli     a4, 11
                  c.lui      s4, 17
                  slt        s1, s0, t5
                  c.addi     a4, -30
                  sra        a6, zero, a5
                  c.srli     a2, 7
                  c.addi     t4, 19
                  sltu       a7, s0, ra
                  lui        s4, 243425
                  bltu       gp, t2, 6385f
                  lui        s11, 188299
                  c.addi     t4, -25
                  auipc      s9, 539523
                  c.addi     a4, 14
                  lui        a4, 918573
                  slli       a1, s2, 12
                  c.srai     a1, 23
                  c.addi     t3, 2
                  c.addi     t6, -30
                  auipc      a0, 963886
                  c.addi     s7, 12
                  srli       a6, t3, 4
                  lui        a2, 143805
                  c.addi     t5, 29
                  lui        a0, 612640
                  auipc      s9, 656308
6385:             ori        s4, gp, -59
                  lui        s11, 671180
                  c.addi     s3, -3
                  sra        a6, a4, s6
                  c.addi     a5, 10
                  c.slli     s0, 11
                  c.slli     t3, 5
                  c.addi     a3, 20
                  c.addi     s7, 20
                  c.addi     a0, -1
                  auipc      s4, 504249
                  c.addi     s7, -32
                  c.srli     a4, 28
                  c.addi     t2, -22
                  c.lui      t6, 10
                  c.addi     a2, -23
                  sll        s0, s8, ra
                  c.addi     a4, 9
                  c.srai     a1, 8
                  c.addi     a2, 25
                  c.srai     s0, 13
                  srl        a5, s1, a1
                  addi       a7, s8, 340
                  lui        s0, 916839
                  lui        s1, 387801
                  fence.i
                  c.srli     a0, 12
                  c.slli     t5, 9
                  auipc      a2, 221369
                  c.srai     a1, 13
                  lui        s9, 206789
                  c.and      a3, a2
                  auipc      a4, 112845
                  auipc      a7, 401433
                  auipc      a5, 413878
                  c.slli     a3, 11
                  sltiu      t1, s11, 219
                  auipc      gp, 553781
                  c.lui      a6, 10
                  lui        t3, 65924
                  c.srli     a1, 11
                  c.addi     gp, 25
                  c.addi     s6, -8
                  c.addi     s10, -27
                  srli       zero, s3, 13
                  c.addi     a7, -24
                  c.addi     a2, 10
                  c.slli     s4, 23
                  c.lui      s9, 14
                  add        s3, s9, tp
                  lui        s2, 347828
                  c.lui      t4, 24
                  c.lui      t1, 10
                  c.addi     a3, -26
                  divu       a5, s3, s2
                  c.slli     s10, 1
                  nop
                  c.srai     a2, 20
                  c.srai     a0, 18
                  mulhu      a5, ra, t4
                  lui        s3, 490290
                  c.addi     a3, 22
                  c.addi     s2, -15
                  c.and      a4, a2
                  c.srli     a2, 28
                  c.addi     s0, -3
                  lui        t6, 989791
                  c.srli     a2, 21
                  c.lui      t6, 6
                  c.srai     a4, 15
                  c.addi     s4, 11
                  auipc      a5, 948832
                  xori       s1, s1, 358
                  div        a0, s5, a7
                  c.addi     a7, -12
                  blt        s7, t5, 6470f
                  lui        a4, 125563
                  fence
                  lui        s9, 562727
                  lui        t5, 965326
                  bge        a3, a7, 6470f
                  c.srai     a1, 30
                  c.addi     s5, -21
                  auipc      s10, 443833
                  c.sub      a4, a1
6470:             c.addi     s7, -7
                  c.srai     a5, 25
                  c.srai     a5, 10
                  c.slli     s4, 2
                  auipc      s8, 878981
                  c.srai     s0, 30
                  bltu       a1, t4, 6487f
                  auipc      gp, 751552
                  lui        t5, 509728
                  c.srai     s0, 13
                  lui        s9, 476439
                  c.andi     a4, -1
                  lui        a5, 727366
                  c.lui      s2, 23
                  c.addi     s11, 7
                  c.xor      a2, a1
                  c.srli     s0, 6
6487:             or         s7, s6, gp
                  c.lui      a1, 26
                  divu       t3, t5, sp
                  c.addi     s0, -13
                  c.srli     a2, 10
                  auipc      a2, 694835
                  c.srai     a4, 5
                  auipc      s1, 347525
                  auipc      s10, 61218
                  c.lui      s8, 4
                  divu       t6, s2, t6
                  c.addi     t3, 4
                  auipc      a3, 594521
                  c.slli     a2, 3
                  auipc      s6, 219875
                  auipc      s6, 1034821
                  auipc      a3, 645720
                  auipc      t1, 314746
                  c.slli     s1, 16
                  auipc      s11, 752181
                  auipc      s6, 828692
                  c.addi     t4, 20
                  c.addi     s2, 14
                  lui        zero, 808619
                  c.addi     a5, 12
                  c.addi     s6, 27
                  slli       zero, t6, 8
                  auipc      s2, 787267
                  c.and      a1, a2
                  c.addi     s7, 17
                  c.slli     a2, 19
                  auipc      t2, 422411
                  c.slli     s1, 9
                  lui        s7, 893668
                  c.addi     s0, 31
                  c.lui      s6, 6
                  c.lui      s8, 1
                  c.srli     a5, 14
                  auipc      a4, 399760
                  srl        a0, t1, t0
                  auipc      s11, 381110
                  c.addi     t5, -20
                  sltu       t2, t6, s10
                  ori        s3, s0, -904
                  div        s0, s7, a6
                  xori       a7, s11, 994
                  mulhu      a0, s11, a7
                  c.addi     t6, -19
                  c.addi     s0, -16
                  c.srai     a1, 27
                  c.srli     a4, 30
                  bgeu       s9, s11, 6554f
                  auipc      t4, 519384
                  auipc      zero, 259606
                  xori       s8, tp, 707
                  auipc      gp, 615253
                  auipc      a5, 754678
                  c.addi     s3, -3
                  c.addi     t5, 27
                  lui        a1, 193002
                  c.srai     a4, 18
                  c.addi     s0, 2
                  sra        zero, s7, s4
                  auipc      a4, 556123
                  c.slli     s0, 21
                  c.slli     s10, 22
                  c.addi     t5, 30
6554:             c.addi     a6, 3
                  bltu       t3, tp, 6558f
                  auipc      a7, 619025
                  auipc      s3, 930885
6558:             c.slli     s9, 27
                  auipc      s5, 515770
                  c.srai     a1, 30
                  c.addi     a3, 6
                  c.addi     a4, -12
                  c.addi     t5, 21
                  c.addi     gp, -22
                  lui        a3, 393990
                  c.lui      t5, 22
                  auipc      s6, 749999
                  c.slli     s5, 22
                  c.addi     s10, -4
                  c.nop
                  c.addi     s0, 5
                  c.addi     a0, -26
                  c.addi     gp, 3
                  auipc      a1, 814881
                  srl        s0, t6, t3
                  auipc      a3, 837850
                  lui        a1, 463851
                  c.addi     s4, -29
                  lui        a1, 71125
                  c.addi     s11, -1
                  c.addi     s2, 15
                  auipc      s4, 727713
                  c.add      s0, s1
                  lui        s0, 927011
                  c.slli     s0, 11
                  c.addi     a2, -9
                  lui        s10, 651736
                  c.slli     a7, 2
                  auipc      a0, 68537
                  auipc      s9, 883371
                  c.addi     s9, 3
                  c.srli     a2, 15
                  auipc      s3, 104888
                  lui        s9, 9050
                  c.mv       t6, a2
                  lui        zero, 595255
                  div        t6, s11, zero
                  c.srli     a5, 19
                  c.addi     a2, -27
                  c.slli     a7, 18
                  c.lui      s3, 30
                  div        a6, a5, a7
                  c.andi     s1, 26
                  fence
                  sltu       s6, s1, a2
                  sub        s5, s6, a3
                  bgeu       t6, t4, 6609f
                  c.addi     t5, 13
6609:             auipc      a6, 765252
                  c.srli     a4, 30
                  divu       a0, t6, s4
                  c.addi     s10, -12
                  mulh       a5, s4, t3
                  c.addi     s8, -5
                  c.and      a5, s1
                  bne        a1, t2, 6633f
                  c.lui      s1, 1
                  c.srai     a0, 23
                  c.srli     a3, 17
                  c.addi     a5, 23
                  sltu       zero, t6, t1
                  c.addi     s1, 22
                  lui        s8, 780771
                  c.srai     a3, 9
                  c.addi     s2, 4
                  srai       gp, a1, 11
                  remu       a5, a2, s5
                  c.srli     s0, 12
                  fence
                  lui        t3, 325857
                  c.slli     s8, 17
                  c.srai     a4, 15
6633:             c.addi     a2, 6
                  c.srli     a5, 17
                  c.srai     a5, 24
                  auipc      s9, 162595
                  c.addi     t2, 23
                  lui        s0, 526464
                  c.slli     t1, 28
                  c.srli     a3, 12
                  c.addi     t4, 20
                  mul        t1, a2, s4
                  auipc      a3, 345515
                  sll        t4, s1, a3
                  lui        s10, 271386
                  remu       a3, s0, s10
                  c.andi     a5, 24
                  c.slli     s9, 14
                  auipc      zero, 169251
                  c.li       t1, 0
                  lui        s6, 409164
                  c.addi     s9, -16
                  lui        a7, 68534
                  c.addi     a2, 11
                  c.li       s9, 22
                  c.beqz     s0, 6670f
                  c.xor      a1, a2
                  c.srli     a1, 26
                  c.srai     a4, 11
                  c.and      a2, s1
                  c.srli     a2, 7
                  auipc      s0, 354797
                  c.srai     a3, 16
                  lui        t1, 495745
                  c.addi     a1, 25
                  lui        a5, 545164
                  bgeu       t5, s8, 6675f
                  bge        gp, s8, 6678f
                  mulh       t5, t5, t4
6670:             c.addi     s4, 2
                  c.srli     a3, 28
                  c.slli     t2, 28
                  c.nop
                  c.addi     a5, 2
6675:             auipc      a5, 664441
                  c.srli     a3, 8
                  c.addi     s2, -27
6678:             c.addi     a6, -13
                  c.slli     t3, 23
                  auipc      s11, 511041
                  auipc      s2, 705944
                  mulhsu     t4, s10, s0
                  auipc      s11, 207047
                  fence
                  c.addi     s4, 24
                  c.addi     s7, -11
                  lui        t5, 401823
                  c.addi     a4, -1
                  c.srli     a5, 8
                  div        s10, ra, a1
                  c.lui      s8, 17
                  lui        s7, 728956
                  lui        t3, 116194
                  sub        s3, t3, sp
                  c.lui      s2, 29
                  mul        s9, s5, t1
                  c.slli     s5, 9
                  c.addi     t1, 13
                  la         s4, data_page_19+1981 #start riscv_load_store_rand_instr_stream_57
                  lb         a2, 1853(s4)
                  c.lui      s6, 13
                  lui        s11, 616694
                  c.lui      s10, 21
                  lui        s1, 697315
                  auipc      zero, 855873
                  c.addi     a7, 21
                  c.addi     s5, -28
                  c.lui      s9, 19
                  lui        s6, 267524
                  lb         t2, -1946(s4)
                  andi       t4, s2, 820
                  c.addi     s11, 13
                  lui        s8, 255685
                  sub        t1, t0, zero
                  sb         a7, 222(s4)
                  lui        s8, 571896
                  auipc      zero, 391782
                  c.srai     s1, 26
                  auipc      s6, 582603
                  c.addi     a4, -24
                  lb         a6, -1105(s4)
                  nop
                  c.lui      a7, 22
                  lb         gp, 1374(s4)
                  auipc      t5, 656594
                  addi       s7, sp, 687
                  lw         a1, -673(s4)
                  lui        s2, 734286
                  c.addi     s0, -2
                  lbu        s11, 1241(s4)
                  addi       s7, tp, -960
                  c.srli     a5, 25
                  lb         s8, -1880(s4)
                  lbu        a7, 1461(s4)
                  sb         t1, 1728(s4)
                  c.slli     s11, 3
                  c.addi     s8, -9
                  auipc      a4, 281091
                  c.srai     a2, 1
                  lb         a5, 1050(s4) #end riscv_load_store_rand_instr_stream_57
                  c.slli     a1, 22
                  lui        s5, 750051
                  lui        t3, 667394
                  c.srai     s1, 27
                  nop
                  auipc      s9, 145590
                  c.srli     s1, 13
                  c.addi     a6, 10
                  bne        s5, s0, 6718f
                  c.addi     s5, -12
                  auipc      s0, 981512
                  c.lui      a7, 8
                  andi       s7, t1, -820
                  bgeu       t2, s5, 6725f
                  c.addi     s10, -8
                  c.srli     a3, 20
                  c.srli     a1, 24
                  c.addi     t4, -17
                  c.lui      s7, 20
6718:             c.srli     a3, 2
                  lui        s0, 43313
                  c.srai     a5, 22
                  auipc      s2, 698113
                  lui        s1, 328023
                  auipc      s2, 90995
                  c.andi     s0, 8
6725:             c.addi     a4, -4
                  c.slli     t2, 1
                  c.srai     a0, 6
                  sltiu      s10, s10, 227
                  c.slli     s3, 11
                  add        s6, a3, s4
                  c.srai     a0, 5
                  auipc      s0, 992855
                  lui        s10, 945794
                  auipc      s3, 429783
                  c.addi     s0, -16
                  c.addi     s8, -16
                  c.addi     a1, -23
                  c.srai     a2, 11
                  c.srli     a3, 27
                  c.addi     s0, -11
                  c.addi     s5, 11
                  c.mv       t4, t0
                  sltu       s11, s2, s4
                  c.addi     t1, -31
                  c.addi     s0, -19
                  auipc      s1, 277246
                  slti       t1, s9, -180
                  auipc      t6, 510911
                  auipc      t1, 384561
                  c.beqz     s1, 6751f
6751:             auipc      gp, 496610
                  auipc      a2, 1006210
                  lui        zero, 46450
                  slt        t4, s0, gp
                  lui        a0, 934581
                  c.addi     t2, 3
                  mul        s7, s5, gp
                  sll        s1, gp, gp
                  and        s3, s5, a3
                  lui        s7, 795203
                  auipc      a4, 886156
                  auipc      t1, 921354
                  c.slli     s1, 3
                  c.addi     s5, -11
                  c.addi     a5, 6
                  lui        t1, 619901
                  bltu       t5, a2, 6774f
                  sltiu      t4, a2, 838
                  c.srli     a0, 3
                  c.lui      a1, 9
                  auipc      a2, 109991
                  slt        s9, gp, s2
                  c.srai     s0, 26
6774:             c.srai     s1, 16
                  sub        zero, a4, a0
                  sltu       a3, t6, t1
                  lui        a2, 413123
                  lui        s0, 407415
                  c.addi     t1, 8
                  mulh       s1, s6, s8
                  c.srai     a0, 24
                  c.addi     s11, -30
                  lui        a1, 963883
                  lui        s3, 708306
                  c.addi     a7, -20
                  c.addi     t6, 23
                  c.srli     a2, 24
                  fence
                  c.addi     a7, 1
                  c.srli     a0, 8
                  lui        t2, 51333
                  auipc      s5, 780314
                  c.srai     s0, 9
                  c.addi     a4, 9
                  auipc      s9, 232642
                  c.lui      s11, 21
                  auipc      s8, 654592
                  lui        s1, 631525
                  sltiu      zero, s8, -613
                  c.addi     s0, 8
                  c.lui      a5, 27
                  c.slli     a7, 23
                  auipc      gp, 568692
                  c.srli     s0, 6
                  auipc      t5, 769667
                  c.addi     a7, -5
                  c.slli     t2, 29
                  c.mv       a0, s3
                  blt        s11, t0, 6812f
                  c.addi     s5, 11
                  lui        a2, 88060
6812:             c.lui      a7, 30
                  c.slli     s7, 15
                  sltu       t4, s9, s10
                  c.nop
                  c.srai     s0, 13
                  auipc      s9, 848226
                  andi       s9, s5, 43
                  c.lui      s1, 2
                  slli       s3, zero, 9
                  lui        s8, 476540
                  auipc      a0, 370801
                  c.or       a5, s0
                  and        a7, ra, s8
                  c.addi     s11, 21
                  auipc      s1, 250742
                  auipc      s2, 56165
                  c.srli     a5, 7
                  c.addi     a0, 6
                  auipc      t4, 708790
                  fence.i
                  c.add      a1, a5
                  c.srli     s1, 17
                  c.lui      s9, 13
                  lui        a5, 786705
                  lui        t6, 386647
                  bgeu       a4, a0, 6841f
                  c.addi     a2, 24
                  c.addi     s0, 13
                  c.and      a4, a4
6841:             c.slli     s8, 20
                  c.lui      a3, 30
                  c.or       s1, a2
                  c.lui      t2, 9
                  c.srli     a1, 19
                  lui        t1, 350127
                  c.lui      s10, 4
                  c.lui      gp, 15
                  c.addi     a1, -32
                  c.addi     s11, 3
                  c.lui      s11, 26
                  addi       t2, s0, -566
                  auipc      s9, 719525
                  slli       s1, t5, 19
                  c.or       a5, a2
                  lui        s2, 953895
                  auipc      t2, 496041
                  c.srli     s1, 26
                  auipc      a4, 999116
                  c.srli     a3, 26
                  c.li       s10, -12
                  remu       gp, s4, t1
                  divu       s11, s9, s10
                  add        a6, s7, a6
                  fence.i
                  c.slli     s4, 16
                  auipc      t5, 916819
                  c.slli     s8, 4
                  c.addi     t2, -23
                  lui        zero, 733504
                  c.srli     s1, 26
                  c.srai     a0, 21
                  c.srai     a0, 2
                  c.addi     s10, 17
                  auipc      a6, 70677
                  blt        t5, t5, 6893f
                  c.addi     s8, 21
                  c.addi     s8, -23
                  la         t2, data_page_5+2156 #start riscv_load_store_rand_instr_stream_42
                  c.addi     s6, -14
                  c.addi     a4, -4
                  lh         s10, -1828(t2)
                  lui        t1, 490007
                  lb         a2, -1811(t2)
                  sb         ra, 1129(t2)
                  lb         s8, -1883(t2)
                  sh         s9, 1508(t2)
                  c.addi     t5, 25
                  lb         s2, 1693(t2)
                  c.addi     s3, -18
                  lb         t3, 1211(t2)
                  lui        a3, 1044530
                  lb         s3, -625(t2)
                  lw         s3, 688(t2)
                  lui        a5, 220733
                  slt        a6, a4, a4
                  lh         a3, -616(t2)
                  c.addi     s8, -9
                  c.slli     a6, 12
                  lb         s9, -1607(t2)
                  sb         t4, -146(t2)
                  auipc      t5, 676926
                  lh         s11, 290(t2)
                  sb         s1, 190(t2)
                  lw         a1, 728(t2)
                  lb         a6, 391(t2)
                  c.lui      t1, 23
                  c.srai     a1, 24
                  sh         t5, 282(t2)
                  sb         a2, 560(t2)
                  sb         s2, -909(t2)
                  lb         t1, 357(t2)
                  c.slli     a3, 27
                  lhu        s4, -1124(t2)
                  c.addi     t4, 19
                  lbu        t5, -1459(t2)
                  c.mv       s0, a3
                  sw         t2, 1196(t2)
                  sb         a0, 682(t2)
                  mulhsu     s3, t6, s3
                  sh         s9, 114(t2)
                  lui        s3, 8626
                  sb         a7, -1738(t2)
                  lb         s5, -950(t2) #end riscv_load_store_rand_instr_stream_42
                  auipc      a6, 239478
                  c.addi     s6, 5
                  c.or       s0, a0
                  srli       t2, a0, 14
                  srai       zero, s3, 22
                  c.addi     a3, -2
                  lui        a3, 361689
                  div        t4, s3, a7
                  c.srai     a2, 29
                  lui        t4, 673941
                  mulhsu     a3, a7, s1
                  sltiu      a5, s6, -374
                  c.addi     s4, -14
                  lui        s4, 855682
6893:             c.beqz     s0, 6909f
                  slti       t6, a6, -497
                  c.addi     t2, 2
                  c.srli     a4, 19
                  and        a5, s8, s10
                  mulhu      s3, s7, s6
                  c.addi     a0, -10
                  c.lui      t3, 17
                  lui        a3, 556874
                  mulhu      a6, a4, a7
                  c.and      a4, a4
                  c.srli     s1, 30
                  c.slli     s11, 10
                  c.slli     s6, 13
                  c.addi     t5, -14
                  xori       gp, a3, -827
6909:             c.addi     s8, -31
                  lui        t1, 140682
                  c.addi     s2, 9
                  c.lui      s10, 6
                  and        s0, s10, t2
                  bltu       s11, s7, 6927f
                  c.srai     s0, 27
                  c.srli     a1, 21
                  auipc      t1, 314973
                  c.lui      gp, 4
                  c.addi     a3, 7
                  auipc      s11, 204743
                  c.addi     s11, 1
                  slli       s3, t3, 20
                  or         a5, s0, sp
                  lui        a4, 14004
                  remu       s4, s0, s5
                  c.addi     t2, 10
6927:             c.addi     t6, 22
                  auipc      a2, 156291
                  lui        zero, 2766
                  c.srai     a3, 19
                  fence
                  c.addi     gp, -26
                  c.addi     gp, -4
                  c.addi     s3, 18
                  lui        zero, 712721
                  c.addi     a4, 24
                  lui        t2, 539046
                  auipc      s11, 758209
                  auipc      a6, 61953
                  c.mv       a5, ra
                  c.srli     a2, 7
                  auipc      a1, 350503
                  c.addi     a7, 4
                  c.or       a3, a3
                  c.sub      a5, a1
                  c.srai     a1, 14
                  c.mv       s2, t1
                  c.addi     a1, -31
                  auipc      s0, 785830
                  auipc      t6, 511908
                  c.srli     a1, 30
                  c.lui      s1, 23
                  sltiu      t6, zero, -876
                  lui        a3, 485980
                  c.addi     a2, -15
                  c.srli     s1, 26
                  bne        gp, a1, 6960f
                  c.slli     s4, 22
                  c.slli     s9, 15
6960:             auipc      s8, 569155
                  sll        s3, t2, s0
                  auipc      t6, 290377
                  c.addi     s0, 18
                  auipc      a3, 1027553
                  sll        t4, a4, sp
                  c.srli     s0, 24
                  c.addi     s2, 4
                  auipc      t3, 568089
                  c.lui      s6, 22
                  lui        s9, 182889
                  remu       t2, t4, s11
                  c.addi     s6, 28
                  c.addi     t4, -26
                  nop
                  lui        s3, 648922
                  c.addi     a3, 15
                  lui        a1, 641513
                  lui        t6, 648216
                  c.srli     a4, 25
                  c.srai     a5, 17
                  c.addi     t2, -16
                  mulhu      s9, a2, s0
                  c.addi     a5, -9
                  auipc      t2, 859625
                  c.srli     a5, 2
                  ori        a5, t6, -471
                  c.srai     s0, 8
                  c.srai     a0, 21
                  bne        a6, s4, 6997f
                  sub        a7, s11, s2
                  slti       s9, s5, 616
                  c.add      s1, a0
                  c.addi     t1, 22
                  and        t1, a2, sp
                  lui        a2, 727256
                  auipc      s0, 660299
6997:             c.srai     a0, 3
                  remu       a2, sp, t1
                  c.addi     s2, 18
                  c.slli     t4, 12
                  c.srai     a1, 18
                  mulh       t4, s2, s10
                  lui        s9, 248523
                  c.addi     s9, -10
                  c.addi     a4, 26
                  c.srai     a4, 28
                  c.addi     s7, 28
                  c.addi     t3, 26
                  la         s11, data_page_11+2699 #start riscv_load_store_rand_instr_stream_10
                  sb         a6, -1753(s11)
                  auipc      a2, 329432
                  c.addi     a4, 21
                  sh         a7, -183(s11)
                  andi       t4, s8, 643
                  c.addi     t6, 14
                  sb         ra, 1351(s11)
                  c.srai     s1, 1
                  auipc      s0, 349524
                  c.lui      s10, 4
                  srai       s10, ra, 1
                  c.addi     t1, 19
                  sb         t5, -157(s11)
                  divu       s6, a3, a2
                  lhu        s1, 1267(s11)
                  fence.i
                  lb         a3, -784(s11)
                  lui        zero, 729020
                  sh         ra, 1137(s11)
                  sw         a0, -1499(s11)
                  sb         s2, -733(s11)
                  c.addi     t3, -5
                  lui        s10, 78802
                  c.slli     s2, 15
                  sb         s10, -265(s11)
                  auipc      s2, 189427
                  sra        t5, s7, ra
                  c.li       t4, 24
                  auipc      t3, 591440
                  sw         t0, 617(s11)
                  sb         s10, -688(s11)
                  sltu       s9, a6, s4
                  lbu        t4, -805(s11)
                  sb         a4, -1123(s11)
                  sh         a7, 275(s11)
                  c.addi     s1, -29
                  lbu        a4, -1272(s11)
                  lb         a0, -1784(s11)
                  lbu        s1, 75(s11)
                  sb         t4, -830(s11)
                  c.li       s8, 11
                  c.addi     a5, -6
                  c.addi     s3, 29
                  c.lui      t5, 23
                  c.srai     a5, 13
                  sh         ra, -1561(s11) #end riscv_load_store_rand_instr_stream_10
                  c.addi     t3, -2
                  auipc      a7, 758696
                  c.slli     s7, 3
                  c.lui      s10, 9
                  c.addi     a3, -24
                  c.slli     gp, 24
                  c.addi     a5, 4
                  sltiu      s4, s10, 849
                  c.srli     a0, 8
                  xori       s10, zero, -532
                  c.slli     a4, 3
                  c.slli     s4, 13
                  c.addi     s0, -32
                  c.addi     s11, -30
                  remu       a3, a1, sp
                  c.beqz     s1, 7031f
                  c.srai     a2, 3
                  lui        gp, 100307
                  auipc      t6, 42229
                  c.srai     s0, 22
                  c.slli     t3, 22
                  c.slli     a2, 8
7031:             auipc      t4, 1037428
                  lui        s3, 570292
                  c.addi     s0, 31
                  c.lui      s0, 20
                  c.add      a3, a0
                  lui        a0, 851689
                  c.srai     a5, 2
                  c.addi     t1, -6
                  c.addi     s6, 10
                  auipc      s0, 161487
                  lui        t1, 998134
                  c.srai     s1, 19
                  auipc      a5, 1029193
                  c.lui      a2, 7
                  lui        s0, 292016
                  lui        s7, 280008
                  auipc      gp, 494215
                  c.addi     t4, -16
                  xor        a6, a6, a3
                  c.addi     s4, 9
                  c.lui      s4, 24
                  auipc      t5, 267098
                  c.srli     a1, 2
                  c.srli     s1, 24
                  c.srli     a5, 25
                  c.addi     t3, 28
                  c.addi     s10, -17
                  auipc      t6, 800865
                  lui        s0, 532183
                  c.addi     a3, 27
                  c.srli     s1, 18
test_done:        
                  li gp, 1
                  ecall
sub_1:            bge        s4, t1, sub_1_stack_p
sub_1_stack_p:    addi       sp, sp, -32
                  sw         ra, 4(sp)
                  c.addi     t1, 4
                  srai       t6, a3, 9
                  sw         t0, 8(sp)
                  auipc      s8, 599512
                  c.addi     a4, 21
                  c.lui      t6, 23
                  c.and      a5, s0
                  mulh       a2, t4, t4
                  c.srli     a0, 26
                  c.addi     t5, 11
                  c.addi     s5, -15
                  c.lui      t6, 28
                  c.addi     s7, -11
                  c.li       a6, 8
                  fence
                  c.addi     a0, -30
                  c.addi     t1, -14
                  c.addi     s4, 21
                  nop
                  c.addi     t4, 29
                  srli       s8, a1, 1
                  c.addi     a6, 24
                  c.srli     s1, 30
                  c.slli     a6, 11
                  auipc      s10, 392995
                  c.slli     a1, 16
                  c.srai     s1, 8
                  c.lui      s7, 8
                  c.addi     a1, 8
                  c.srli     a1, 27
                  c.addi     s4, -20
                  nop
                  lui        s11, 430337
                  c.addi     a5, 14
                  c.xor      a4, a5
                  c.addi     s7, -17
                  lui        t1, 200003
                  remu       s7, zero, a2
                  auipc      s3, 181959
                  c.addi     s10, -25
                  auipc      s6, 58417
                  mulh       t3, s4, t5
                  auipc      s10, 526315
                  c.addi     s9, -31
                  c.srai     a1, 26
                  bltu       t2, s4, 41f
41:               c.lui      a2, 12
                  c.srai     a3, 16
                  c.srai     a3, 22
                  c.addi     s9, 6
                  c.srli     a4, 9
                  c.srli     a0, 7
                  c.addi     a2, 18
                  c.srli     a3, 16
                  c.addi     a0, -1
                  c.or       s1, a1
                  add        a4, gp, t6
                  c.srai     s1, 8
                  c.addi     gp, 7
                  srai       a4, s11, 27
                  c.addi     t4, 10
                  c.addi     a4, -12
                  lui        t3, 557311
                  c.xor      a5, a2
                  auipc      s2, 840535
                  srl        s5, a4, s8
                  srli       s8, t0, 29
                  c.srli     s1, 10
                  c.beqz     a1, 67f
                  ori        a5, s2, 901
                  c.addi     s4, 1
                  c.slli     s2, 19
67:               auipc      a4, 297044
                  c.lui      a2, 12
                  lui        t4, 249957
                  c.lui      s9, 26
                  c.srai     s0, 31
                  c.lui      a1, 14
                  c.and      a1, a5
                  c.slli     a4, 1
                  c.srli     a4, 4
                  c.lui      s4, 4
                  lui        a0, 332598
                  c.add      s0, a4
                  xor        s6, s1, ra
                  lui        s8, 572853
                  auipc      t3, 515534
                  auipc      a2, 8152
                  lw         ra, 4(sp)
                  lw         t0, 8(sp)
                  addi       sp, sp, 32
                  and        zero, s1, s0
95:               ret
sub_3:            bge        a4, s7, sub_3_stack_p
                  c.addi     gp, 8
sub_3_stack_p:    addi       sp, sp, -8
                  sw         ra, 4(sp)
                  sw         t0, 8(sp)
                  c.addi     a1, -22
                  srai       t5, a0, 4
                  c.lui      t2, 27
                  c.li       s7, 30
                  auipc      s9, 101509
                  c.sub      s1, a2
                  auipc      s2, 231216
                  c.addi     s1, 22
                  lui        s1, 575378
                  ori        s10, a3, -15
                  c.lui      s3, 11
                  auipc      t5, 1041768
                  la         t2, data_page_0+1379 #start riscv_load_store_rand_instr_stream_1
                  lb         t6, 1622(t2)
                  sb         a7, 1328(t2)
                  c.addi     a0, -5
                  auipc      s8, 328032
                  and        t5, a4, s5
                  ori        s11, t6, -718
                  c.addi     s4, -6
                  sb         a7, 1990(t2)
                  lb         s4, 1124(t2)
                  c.addi     s0, 3
                  lb         a6, -46(t2)
                  lbu        t1, 935(t2)
                  lh         zero, -1253(t2)
                  sh         s6, 877(t2)
                  lb         s7, -1374(t2)
                  c.srai     a2, 28
                  lb         s3, -1144(t2)
                  lbu        t5, -12(t2)
                  lb         a3, 128(t2)
                  c.addi     s8, -9
                  sw         sp, 1645(t2)
                  lui        t4, 696624
                  sw         ra, 773(t2)
                  sb         s8, -778(t2)
                  lbu        zero, 1627(t2)
                  lbu        a3, -190(t2)
                  lb         a1, -371(t2)
                  lb         s11, -950(t2)
                  lb         s6, 1823(t2)
                  lw         t6, 81(t2)
                  mul        zero, s2, s11
                  sub        gp, s9, s11
                  c.srai     a4, 1
                  c.srai     a4, 24
                  lui        s9, 83037
                  lh         gp, -723(t2)
                  c.lui      s1, 25
                  sh         a5, -1019(t2)
                  lbu        s1, 1033(t2)
                  lb         s9, 1102(t2)
                  lbu        gp, -84(t2)
                  c.addi     a7, -3
                  lb         s1, -77(t2) #end riscv_load_store_rand_instr_stream_1
                  ori        a4, tp, -246
                  blt        a2, a3, j_sub_3_sub_5_6 #branch to jump instr
                  c.andi     s0, -28
                  c.slli     s4, 21
                  c.addi     a6, 8
                  c.srai     a5, 2
                  lui        t4, 951737
                  lui        a6, 820046
                  auipc      s4, 334962
                  lui        s4, 143866
                  add        s0, a1, s1
                  c.srai     a3, 26
j_sub_3_sub_5_6:  jal        ra, sub_5
                  c.srli     s0, 11
                  c.addi     s4, 6
                  c.addi     s7, 8
                  auipc      a5, 645482
                  c.addi     s5, -29
                  sltu       t2, sp, a5
                  divu       a6, t5, s4
                  auipc      s8, 526093
                  c.addi     a5, 19
                  auipc      s7, 381776
                  c.addi     s1, -23
                  bltu       zero, a7, 37f
                  lui        s2, 1004920
                  lui        a2, 48561
                  lui        t4, 633592
                  lui        s6, 732041
                  c.lui      gp, 25
                  c.lui      a0, 9
                  c.addi     s6, 4
                  c.lui      a6, 17
                  auipc      a3, 746543
                  auipc      s2, 656075
                  c.lui      s8, 15
                  c.addi     s11, -22
                  auipc      a1, 155999
                  c.addi     a4, 9
37:               lui        t3, 969968
                  c.srli     s1, 3
                  c.srai     s0, 26
                  c.srli     a2, 6
                  c.lui      t5, 1
                  c.slli     s5, 12
                  lui        s5, 587403
                  auipc      s2, 99719
                  c.addi     a7, 18
                  fence.i
                  c.slli     a0, 14
                  c.addi     a4, 9
                  c.srli     a3, 2
                  c.addi     a5, -20
                  c.or       a3, a2
                  auipc      s10, 72271
                  sra        a5, a0, s10
                  c.addi     s9, 28
                  lui        t6, 901922
                  c.srli     s0, 11
                  c.srli     a3, 4
                  lui        s10, 906039
                  c.srai     a0, 9
                  bltu       zero, s2, 79f
                  lui        a6, 355663
                  c.addi     t3, 24
                  c.addi     a4, 18
                  beq        s0, s9, 70f
                  lui        s0, 831429
                  c.srai     s1, 12
                  auipc      a6, 406575
                  andi       s9, a7, 725
                  c.addi     s3, 28
70:               c.srai     a5, 24
                  lui        s8, 584434
                  c.srai     a3, 13
                  la         a4, data_page_19+1880 #start riscv_load_store_rand_instr_stream_5
                  sh         sp, 1858(a4)
                  lb         a5, 1180(a4)
                  lui        s8, 250105
                  lui        s9, 360161
                  c.addi     s10, 9
                  auipc      zero, 760437
                  c.addi     s6, 3
                  lbu        t5, -27(a4)
                  lbu        s8, 593(a4)
                  c.addi     s10, -3
                  lb         a1, -1467(a4)
                  sb         t1, -283(a4)
                  c.addi     s0, -13
                  lbu        t4, -1215(a4)
                  lb         s11, -1475(a4)
                  slti       s0, t0, 1009
                  lb         a6, 445(a4)
                  sb         s10, -1519(a4)
                  sb         s10, -1325(a4)
                  sh         s0, 176(a4)
                  auipc      s10, 322745
                  lb         a6, 425(a4)
                  sra        s1, gp, a2
                  c.addi     s6, 8
                  lh         a7, 236(a4)
                  lb         a0, -1638(a4)
                  sh         s1, -848(a4)
                  lh         s4, -1154(a4)
                  c.srli     s0, 22
                  lbu        t4, -76(a4)
                  c.srai     s1, 14
                  sb         a1, -265(a4)
                  lui        s5, 2893
                  lui        s10, 551903
                  sb         s6, 1673(a4)
                  sb         s9, -1272(a4) #end riscv_load_store_rand_instr_stream_5
                  sra        gp, gp, a4
                  c.addi     s2, -15
                  c.slli     a3, 11
                  c.addi     s0, 31
                  c.addi     s3, 5
                  auipc      a4, 220373
79:               c.slli     t2, 12
                  c.lui      s2, 31
                  lui        zero, 1012934
                  c.addi     s5, -21
                  c.addi     a6, -22
                  c.li       s3, 17
                  mul        a6, s2, a4
                  c.srli     a1, 3
                  lui        t6, 405270
                  xor        s10, s8, s11
                  auipc      t3, 488855
                  c.addi     s8, 12
                  c.andi     a3, 25
                  c.addi     s7, 6
                  c.addi     s11, -25
                  bne        t0, a6, 97f
                  c.slli     a7, 5
                  c.addi     t3, 17
97:               auipc      t6, 245455
                  c.slli     s2, 26
                  c.lui      a2, 10
                  c.addi     s8, -5
                  c.addi     s7, 6
                  auipc      a2, 43698
                  auipc      t4, 260786
                  c.addi     s7, -20
                  lui        s3, 865718
                  sltu       a4, s5, s9
                  mulhu      s4, s8, t1
                  and        t1, a3, zero
                  auipc      t3, 754564
                  c.addi     a7, -31
                  lui        a1, 281010
                  c.lui      s6, 4
                  lui        a1, 293452
                  c.addi     s2, -10
                  c.slli     a5, 30
                  lui        a1, 556719
                  c.addi     s9, -16
                  c.srli     a0, 12
                  c.addi     s3, -28
                  auipc      t4, 928387
                  c.srli     s1, 8
                  xor        a0, a6, a1
                  c.lui      a1, 5
                  c.sub      a0, a0
                  c.add      a4, a4
                  c.addi     a5, -10
                  bltu       gp, s3, 141f
                  c.addi     a2, -11
                  remu       a5, t1, s9
                  slti       s7, s6, -955
                  slli       s1, t0, 22
                  slt        s8, a3, s5
                  c.li       t5, 10
                  auipc      t5, 874042
                  c.slli     s4, 25
                  c.lui      a1, 19
                  lui        s1, 804289
                  auipc      t4, 725054
                  c.sub      a2, s1
                  lui        t4, 470429
141:              c.addi     t3, 26
                  c.srai     s0, 1
                  c.lui      s2, 14
                  remu       t3, t4, s4
                  c.addi     t1, 17
                  lui        t3, 104081
                  c.addi     t6, 1
                  c.srai     a5, 20
                  c.beqz     a0, 154f
                  or         s6, t4, s0
                  c.lui      a6, 5
                  sra        a1, ra, a5
                  c.addi     a7, -12
154:              c.srai     s0, 24
                  addi       s10, t2, 388
                  bgeu       t4, t6, 171f
                  c.addi     gp, 2
                  la         t4, data_page_15+1572 #start riscv_load_store_rand_instr_stream_6
                  c.lui      s9, 28
                  c.addi     a5, 10
                  fence
                  lhu        s4, 1990(t4)
                  lbu        a5, 546(t4)
                  c.slli     s3, 28
                  lb         t2, 719(t4)
                  lb         s0, -161(t4)
                  sh         t3, -32(t4)
                  lb         t5, -201(t4)
                  auipc      s6, 734144
                  ori        t6, s3, -644
                  lhu        zero, -758(t4)
                  c.and      s1, a5
                  lb         a3, -305(t4)
                  c.lui      a3, 13
                  lui        s5, 918336
                  lb         t5, -513(t4)
                  slli       s9, s0, 20
                  sb         s6, -1009(t4) #end riscv_load_store_rand_instr_stream_6
                  c.addi     s10, -24
                  lui        zero, 287927
                  c.nop
                  bltu       a5, t3, 175f
                  c.addi     s7, -4
                  c.lui      t3, 29
                  lui        a6, 923072
                  c.addi     a4, 25
                  auipc      s3, 328394
                  c.slli     a2, 11
                  c.addi     t4, -29
                  c.sub      a0, a2
                  c.addi     gp, 26
171:              c.srli     a4, 26
                  c.addi     s2, 15
                  c.lui      a6, 21
                  c.bnez     a0, 190f
175:              auipc      a1, 262661
                  la         s5, data_page_13+1761 #start riscv_load_store_rand_instr_stream_3
                  sb         t3, -1544(s5)
                  lbu        a5, -1287(s5)
                  lbu        a7, 1496(s5)
                  lbu        s0, -1474(s5)
                  lb         t5, 533(s5)
                  sb         a1, 390(s5)
                  c.addi     a2, -5
                  lb         t6, -623(s5)
                  c.slli     a7, 19
                  sb         t1, 869(s5)
                  c.slli     s9, 6
                  lhu        gp, -1539(s5)
                  lui        s7, 717549
                  lbu        a5, 850(s5)
                  lb         a7, -70(s5)
                  srai       t4, s3, 11
                  c.addi     a6, -30
                  auipc      t2, 494813
                  lhu        s3, 1943(s5)
                  lh         s1, -823(s5)
                  auipc      a5, 991481
                  or         t6, s1, a4
                  lb         a5, -234(s5)
                  lb         gp, 1514(s5)
                  lb         s1, 889(s5)
                  sh         a5, 1549(s5)
                  sb         a5, -619(s5)
                  lb         s7, 1528(s5)
                  xori       s10, a1, -419
                  sb         a0, -887(s5)
                  c.addi     s6, 7
                  sb         s11, -824(s5)
                  lb         s7, -91(s5) #end riscv_load_store_rand_instr_stream_3
                  c.srli     a5, 23
                  c.srai     s0, 25
                  c.srli     s0, 7
                  c.srli     a2, 24
                  c.addi     s11, -5
                  c.addi     t6, 4
                  c.addi     t2, 22
                  c.addi     t4, 16
                  slti       s6, s10, -273
                  c.addi     gp, -26
                  c.addi     s8, 29
                  auipc      t4, 964108
                  slli       s9, zero, 1
                  lui        a0, 278493
190:              lui        s8, 383759
                  c.srli     a4, 17
                  c.addi     t4, 10
                  auipc      s4, 662058
                  fence
                  c.xor      s1, s0
                  lui        s11, 361583
                  fence.i
                  auipc      a7, 364570
                  auipc      s7, 233272
                  c.lui      t1, 9
                  lui        t5, 672259
                  c.addi     s11, -27
                  c.srai     a0, 7
                  c.addi     gp, -5
                  c.li       t6, -16
                  c.nop
                  auipc      s0, 519828
                  c.and      a3, a2
                  c.addi     t3, -14
                  c.mv       a4, s8
                  c.addi     s3, 25
                  c.addi     a1, 25
                  and        s1, t1, s8
                  c.addi     a3, -13
                  sltu       a3, s8, t4
                  c.slli     gp, 30
                  c.addi     s9, 4
                  c.lui      t3, 4
                  auipc      t1, 739270
                  c.addi     s6, -19
                  c.addi     s1, 20
                  auipc      s3, 731421
                  c.slli     s5, 21
                  lui        gp, 523605
                  lui        a0, 756905
                  c.addi     s8, 13
                  c.lui      t6, 6
                  divu       s10, a7, sp
                  c.srai     a2, 13
                  c.addi     t3, -13
                  c.addi     a1, -17
                  lui        s3, 681602
                  auipc      s8, 329123
                  c.li       s11, 4
                  lui        s1, 771795
                  c.addi     a0, -4
                  c.addi     t2, 22
                  c.srli     a4, 26
                  auipc      s10, 131571
                  la         a1, sub_4
                  c.addi     s1, 18
                  addi       a1, a1, 315
                  auipc      a0, 555967
                  c.and      s0, a0
j_sub_3_sub_4_5:  jalr       ra, a1, -315
                  slt        s7, t3, a4
                  auipc      a7, 775849
                  c.addi     t4, 6
                  bgeu       t3, a4, 240f
                  auipc      t3, 519968
                  c.addi     t2, 11
                  or         s7, a5, a5
240:              c.srai     a2, 17
                  c.slli     t4, 3
                  c.lui      s10, 1
                  lui        a7, 797985
                  c.srli     a2, 30
                  c.srai     a2, 5
                  auipc      t6, 227102
                  c.lui      s2, 31
                  lui        s11, 688608
                  c.addi     s4, -27
                  c.andi     a4, -16
                  lui        a4, 33670
                  c.slli     s7, 18
                  c.addi     a1, 1
                  c.addi     t1, 5
                  lui        s7, 736706
                  c.addi     s7, -29
                  c.srli     a3, 10
                  c.addi     s7, -8
                  c.slli     s7, 30
                  bltu       t0, s10, 264f
                  lui        s1, 232064
                  c.or       a5, a0
                  c.addi     s5, -14
264:              c.lui      t4, 14
                  c.addi     s8, 9
                  c.addi     t5, -3
                  c.srli     s0, 28
                  c.addi     s7, -21
                  lui        a7, 164039
                  c.lui      a0, 12
                  c.srai     a3, 20
                  c.addi     t4, 25
                  c.srai     a1, 27
                  c.srli     s1, 10
                  c.slli     s7, 31
                  c.addi     t6, -20
                  c.slli     a1, 8
                  c.addi     t4, 24
                  slti       s11, s10, 412
                  c.lui      a3, 2
                  c.addi     s10, -10
                  bltu       a7, a6, 287f
                  sltiu      a7, s8, -284
                  lui        s3, 456025
                  mul        t1, t2, a0
                  c.srai     a4, 31
287:              nop
                  c.srli     a5, 22
                  c.addi     t1, -22
                  lui        s4, 322073
                  c.add      s0, s0
                  c.slli     t5, 13
                  mul        s0, a5, a3
                  auipc      s0, 502688
                  auipc      s1, 432453
                  c.srli     a5, 13
                  lui        t5, 296095
                  auipc      a5, 941318
                  bgeu       s10, s0, 306f
                  c.addi     s10, -29
                  lui        s2, 937496
                  auipc      t3, 959272
                  c.addi     t6, 4
                  srli       t5, s0, 29
                  c.addi     s6, 19
306:              auipc      t1, 293799
                  c.addi     a2, 21
                  c.xor      a1, s0
                  lui        s5, 189574
                  auipc      s3, 429591
                  lui        gp, 599774
                  c.and      a4, a2
                  c.slli     a3, 2
                  mul        a5, t1, zero
                  c.srai     a3, 25
                  c.addi     s2, 2
                  c.slli     s1, 6
                  c.addi     s6, 15
                  lui        s10, 311608
                  c.slli     t5, 7
                  and        t5, zero, a4
                  c.addi     s3, -31
                  rem        t6, s4, a2
                  c.lui      s6, 6
                  c.addi     a5, -2
                  c.addi     a2, 14
                  beq        s3, a1, 344f
                  c.addi     s10, 16
                  lui        s9, 389868
                  c.addi     t4, 1
                  c.addi     a2, 23
                  lui        s3, 120087
                  c.mv       a7, a3
                  slt        s0, a2, s1
                  c.xor      s0, s1
                  c.addi     s9, 28
                  lui        t5, 372966
                  lui        gp, 244150
                  c.andi     a4, -6
                  addi       a7, zero, -277
                  c.xor      s1, a0
                  c.srli     a5, 19
                  lui        a4, 332212
344:              c.lui      t3, 14
                  auipc      s10, 148952
                  divu       gp, s10, s5
                  c.addi     s4, 25
                  auipc      a1, 525981
                  add        zero, a1, s3
                  c.addi     a5, -26
                  c.srai     a3, 30
                  bgeu       s1, a6, j_sub_3_sub_5_7 #branch to jump instr
                  c.srai     s1, 16
                  ori        t4, t3, -820
                  c.srli     s0, 14
j_sub_3_sub_5_7:  jal        ra, sub_5
                  c.addi     s9, 9
                  auipc      a2, 106145
                  c.addi     t3, -18
                  slli       s10, s3, 16
                  auipc      a6, 817856
                  auipc      s1, 72706
                  slt        t3, ra, a1
                  lui        s10, 630859
                  c.srli     a3, 22
                  c.addi     a2, -14
                  c.addi     a5, 2
                  bltu       a5, t0, 373f
                  lui        a6, 353448
                  c.srai     a4, 22
                  c.srai     s0, 20
                  c.srli     a2, 4
                  auipc      gp, 555318
                  c.addi     s9, 27
                  xor        a3, sp, s9
                  c.srli     a3, 14
                  c.slli     t6, 5
                  auipc      t1, 38402
                  lui        a2, 182163
                  c.addi     a1, 5
                  c.addi     s3, 15
                  bltu       a6, t0, 385f
373:              c.srli     a3, 6
                  c.addi     s0, 4
                  c.lui      s11, 8
                  c.addi     t4, -1
                  andi       a3, a5, 929
                  mulhsu     gp, s2, s4
                  c.addi     s3, 28
                  lui        s1, 307114
                  c.addi     a7, 15
                  c.addi     s7, 4
                  auipc      zero, 5983
                  lui        s11, 862047
385:              c.srai     a4, 22
                  c.addi     s5, 11
                  lui        t1, 456943
                  c.lui      a5, 3
                  div        t3, t4, s6
                  lui        s3, 814637
                  c.lui      a5, 23
                  sltu       t6, s0, t4
                  lui        gp, 673130
                  c.slli     s3, 28
                  c.srli     a5, 4
                  la         t3, data_page_19+1583 #start riscv_load_store_rand_instr_stream_4
                  c.srli     a3, 29
                  lb         s2, 1914(t3)
                  c.srli     a4, 26
                  c.srai     a1, 27
                  lb         t2, -924(t3)
                  sb         a7, -1060(t3)
                  lb         t4, 1179(t3)
                  lb         s11, 616(t3)
                  lui        t6, 333627
                  c.addi     a3, 28
                  mul        a1, t2, a1
                  lbu        a0, 1264(t3)
                  auipc      a0, 3046
                  lw         s11, 1169(t3)
                  lbu        t4, 876(t3)
                  c.slli     t6, 22
                  c.srai     s1, 10
                  lbu        t2, 1047(t3)
                  or         s6, a0, s5
                  sb         gp, 36(t3)
                  lhu        s1, 1471(t3)
                  lbu        a7, 1196(t3)
                  c.andi     a5, -11
                  sub        t6, a1, a0
                  and        t5, s11, a1
                  lhu        t5, -875(t3) #end riscv_load_store_rand_instr_stream_4
                  slt        a5, a4, a5
                  lui        s8, 642772
                  c.addi     s2, -15
                  auipc      s8, 133081
                  c.sub      a4, a2
                  c.addi     s6, -18
                  auipc      a4, 167112
                  c.nop
                  c.lui      s2, 27
                  lui        a1, 716408
                  c.srai     a0, 19
                  c.addi     a5, 31
                  auipc      a5, 129719
                  c.add      a5, a5
                  c.addi     s6, -2
                  slti       s3, tp, -569
                  bge        t4, zero, 415f
                  auipc      t4, 373355
                  c.srai     a3, 1
415:              c.and      s1, s0
                  auipc      s3, 1008224
                  auipc      s10, 371102
                  c.srai     s0, 12
                  lui        a6, 16284
                  nop
                  sltiu      t4, s2, -501
                  c.addi     s1, -29
                  sltu       a6, t1, t6
                  c.addi     s9, 5
                  lui        s8, 87848
                  auipc      gp, 782480
                  c.lui      s2, 13
                  c.addi     gp, 22
                  c.slli     s7, 5
                  mulh       a5, s7, s9
                  c.addi     a0, 19
                  bge        s6, sp, 447f
                  c.addi     s6, -18
                  c.srai     a3, 6
                  lui        a6, 625541
                  c.addi     a2, -18
                  c.slli     t3, 18
                  c.srli     s1, 21
                  sra        a3, s5, zero
                  c.addi     s1, 22
                  c.addi     a2, -3
                  lui        a5, 489344
                  auipc      t4, 561433
                  c.addi     s11, 16
                  sub        s9, t1, t5
                  c.addi     a4, 19
447:              c.addi     s5, -5
                  c.addi     s1, -26
                  c.addi     a4, 30
                  lui        a1, 412691
                  c.slli     t4, 24
                  lui        zero, 512415
                  sltu       a6, ra, a6
                  mulhu      s0, sp, t1
                  c.addi     a4, 4
                  lui        t1, 1019163
                  c.addi     a5, 1
                  c.slli     a1, 12
                  c.srai     a4, 5
                  c.addi     a5, -11
                  andi       t6, a7, -243
                  c.addi     s1, 18
                  auipc      a7, 147155
                  lui        s5, 454912
                  c.slli     t1, 10
                  c.srai     a0, 26
                  c.slli     s0, 25
                  auipc      t2, 566273
                  c.lui      a4, 26
                  slti       s5, s11, 296
                  c.slli     s3, 10
                  auipc      gp, 217267
                  c.srai     s1, 28
                  lui        s6, 61789
                  c.srli     a3, 1
                  srli       t1, s0, 27
                  c.srai     s1, 19
                  lui        t3, 191696
                  c.addi     t5, 4
                  lui        a3, 331330
                  bge        t3, a7, 496f
                  c.addi     t3, -7
                  c.addi     t3, -8
                  add        t4, zero, s7
                  lui        s10, 285355
                  c.addi     s7, -23
                  c.srai     a5, 13
                  auipc      s1, 735056
                  lui        a5, 461008
                  c.lui      a1, 10
                  c.xor      a5, a4
                  auipc      t4, 801316
                  auipc      t4, 814477
                  c.slli     s7, 16
                  c.addi     t5, -16
496:              c.addi     a6, -8
                  c.srai     s1, 5
                  c.addi     s11, -13
                  c.slli     t3, 18
                  c.addi     a6, 14
                  c.addi     t5, -28
                  c.mv       s7, a2
                  c.srli     a5, 17
                  remu       t3, gp, s10
                  c.addi     a1, -6
                  c.srai     a5, 24
                  c.srai     s1, 18
                  c.lui      t6, 16
                  auipc      s2, 367622
                  c.srai     a5, 8
                  and        t2, a7, s11
                  c.slli     s8, 27
                  c.mv       a7, gp
                  auipc      s10, 1040772
                  c.addi     t6, -28
                  c.addi     t5, -18
                  auipc      t6, 742965
                  srli       s5, s0, 8
                  c.addi     s0, -14
                  c.addi     t5, 14
                  c.addi     t6, 18
                  c.srli     a2, 11
                  c.sub      a0, a0
                  sltiu      t3, s1, -556
                  lui        zero, 300560
                  c.slli     t3, 17
                  la         t3, data_page_8+1564 #start riscv_load_store_rand_instr_stream_0
                  c.slli     s8, 25
                  c.addi     s3, -17
                  c.addi     s10, -13
                  slli       s0, t2, 1
                  sb         zero, 823(t3)
                  lb         a5, -1399(t3)
                  xor        zero, a2, s9
                  addi       a2, s10, 96
                  c.srai     a4, 11
                  sh         t1, -1214(t3)
                  lb         a6, 1505(t3)
                  lb         s8, -1339(t3)
                  c.srli     a2, 21
                  lui        a7, 935374
                  sw         s4, 268(t3)
                  auipc      zero, 725819
                  lb         s7, 222(t3)
                  c.addi     s10, 9
                  sb         a5, 623(t3)
                  lh         a2, 96(t3)
                  c.srli     a2, 7
                  c.xor      a3, a0
                  lui        t6, 513208
                  lh         a4, -906(t3)
                  lhu        s3, 1648(t3)
                  auipc      t6, 54593
                  lb         a5, -1229(t3)
                  lhu        s4, 1784(t3)
                  lbu        t6, 1483(t3)
                  c.slli     s9, 6
                  sb         ra, 1991(t3)
                  sb         s7, 1280(t3)
                  lbu        s6, 268(t3)
                  mulh       t4, t4, a0
                  lb         s6, 1241(t3)
                  slli       s8, gp, 4
                  lui        t2, 794686
                  lhu        t2, -130(t3)
                  c.addi     gp, 2
                  lb         a7, -413(t3)
                  lbu        s10, 1570(t3)
                  sb         t5, -211(t3)
                  lbu        a3, 1757(t3)
                  lui        zero, 713784
                  lbu        t1, 1289(t3)
                  c.lui      s5, 30
                  lw         a3, -332(t3)
                  xori       s1, gp, -291
                  lbu        s4, 1945(t3) #end riscv_load_store_rand_instr_stream_0
                  c.addi     s0, -1
                  c.srai     s1, 28
                  c.addi     t5, 26
                  lui        a4, 113149
                  auipc      t2, 1004973
                  c.addi     a0, 20
                  c.and      s1, a0
                  c.addi     t6, 22
                  auipc      t1, 386324
                  srl        a4, s2, t6
                  c.addi     t1, -29
                  c.addi     s0, -10
                  c.addi     s7, -1
                  c.mv       a6, a2
                  ori        s2, t2, -84
                  blt        a2, t4, 557f
                  auipc      s5, 343868
                  rem        s3, a0, ra
                  c.srli     s0, 22
                  c.slli     s3, 6
                  c.addi     t2, 3
                  slt        s1, t6, s11
                  auipc      s5, 474997
                  auipc      a1, 793680
                  c.addi     s9, 31
                  c.addi     t4, 23
                  srli       s3, s5, 27
                  c.addi     a5, 3
                  c.addi     s0, -18
                  c.slli     s5, 16
557:              bltu       s1, s5, 560f
                  c.addi     t3, 18
                  c.addi     t2, -17
560:              c.sub      s1, s1
                  fence
                  auipc      a7, 373758
                  c.slli     t4, 26
                  auipc      t3, 393135
                  srli       a3, s10, 22
                  sll        s1, a1, s5
                  c.xor      a0, s1
                  c.srli     a2, 6
                  c.lui      t4, 16
                  srli       s0, s4, 18
                  slli       a1, a7, 23
                  c.addi     gp, 11
                  auipc      s2, 546700
                  sra        a0, t4, s11
                  auipc      s4, 973706
                  c.srli     s1, 2
                  lui        a0, 220242
                  c.addi     s0, -15
                  beq        a7, t1, 599f
                  auipc      s10, 797465
                  auipc      s11, 45570
                  mulhsu     s11, s9, s4
                  auipc      s5, 426877
                  sltu       s5, gp, a6
                  c.lui      s7, 2
                  c.addi     a0, -31
                  auipc      a4, 896143
                  c.slli     s6, 3
                  c.srai     s1, 12
                  sra        gp, s10, s2
                  c.slli     s0, 12
                  auipc      s0, 329959
                  sltiu      s8, ra, -513
                  c.srai     a4, 24
                  c.lui      s1, 8
                  srli       s5, s0, 2
                  c.srli     a3, 28
                  auipc      gp, 303955
599:              xor        t1, s0, a7
                  c.slli     t1, 5
                  c.lui      t4, 9
                  c.addi     a7, 16
                  sll        s3, s10, a4
                  beq        t4, t5, 619f
                  ori        s6, s2, 434
                  slt        s10, t3, t0
                  c.srai     a2, 13
                  slt        s9, tp, a2
                  auipc      t5, 867259
                  c.slli     a1, 8
                  c.lui      a6, 13
                  c.slli     s5, 18
                  slti       s7, s9, -321
                  c.addi     s4, -24
                  c.slli     a1, 26
                  auipc      t3, 731496
                  lui        s0, 273146
                  c.slli     t2, 14
619:              c.sub      a5, a5
                  slti       s2, s11, -402
                  bge        s7, t1, 626f
                  c.lui      s6, 14
                  c.addi     s4, -22
                  la         gp, data_page_10+2057 #start riscv_load_store_rand_instr_stream_2
                  c.xor      s0, s0
                  auipc      a4, 664178
                  lb         zero, -791(gp)
                  mulhu      s6, s4, a0
                  c.addi     a2, 26
                  lbu        s10, -1906(gp)
                  lb         s4, -158(gp)
                  c.srai     a5, 3
                  sltu       a1, t6, s1
                  c.lui      a2, 30
                  c.addi     s9, -21
                  sh         a7, -1985(gp)
                  sb         a6, 1866(gp)
                  c.addi     s7, 20
                  lhu        a5, -963(gp)
                  sb         s6, -478(gp)
                  auipc      s0, 322921
                  lbu        a3, -1450(gp)
                  lb         a0, 346(gp)
                  c.addi     s7, -18
                  lbu        s7, 1940(gp)
                  lbu        t2, 1470(gp)
                  c.addi     a3, 13
                  divu       t3, a1, a5
                  sh         s9, -1215(gp)
                  lb         s1, 520(gp)
                  lb         a4, -24(gp)
                  lb         t5, -978(gp)
                  lb         a4, -1380(gp)
                  auipc      s10, 612374
                  lb         s8, 956(gp)
                  c.addi     t4, -10
                  lbu        zero, 275(gp)
                  c.addi     s1, 23
                  sb         s4, 1887(gp)
                  lbu        s6, 356(gp)
                  slti       a6, a0, -201
                  srl        t2, s8, t3
                  c.srli     s0, 16
                  c.lui      s0, 21
                  c.lui      t6, 12
                  lui        zero, 327133
                  and        a3, t4, a1
                  c.srai     a2, 17
                  lbu        zero, -324(gp)
                  c.addi     s2, -31
                  lbu        s4, -1456(gp)
                  c.lui      s2, 24
                  sb         t3, 1500(gp)
                  c.addi     s3, 6
                  rem        a7, a1, s7
                  lhu        s8, 991(gp)
                  c.addi     s0, 15
                  xori       zero, a7, 899
                  lb         a0, -1370(gp)
                  lbu        t5, -1922(gp)
                  sb         a5, -1128(gp)
                  lbu        s3, 1755(gp) #end riscv_load_store_rand_instr_stream_2
                  auipc      a6, 1031447
                  c.addi     s1, 10
626:              lui        a7, 727377
                  lui        a5, 831510
                  c.xor      s0, a0
                  c.addi     a0, 4
                  c.srli     a0, 2
                  c.mv       a2, s9
                  lui        a0, 625227
                  c.slli     s7, 20
                  lui        s2, 1036134
                  bgeu       t1, t4, 638f
                  c.srai     a3, 29
                  c.addi     t2, -22
638:              auipc      a2, 1009391
                  c.slli     s8, 12
                  auipc      s6, 1016218
                  auipc      t5, 863999
                  c.slli     a5, 4
                  c.lui      a0, 15
                  c.srai     a1, 23
                  c.or       a2, a4
                  c.addi     t2, -11
                  c.addi     a5, 23
                  c.addi     gp, 21
                  c.addi     a4, 14
                  slti       a6, t3, 870
                  c.addi     a7, -15
                  c.lui      a6, 20
                  sltiu      t2, t0, -448
                  c.addi     t1, 9
                  divu       s11, s11, a1
                  bltu       t4, t1, 662f
                  lui        t2, 43998
                  c.slli     a7, 15
                  c.srli     s0, 4
                  c.slli     a1, 17
                  auipc      t2, 607634
662:              c.srai     a0, 15
                  lui        s2, 678585
                  c.srai     a2, 21
                  c.slli     a0, 31
                  lui        s10, 353964
                  c.addi     a4, -20
                  c.addi     a4, -18
                  auipc      t3, 480520
                  c.or       a1, a4
                  c.addi     t6, 10
                  c.addi     a3, 13
                  c.slli     s6, 27
                  c.slli     s11, 13
                  c.srli     a2, 28
                  nop
                  c.andi     a2, 10
                  c.addi     t1, 14
                  c.addi     t3, -5
                  mul        t2, s1, sp
                  mulhsu     a7, s5, t0
                  lui        zero, 93029
                  lui        a3, 968242
                  auipc      s9, 943104
                  auipc      t2, 226656
                  lui        s3, 1040578
                  lui        t2, 677108
                  lui        a5, 207614
                  c.slli     a3, 19
                  c.srli     a2, 30
                  xori       a2, s11, -323
                  c.addi     a6, 23
                  ori        t6, s11, -22
                  c.addi     a6, -29
                  sra        s10, a2, a6
                  c.srai     a0, 13
                  auipc      t2, 700284
                  c.addi     a2, -10
                  c.lui      s1, 12
                  auipc      a5, 672877
                  lui        t6, 49380
                  c.addi     a0, -8
                  c.srai     a0, 2
                  c.mv       a7, s6
                  mulh       a5, s7, a5
                  lui        s10, 184018
                  c.addi     s3, -9
                  lui        t2, 953562
                  c.addi     t1, -22
                  c.lui      gp, 15
                  rem        s7, a7, a4
                  auipc      s6, 216542
                  lui        s5, 72950
                  sltu       s3, s3, sp
                  lui        s3, 43960
                  auipc      zero, 649148
                  c.lui      s6, 9
                  c.addi     s5, -30
                  lui        zero, 179333
                  fence
                  auipc      t5, 660296
                  bne        zero, a5, 726f
                  c.addi     a5, 22
                  c.addi     a6, -1
                  lui        s3, 615047
726:              c.srai     a3, 16
                  lui        t6, 603049
                  c.addi     t4, -21
                  c.addi     s1, 25
                  c.srli     a4, 8
                  c.addi     a4, -3
                  c.slli     s2, 20
                  c.addi     t5, -23
                  divu       s8, s7, s3
                  auipc      s4, 129635
                  auipc      t1, 796248
                  sra        t2, s7, a6
                  fence.i
                  c.srli     a4, 9
                  c.lui      s0, 10
                  c.beqz     a0, 742f
742:              lui        s9, 733657
                  auipc      s9, 116464
                  lui        s8, 857005
                  c.slli     s4, 7
                  c.srai     a4, 24
                  lw         ra, 4(sp)
                  c.addi     t2, -10
                  lw         t0, 8(sp)
                  auipc      t5, 887765
                  addi       sp, sp, 8
                  c.slli     s11, 6
                  lui        a6, 52278
                  c.addi     t2, 12
                  c.srli     s0, 10
1070:             ret
sub_4:            blt        t0, s2, sub_4_stack_p
                  lui        s9, 1003359
                  c.addi     s2, -30
sub_4_stack_p:    addi       sp, sp, -12
                  sw         ra, 4(sp)
                  c.addi     s0, -27
                  sw         t0, 8(sp)
                  c.andi     a4, 18
                  mulhsu     t3, s0, s7
                  lui        s6, 869071
                  addi       t1, s10, -280
                  c.slli     s3, 15
                  c.addi     a4, -1
                  or         zero, s2, a3
                  c.addi     s0, -2
                  lui        t4, 786330
                  mul        a1, t3, a4
                  bne        s3, s4, 22f
                  lui        a2, 141835
                  c.slli     a0, 8
                  c.addi     gp, 7
                  sra        s8, t4, s5
                  c.addi     t3, 22
                  c.addi     s5, -12
                  xori       s8, s0, -170
                  c.addi     a5, -20
                  c.addi     a4, 24
                  fence.i
                  c.addi     t4, 5
                  c.srai     a2, 19
22:               c.addi     t5, -5
                  bge        t3, zero, 37f
                  ori        zero, t1, -500
                  c.addi     t4, -11
                  c.addi     t4, -14
                  mulhu      t4, s1, zero
                  c.srai     a2, 25
                  c.addi     s7, 30
                  auipc      a2, 862859
                  c.addi     a3, 12
                  and        a5, s8, gp
                  c.addi     a2, 14
                  c.addi     s5, 8
                  c.addi     s5, -25
                  lui        t3, 909957
37:               bge        s9, s0, 51f
                  c.addi     a2, -3
                  c.addi     t2, 20
                  c.addi     t5, 5
                  c.addi     a4, -7
                  c.addi     a3, -3
                  auipc      a3, 633683
                  c.addi     a5, 13
                  lui        s10, 739741
                  c.addi     a1, -26
                  and        s11, a4, a7
                  srl        a7, s7, ra
                  c.slli     s4, 9
                  c.addi     t3, -15
51:               lui        s6, 335992
                  lui        a7, 283967
                  lui        s1, 383868
                  c.srai     a4, 7
                  c.slli     s1, 25
                  c.addi     t2, -30
                  c.srai     a4, 3
                  div        s1, sp, a5
                  c.addi     t3, -16
                  auipc      t2, 332004
                  c.srli     a2, 6
                  divu       a5, s6, s4
                  c.srai     a5, 26
                  auipc      t2, 392645
                  ori        t3, a5, 387
                  lui        zero, 583380
                  c.addi     s11, 27
                  divu       a7, a4, s4
                  auipc      s1, 510298
                  c.addi     s5, -27
                  c.addi     a2, 30
                  lui        a7, 130859
                  lui        a2, 853013
                  lui        gp, 689685
                  c.lui      a3, 16
                  c.slli     s6, 1
                  c.addi     a3, -13
                  c.lui      s4, 20
                  srai       s4, s1, 27
                  bgeu       t2, t2, 95f
                  c.addi     s4, -5
                  auipc      s11, 474474
                  c.lui      s8, 12
                  lui        a4, 567697
                  divu       t3, ra, s4
                  rem        gp, s6, s6
                  c.andi     s1, -12
                  blt        s8, s0, 103f
                  c.lui      s6, 18
                  lui        t5, 80039
                  c.slli     s5, 19
                  fence
                  fence.i
                  c.xor      a3, s0
95:               c.lui      s11, 9
                  c.srai     a1, 2
                  auipc      zero, 967291
                  lui        a4, 882532
                  auipc      s5, 827466
                  c.srai     a0, 10
                  c.lui      a2, 27
                  sltiu      s1, s10, 172
103:              c.srli     a0, 2
                  c.srli     a1, 9
                  lui        s9, 119899
                  c.srli     a4, 1
                  xor        s1, s11, s0
                  c.slli     t1, 29
                  lui        a7, 715840
                  c.srli     a5, 16
                  auipc      a4, 952235
                  auipc      a6, 433720
                  lui        t5, 471272
                  c.lui      s7, 29
                  c.bnez     a2, 123f
                  c.addi     s11, -26
                  c.addi     a3, -23
                  c.addi     a0, -2
                  andi       t1, tp, -261
                  divu       s3, a5, a5
                  fence
                  c.addi     s2, -31
123:              c.addi     s2, 8
                  c.addi     s7, 8
                  c.srli     s0, 19
                  c.srai     a2, 9
                  auipc      s5, 105190
                  divu       s7, a5, s9
                  lui        a2, 640192
                  c.addi     a3, 17
                  auipc      a7, 593147
                  lui        t4, 675580
                  lui        s6, 897409
                  c.srai     a3, 23
                  c.addi     a6, 23
                  lui        t4, 229395
                  c.andi     a3, 9
                  c.srai     a1, 26
                  c.srli     a0, 13
                  auipc      a7, 727283
                  c.srai     s1, 2
                  mulhu      s1, s6, ra
                  c.lui      s2, 10
                  c.addi     t1, 6
                  c.addi     t6, -17
                  lui        a6, 161595
                  fence
                  c.addi     t2, -7
                  lui        t2, 315581
                  c.slli     s11, 5
                  auipc      zero, 737983
                  lui        t1, 417967
                  c.addi     a6, -13
                  c.lui      a0, 31
                  auipc      s7, 219164
                  c.addi     a5, -30
                  c.slli     s5, 17
                  nop
                  c.addi     a0, 13
                  c.addi     s7, 30
                  divu       a5, a5, s5
                  nop
                  c.addi     s8, -12
                  c.addi     s6, 13
                  auipc      s2, 365609
                  c.addi     s2, 6
                  c.addi     a0, -26
                  lui        s11, 704705
                  c.addi     s2, 10
                  lui        t1, 628287
                  sra        a6, t1, s5
                  srl        s8, s2, s6
                  srl        a7, t2, t1
                  auipc      s1, 741630
                  slti       s9, s7, -360
                  c.addi     a7, 3
                  mul        a5, s7, s8
                  remu       s10, s4, tp
                  c.lui      a7, 7
                  c.srai     s0, 22
                  c.addi     a4, 4
                  c.addi     t4, 24
                  c.addi     a7, 23
                  c.slli     s1, 29
                  c.addi     t4, -5
                  c.addi     s7, -23
                  c.addi     t1, -29
                  auipc      s8, 459137
                  lui        s11, 263425
                  c.srai     a2, 31
                  c.addi     s11, -7
                  lui        t3, 502942
                  lui        s2, 962844
                  beq        a5, t1, 195f
195:              c.mv       a1, s11
                  ori        s11, s11, -622
                  c.lui      a6, 17
                  lui        a5, 475373
                  nop
                  c.slli     t1, 30
                  sltu       t4, a6, s0
                  sub        s3, s10, zero
                  c.addi     s3, 19
                  c.slli     s6, 21
                  c.add      a4, a1
                  lui        s11, 858139
                  lui        a5, 75817
                  c.srli     s0, 14
                  mul        a0, t1, a7
                  remu       zero, a2, a0
                  c.srli     a2, 22
                  bge        s9, s11, 222f
                  c.addi     a1, -17
                  sltiu      s1, t6, 62
                  c.srli     a4, 29
                  c.addi     s0, 20
                  c.srai     a4, 31
                  nop
                  c.and      a5, a0
                  c.srai     a3, 2
                  c.addi     s9, 7
222:              auipc      a5, 446636
                  c.srai     s1, 25
                  c.srai     a1, 24
                  c.addi     gp, -24
                  sub        s5, t0, s4
                  lui        s7, 418689
                  c.addi     t1, -32
                  srai       gp, s11, 6
                  c.addi     s6, -14
                  bgeu       gp, a6, 232f
232:              lui        s1, 382145
                  c.addi     s10, 7
                  c.lui      s4, 31
                  sra        t4, a1, tp
                  c.or       a1, a3
                  auipc      t4, 363029
                  c.srai     a1, 23
                  c.addi     s4, -9
                  c.addi     a3, 3
                  c.lui      s9, 15
                  beq        t1, t0, 250f
                  add        t6, t2, a6
                  beq        a1, t4, 262f
                  c.srli     s1, 6
                  c.lui      gp, 28
                  la         t3, data_page_18+1722 #start riscv_load_store_rand_instr_stream_5
                  c.add      a1, a0
                  sb         sp, 119(t3)
                  c.srai     a4, 21
                  c.slli     gp, 13
                  lui        t2, 291962
                  sb         s5, -947(t3)
                  c.addi     s5, 14
                  lhu        t5, 1740(t3)
                  sh         t3, 616(t3)
                  lui        a5, 489599
                  lb         s10, -1043(t3)
                  c.addi     a0, 29
                  lbu        s0, -599(t3)
                  lbu        t6, -247(t3)
                  lw         s4, 674(t3)
                  c.addi     a4, -4
                  lhu        s7, 1662(t3)
                  lb         s8, 1891(t3)
                  auipc      t5, 91677
                  lhu        a0, -1642(t3)
                  lb         gp, 927(t3)
                  auipc      a6, 746671
                  sltiu      s11, s3, -951
                  lbu        s9, -387(t3)
                  lb         s3, -1285(t3)
                  mulhu      t5, s5, s5
                  c.slli     a0, 7
                  c.xor      s1, s1
                  lb         t5, -407(t3)
                  c.srai     s0, 23
                  lui        a7, 885291
                  mul        a7, t5, s6
                  lbu        t5, -821(t3)
                  c.lui      a5, 20
                  lui        t4, 151297
                  c.srai     a4, 13
                  and        s9, sp, t4
                  c.srli     a0, 7
                  c.lui      a2, 16
                  c.slli     a3, 10
                  c.addi     t6, 29
                  andi       s10, s4, -41
                  sh         s1, -1076(t3)
                  c.lui      s2, 12
                  lui        t2, 955927
                  lui        s3, 294016
                  lbu        s11, 740(t3)
                  lb         s0, 179(t3)
                  lb         s0, 1966(t3) #end riscv_load_store_rand_instr_stream_5
                  sltiu      a4, t5, -39
                  c.srai     a2, 16
                  c.addi     s11, -1
250:              lui        t2, 432808
                  beq        s6, s3, 267f
                  c.slli     a3, 19
                  auipc      gp, 113656
                  lui        s1, 130430
                  c.srai     a3, 19
                  c.addi     gp, 20
                  c.addi     t1, -17
                  c.srai     a1, 3
                  ori        t4, s9, 837
                  c.srli     a1, 15
                  c.addi     s6, -27
262:              lui        a6, 519567
                  c.slli     s6, 3
                  xori       s8, s3, -87
                  c.srai     s0, 18
                  c.lui      s9, 29
267:              lui        gp, 724988
                  c.srli     a2, 31
                  andi       a0, s9, -298
                  mulhsu     s6, a7, a4
                  auipc      a6, 1005681
                  c.addi     s8, 5
                  c.addi     s6, -16
                  c.srli     a0, 13
                  lui        s2, 463491
                  lui        t1, 1034333
                  auipc      s2, 362489
                  c.srli     a0, 29
                  auipc      gp, 754792
                  sub        t6, t2, a3
                  auipc      t3, 701162
                  c.and      s1, a2
                  xor        s7, s3, s3
                  c.srai     a0, 28
                  c.xor      a1, a5
                  c.addi     a3, 11
                  c.sub      a4, a2
                  auipc      zero, 803641
                  auipc      a6, 461791
                  c.addi     a7, 14
                  c.addi     t1, 13
                  c.addi     a1, -15
                  c.lui      t2, 15
                  c.lui      gp, 10
                  mul        a0, t6, a2
                  auipc      s10, 639140
                  c.beqz     a0, 301f
                  c.srai     a1, 7
                  sltu       s9, s3, a6
                  lui        s11, 67310
301:              lui        s4, 817080
                  lui        a1, 390754
                  c.slli     s7, 25
                  bgeu       tp, s8, 312f
                  c.addi     s3, 14
                  c.addi     t3, 22
                  c.lui      t5, 9
                  c.addi     s1, -17
                  mulhu      s8, a0, s7
                  c.slli     t4, 12
                  c.srli     a4, 14
312:              sltu       a6, a5, s4
                  c.addi     s1, 16
                  auipc      t6, 78105
                  c.addi     s0, 16
                  c.addi     t1, -15
                  fence
                  lui        s10, 279619
                  c.srai     a2, 13
                  c.lui      s7, 21
                  c.srli     s1, 18
                  c.srli     s1, 16
                  c.addi     a3, -5
                  auipc      s7, 785024
                  add        t2, s4, a2
                  c.addi     s3, -5
                  c.addi     s0, -3
                  srl        t4, s9, a5
                  c.addi     a0, -22
                  c.addi     a7, 25
                  srl        s4, sp, a0
                  c.addi     a4, -26
                  add        a0, s6, t6
                  fence
                  lui        a5, 545023
                  lui        a6, 228307
                  lui        s4, 196452
                  addi       s2, s2, 290
                  c.srai     a0, 11
                  c.srai     s0, 7
                  ori        s7, s0, -471
                  mulh       s0, s11, t5
                  auipc      t2, 21876
                  lui        s9, 550489
                  c.addi     s9, -24
                  c.addi     s9, -6
                  div        a2, t0, s10
                  c.addi     s7, -23
                  c.addi     t5, 12
                  lui        zero, 372433
                  bgeu       s1, tp, 365f
                  c.li       a4, -17
                  c.slli     a3, 5
                  c.addi     s9, 27
                  c.addi     s11, -21
                  c.addi     a1, -11
                  lui        s8, 469798
                  fence
                  c.lui      s3, 13
                  lui        s4, 50781
                  c.addi     t5, -23
                  auipc      s5, 676469
                  mulhu      a2, s4, t3
                  c.beqz     a1, 380f
365:              c.srai     s0, 18
                  lui        s7, 296428
                  nop
                  auipc      s2, 88947
                  auipc      t1, 850417
                  lui        a6, 422862
                  c.addi     t4, 30
                  c.addi     t2, 16
                  lui        s1, 917071
                  c.addi     s11, 5
                  c.lui      s0, 13
                  c.srai     a4, 28
                  auipc      t3, 429069
                  c.slli     a7, 30
                  la         a1, data_page_16+2685 #start riscv_load_store_rand_instr_stream_0
                  slti       a0, s7, 862
                  c.addi     s4, -30
                  lb         a6, 313(a1)
                  c.srli     a0, 5
                  sh         s3, 993(a1)
                  lhu        a5, 693(a1)
                  fence
                  lbu        s11, 1386(a1)
                  lbu        t3, 1198(a1)
                  rem        t1, s1, zero
                  lb         s6, -358(a1)
                  sb         t6, -854(a1)
                  lhu        s6, -1081(a1)
                  sw         s6, 167(a1)
                  c.srai     a5, 26
                  lb         s9, -1924(a1)
                  lbu        s7, -370(a1)
                  lbu        t4, -411(a1)
                  c.slli     a0, 25
                  lbu        t2, -626(a1)
                  sb         t5, -310(a1)
                  lbu        zero, -1392(a1)
                  c.slli     a3, 9
                  auipc      s11, 657471
                  srai       t1, a0, 30
                  divu       t3, s9, tp
                  auipc      a3, 536494
                  lui        zero, 481417
                  c.slli     s8, 7
                  c.addi     a7, 19
                  sb         t6, 1052(a1)
                  lh         s7, -1055(a1)
                  c.addi     s0, 25
                  lb         a2, 524(a1)
                  c.srli     a2, 30
                  lhu        t3, 93(a1) #end riscv_load_store_rand_instr_stream_0
                  c.addi     a4, 5
380:              bgeu       a1, t3, 389f
                  c.addi     t5, -1
                  c.lui      s7, 23
                  add        a0, t0, a2
                  c.addi     s7, -22
                  bgeu       s3, ra, 397f
                  c.srai     a3, 4
                  lui        t3, 16927
                  auipc      t6, 983309
389:              c.or       a0, a0
                  c.lui      t2, 10
                  lui        t2, 647244
                  c.slli     gp, 26
                  c.slli     gp, 19
                  mulh       t3, a3, t3
                  or         t2, s9, t6
                  xor        s7, s1, s2
397:              c.lui      t4, 28
                  c.slli     a1, 13
                  remu       s8, a1, ra
                  rem        a4, t4, s1
                  c.andi     s0, 11
                  auipc      s2, 229898
                  ori        t2, s1, 711
                  c.addi     a5, -6
                  auipc      s8, 909537
                  srli       s6, a6, 27
                  c.lui      a0, 5
                  auipc      t5, 340650
                  c.addi     a5, -29
                  lui        t3, 711905
                  auipc      s0, 361591
                  lui        t6, 484083
                  lui        s8, 208235
                  c.addi     s3, -1
                  c.slli     a4, 11
                  lui        a6, 120297
                  c.addi     s11, -16
                  lui        s10, 53779
                  c.addi     s4, -10
                  div        s4, s8, a2
                  sub        t4, s8, s1
                  c.lui      gp, 30
                  lui        s0, 807970
                  c.add      a4, s0
                  c.srli     a2, 25
                  lui        s3, 347440
                  c.addi     s8, -3
                  divu       s10, a7, a0
                  c.addi     t1, -15
                  c.addi     s2, -1
                  c.addi     s8, -22
                  c.addi     t3, 25
                  xori       t1, ra, 444
                  c.addi     s1, 18
                  blt        a2, s1, 438f
                  c.sub      a2, a0
                  lui        s7, 401662
438:              c.lui      a4, 26
                  add        s0, t1, a3
                  remu       t1, t2, a5
                  c.bnez     a4, 449f
                  c.srli     a4, 18
                  sltiu      t5, t2, -521
                  c.mv       t2, s10
                  c.addi     s3, 9
                  c.addi     s8, -7
                  c.addi     s5, -11
                  rem        s1, t3, gp
449:              c.lui      a1, 6
                  lui        t4, 7983
                  srai       a4, sp, 0
                  la         s3, data_page_14+1564 #start riscv_load_store_rand_instr_stream_7
                  mulh       s4, a6, s5
                  lb         a7, -315(s3)
                  sw         sp, 1740(s3)
                  c.add      a4, a0
                  sh         s10, -1262(s3)
                  lb         gp, 86(s3)
                  c.addi     t3, 22
                  lb         s4, 1301(s3)
                  c.slli     a6, 25
                  sw         s7, 232(s3)
                  c.addi     a3, -27
                  c.addi     s5, -5
                  lbu        s8, -509(s3)
                  c.addi     s8, 21
                  c.or       s1, a3
                  c.slli     a1, 31
                  lh         s0, -830(s3)
                  lb         s2, 745(s3)
                  sh         a0, -550(s3)
                  lhu        s5, 84(s3)
                  c.addi     a6, 19
                  c.srli     a4, 27
                  lbu        a4, -871(s3)
                  lui        a0, 124024
                  lbu        a5, 1439(s3)
                  sh         s5, -260(s3)
                  sh         ra, -630(s3)
                  lbu        a5, 1067(s3)
                  c.addi     t5, -23
                  lbu        s10, 1077(s3)
                  lbu        zero, -892(s3)
                  sb         s9, 201(s3)
                  lb         s6, 826(s3)
                  sb         zero, -882(s3)
                  lui        gp, 1006709
                  lbu        a4, 1581(s3)
                  c.srai     a0, 11
                  lhu        t5, 1878(s3) #end riscv_load_store_rand_instr_stream_7
                  mulhsu     s8, t2, t0
                  c.slli     t4, 29
                  c.addi     s7, -13
                  c.addi     a6, -11
                  c.addi     s0, -9
                  c.addi     a1, -25
                  mulhsu     s10, a3, s0
                  c.addi     s3, -27
                  c.addi     a6, 10
                  sra        s10, s2, a7
                  c.addi     t5, -6
                  lui        a6, 414392
                  c.li       a6, 22
                  c.addi     t3, 22
                  c.addi     gp, -13
                  auipc      s8, 398286
                  c.slli     a4, 3
                  auipc      s5, 479478
                  c.slli     s2, 11
                  auipc      t5, 575843
                  c.slli     s5, 19
                  auipc      a1, 1048098
                  c.addi     s8, 21
                  c.addi     a0, 6
                  mul        s2, t2, s3
                  c.addi     s5, 27
                  c.srli     a0, 10
                  srl        t6, t2, t2
                  c.addi     s10, 1
                  mulhsu     s1, s2, zero
                  auipc      a0, 438777
                  c.slli     gp, 7
                  c.addi     t4, 29
                  c.slli     s3, 3
                  c.addi     a5, -29
                  c.lui      s4, 27
                  or         a5, s11, t5
                  c.addi     s4, 16
                  c.slli     s3, 27
                  c.srli     a4, 6
                  c.addi     s8, 26
                  lui        t3, 292240
                  c.addi     s1, -4
                  auipc      s7, 196896
                  c.beqz     a4, 505f
                  mulhu      a7, a1, s8
                  c.addi     s8, 22
                  lui        s11, 83536
                  rem        a1, a7, a0
                  c.addi     a1, -11
                  bne        s6, ra, 518f
                  auipc      s8, 966196
                  c.add      a0, a1
505:              c.srai     s0, 12
                  c.addi     s10, -24
                  c.slli     s0, 19
                  c.addi     s3, 14
                  c.addi     s7, 31
                  c.addi     a4, -16
                  auipc      s10, 558750
                  lui        s6, 821164
                  c.addi     t5, -23
                  c.lui      s8, 8
                  c.addi     s10, 4
                  c.addi     a4, -8
                  bge        a2, s9, 530f
518:              lui        a5, 783407
                  c.slli     gp, 4
                  c.addi     t4, 28
                  xor        a7, a7, s6
                  lui        zero, 1045934
                  c.addi     t1, 27
                  c.srai     a1, 19
                  c.slli     t2, 21
                  auipc      t2, 53966
                  c.lui      s7, 23
                  c.addi     t4, 27
                  c.addi     t1, -28
530:              c.addi     a2, 5
                  c.addi     a7, 4
                  c.addi     s4, 19
                  lui        s0, 667356
                  c.srli     a1, 26
                  c.nop
                  sra        a5, t3, t3
                  andi       s1, sp, 321
                  lui        t3, 744761
                  divu       t1, a1, s8
                  c.lui      gp, 4
                  c.slli     t3, 17
                  auipc      a0, 74014
                  auipc      t2, 466230
                  srl        t5, s4, s8
                  divu       s7, zero, s3
                  auipc      zero, 1041196
                  c.addi     a7, -19
                  auipc      s1, 186061
                  c.srai     a2, 24
                  lui        s7, 797397
                  c.addi     s11, -5
                  sll        s2, s1, s10
                  c.lui      t6, 20
                  c.srli     a3, 5
                  lui        s7, 535720
                  c.addi     a1, 27
                  la         a5, data_page_6+2002 #start riscv_load_store_rand_instr_stream_3
                  sb         t4, -1708(a5)
                  lbu        a4, -739(a5)
                  lui        t5, 595348
                  lb         t3, -1363(a5)
                  c.addi     t4, -17
                  lbu        a4, 297(a5)
                  fence
                  lb         t6, -1853(a5)
                  sb         s8, -289(a5)
                  lb         t2, 249(a5)
                  c.xor      s1, a2
                  lb         s6, 646(a5)
                  sb         a5, -1051(a5)
                  lbu        a2, 1740(a5)
                  c.addi     a2, 8
                  lhu        a0, 1224(a5)
                  c.addi     t4, 27
                  lhu        zero, -1662(a5)
                  lbu        t6, -776(a5)
                  c.addi     s10, -31
                  lui        a4, 390523
                  c.li       s8, 4
                  lbu        s7, 1976(a5)
                  lbu        a4, 997(a5)
                  lb         s3, -951(a5)
                  addi       s1, gp, 392
                  c.addi     a1, 21
                  c.srai     a4, 7
                  sh         s6, -1140(a5)
                  c.slli     s0, 16
                  c.lui      a2, 15
                  c.addi     t6, -30
                  c.addi     s11, 8
                  auipc      s9, 355217
                  lui        t5, 76055
                  c.addi     s1, 7
                  lbu        s9, -297(a5)
                  lhu        a7, 824(a5)
                  lb         s11, 1347(a5)
                  mulhu      s8, ra, s11
                  c.srli     s1, 28
                  lui        a0, 980902
                  lb         a0, 669(a5)
                  lb         s6, 1296(a5)
                  lb         s11, 13(a5)
                  lb         t1, -1951(a5)
                  lbu        a4, -1594(a5)
                  c.srli     a4, 6
                  c.addi     a0, -4
                  ori        gp, a4, 583
                  lw         a3, -34(a5) #end riscv_load_store_rand_instr_stream_3
                  c.addi     a2, 3
                  c.nop
                  c.addi     s10, -8
                  lui        a2, 437898
                  c.srai     a4, 23
                  auipc      a1, 539497
                  c.addi     a4, 18
                  c.srli     a3, 6
                  slt        t6, a6, s8
                  c.addi     t6, 19
                  mulhsu     zero, t6, t1
                  blt        zero, tp, 586f
                  c.addi     t4, -6
                  auipc      gp, 730875
                  sltiu      s3, t6, 234
                  c.sub      a2, a2
                  auipc      s3, 925479
                  c.addi     t4, 1
                  c.srai     a2, 8
                  c.srai     a5, 4
                  c.addi     a5, -20
                  c.srli     a1, 31
                  c.addi     t5, -21
                  c.srai     a1, 28
                  divu       a2, ra, s0
                  auipc      t3, 6114
                  lui        s8, 445826
                  auipc      s4, 404243
                  c.slli     s8, 8
586:              c.addi     s0, 17
                  c.addi     s11, 20
                  c.addi     a7, 15
                  auipc      a7, 1023155
                  c.addi     s11, -28
                  auipc      a3, 311244
                  c.lui      t5, 14
                  or         s7, t5, s6
                  c.srli     a0, 5
                  auipc      t3, 780430
                  lui        zero, 324160
                  lui        a3, 506197
                  c.li       a7, 4
                  c.lui      s8, 31
                  c.addi     s8, 2
                  srli       a1, t6, 28
                  slt        t2, a4, t5
                  c.lui      a0, 6
                  xori       s3, s2, -647
                  c.addi     a2, 23
                  addi       s1, s4, 327
                  c.addi     a7, 28
                  c.addi     s1, 18
                  c.addi     a2, -32
                  c.srai     s1, 21
                  remu       t4, a0, a2
                  auipc      a0, 567135
                  slti       s6, a6, -171
                  bne        zero, t2, 623f
                  blt        a2, s7, 630f
                  xori       a5, t2, -640
                  c.addi     a5, 19
                  auipc      s10, 859858
                  lui        s10, 339418
                  c.srli     a1, 1
                  lui        s10, 328536
                  auipc      a4, 164687
623:              slli       s11, s2, 23
                  auipc      a2, 512486
                  lui        a0, 124200
                  andi       t6, t1, -689
                  c.srli     a1, 17
                  c.srai     s0, 7
                  srli       s6, sp, 30
630:              c.srli     s0, 17
                  auipc      zero, 429632
                  c.addi     s11, 3
                  c.slli     s1, 17
                  c.addi     s11, -4
                  sra        t6, s2, s7
                  c.srli     a4, 17
                  lui        t2, 453633
                  auipc      s0, 777782
                  c.addi     a0, -25
                  lui        s7, 687681
                  c.beqz     a5, 644f
                  c.addi     s11, 11
                  c.addi     s3, 4
644:              c.addi     t2, -21
                  c.lui      t3, 15
                  nop
                  lui        a3, 609362
                  c.lui      s9, 1
                  c.addi     a5, 5
                  auipc      s4, 57490
                  fence
                  c.addi     s3, -32
                  c.lui      t5, 24
                  div        a1, t5, t5
                  sll        t1, s3, a5
                  c.srli     a1, 26
                  and        t3, s9, a0
                  mulh       a2, s7, s7
                  lui        s8, 239631
                  auipc      s7, 939366
                  lui        s9, 566573
                  c.srai     a4, 31
                  lui        s8, 404577
                  lui        t2, 47408
                  c.srai     s1, 29
                  c.slli     a0, 9
                  c.srai     a0, 31
                  auipc      a1, 280864
                  c.addi     s3, 22
                  c.addi     a5, 29
                  c.srai     a1, 9
                  auipc      a1, 446561
                  c.addi     s3, -3
                  lui        s2, 155917
                  auipc      t2, 182609
                  c.srli     a1, 10
                  c.addi     a0, 25
                  auipc      a6, 436276
                  c.slli     s6, 4
                  c.li       s4, -1
                  c.lui      gp, 12
                  bgeu       t0, s2, 687f
                  div        a1, s7, tp
                  c.slli     s10, 30
                  c.addi     s6, -2
                  lui        zero, 763213
687:              lui        s9, 345463
                  c.srai     s1, 24
                  c.srai     s1, 27
                  auipc      a2, 611758
                  bltu       t1, s10, 708f
                  auipc      s5, 27325
                  auipc      a1, 711645
                  c.addi     s7, -3
                  c.addi     s0, -8
                  auipc      s9, 863646
                  auipc      a1, 832079
                  c.xor      a0, s1
                  lui        t4, 24000
                  c.addi     s11, -25
                  auipc      s10, 904574
                  auipc      a7, 882469
                  auipc      s1, 190078
                  lui        a6, 562098
                  or         a2, a5, a2
                  c.addi     s7, -25
                  c.addi     a1, -15
708:              div        gp, s4, a6
                  c.lui      s6, 6
                  auipc      s9, 169208
                  sra        a6, gp, a2
                  c.srai     a3, 8
                  c.addi     s2, -23
                  lui        zero, 233691
                  c.srai     a4, 26
                  c.addi     s4, 20
                  c.or       a3, a2
                  mulhsu     t5, a6, a5
                  auipc      s4, 480356
                  c.srai     a4, 23
                  mulh       a1, a4, gp
                  rem        s8, s9, a1
                  lui        s4, 969318
                  addi       s4, s7, 455
                  c.lui      a2, 2
                  c.addi     s10, -31
                  sltu       s2, s0, a1
                  sltu       zero, a6, sp
                  fence
                  c.sub      a3, a3
                  c.lui      s2, 5
                  c.sub      a0, a3
                  c.addi     s4, 18
                  auipc      s9, 1027615
                  c.srai     a2, 26
                  auipc      a6, 430066
                  add        a5, zero, s0
                  auipc      s1, 159832
                  c.addi     s6, -15
                  c.addi     t2, -6
                  div        s3, a3, a6
                  lui        a7, 11733
                  auipc      a5, 604819
                  c.mv       a1, t1
                  lui        t6, 731495
                  c.lui      t2, 19
                  c.addi     s3, 31
                  lui        t2, 363118
                  lui        s8, 679734
                  la         s1, data_page_5+2106 #start riscv_load_store_rand_instr_stream_4
                  lb         gp, -1461(s1)
                  lb         t5, -1811(s1)
                  c.srai     a5, 8
                  c.addi     t6, 6
                  c.srai     a5, 12
                  lbu        t6, 1694(s1)
                  c.slli     t5, 11
                  c.addi     s7, -21
                  lhu        t5, -526(s1)
                  c.andi     a5, 14
                  lui        s9, 602578
                  c.addi     s7, 23
                  mulhsu     a2, tp, a4
                  c.addi     s2, 24
                  sw         t4, 502(s1)
                  c.srai     a1, 3
                  c.lui      t4, 31
                  c.srai     a3, 5
                  lhu        t5, -320(s1)
                  c.srai     a0, 13
                  c.addi     t1, -18
                  c.lui      a1, 4
                  lb         s0, 553(s1)
                  lh         a1, -1288(s1)
                  xor        t3, s0, s1
                  auipc      a4, 608697
                  add        t3, t1, a1
                  c.srai     a3, 29
                  fence
                  sb         s4, -751(s1)
                  lui        s9, 704727
                  c.addi     a2, 29
                  c.srai     a1, 5
                  c.addi     t5, -3
                  lhu        s9, -1216(s1)
                  c.addi     a1, -4
                  c.srli     a3, 9
                  sw         t4, 834(s1) #end riscv_load_store_rand_instr_stream_4
                  sll        s0, s4, t2
                  lui        t6, 946335
                  divu       zero, sp, a4
                  lui        s6, 461882
                  auipc      a7, 492520
                  c.addi     s2, -21
                  c.nop
                  c.srai     s1, 11
                  c.srli     a3, 17
                  c.addi     a6, 30
                  lui        s7, 451674
                  c.xor      a1, s1
                  andi       zero, s1, 277
                  lui        gp, 388248
                  c.slli     s6, 14
                  xor        t6, sp, tp
                  c.addi     a5, 3
                  c.addi     s0, 19
                  c.srai     s1, 7
                  blt        a5, a0, 773f
                  c.addi     a3, 26
                  c.mv       s4, t2
                  auipc      s11, 79118
773:              c.lui      s5, 15
                  auipc      s11, 706152
                  c.addi     gp, -27
                  c.srai     a2, 23
                  c.andi     a0, 4
                  sra        a1, t3, s0
                  auipc      a5, 613343
                  auipc      a6, 8736
                  la         s2, data_page_8+1603 #start riscv_load_store_rand_instr_stream_1
                  lbu        s11, -656(s2)
                  mulh       a6, a2, s3
                  sb         a5, 1516(s2)
                  c.slli     a5, 2
                  addi       a4, t2, 245
                  remu       s10, a3, a2
                  andi       s8, s3, -146
                  c.lui      a1, 20
                  lw         a7, -1455(s2)
                  lbu        t5, 724(s2)
                  srli       s7, a7, 18
                  sra        t1, t1, s1
                  c.lui      gp, 9
                  sltu       s8, a2, tp
                  lb         s9, 2009(s2)
                  lui        a6, 531050
                  lb         t6, 1106(s2)
                  auipc      a2, 628197
                  sh         sp, -1541(s2)
                  lbu        s5, 83(s2)
                  c.addi     a6, -21
                  lbu        s6, -832(s2)
                  lhu        t4, -659(s2)
                  lb         a6, 1825(s2)
                  lb         s6, 928(s2)
                  sltiu      s3, a7, 22
                  lb         t2, -482(s2)
                  lb         t1, 1576(s2)
                  sll        s4, s6, a1
                  sb         a3, -1510(s2)
                  lui        s5, 338991
                  c.srai     s0, 14
                  mulhu      s10, a4, a7
                  c.srli     a5, 21
                  c.addi     s11, -9
                  lb         s8, -448(s2)
                  sb         s4, -698(s2)
                  sb         t0, -1352(s2)
                  lh         a2, 1333(s2)
                  c.and      a5, a0
                  sh         sp, -627(s2)
                  lb         a7, 95(s2)
                  sb         t3, 870(s2)
                  c.addi     s10, 1
                  auipc      s7, 686508
                  xori       a1, s4, 732
                  lui        a2, 969573
                  lbu        t3, -1337(s2)
                  lbu        a5, -1123(s2)
                  sb         s9, 182(s2)
                  fence
                  c.addi     s1, -19
                  lbu        t3, -756(s2)
                  sll        a5, gp, s3
                  lb         s5, 1026(s2)
                  lui        t6, 789026
                  lbu        s8, -22(s2) #end riscv_load_store_rand_instr_stream_1
                  lui        t6, 656235
                  c.addi     t4, 23
                  c.addi     s8, 22
                  srai       a4, a6, 14
                  lui        s2, 733595
                  nop
                  bgeu       t3, s2, 793f
                  auipc      s11, 482826
                  c.slli     t1, 13
                  lui        a7, 507436
                  c.addi     s7, 23
                  c.slli     t5, 14
793:              c.lui      a7, 15
                  la         s7, data_page_16+1532 #start riscv_load_store_rand_instr_stream_2
                  auipc      s2, 295817
                  sb         a7, -1262(s7)
                  c.slli     a6, 27
                  lui        gp, 956017
                  mulhu      a4, t2, t2
                  c.slli     s3, 27
                  sb         a2, 815(s7)
                  lw         a3, -848(s7)
                  sub        t2, a5, tp
                  sb         a4, -24(s7)
                  lhu        s10, 130(s7)
                  c.srai     s1, 20
                  sb         s5, 909(s7)
                  c.srli     a2, 30
                  c.addi     s10, 29
                  remu       s8, gp, a2
                  c.slli     s11, 22
                  addi       s6, t4, 364
                  lbu        zero, 597(s7)
                  rem        s9, s6, t4
                  lh         s9, -680(s7)
                  c.addi     a0, -17
                  auipc      a6, 304819
                  lui        s4, 863689
                  lb         gp, -1093(s7)
                  c.addi     a0, 20
                  c.addi     a1, 2
                  c.srli     s1, 13
                  lui        s11, 420094
                  lui        t5, 768157
                  c.lui      a2, 24
                  c.srli     s0, 30
                  lh         a5, 522(s7)
                  add        a0, a6, s7
                  c.addi     a1, -32
                  c.addi     t2, 10
                  c.slli     s8, 9
                  mulhu      s1, s9, t0
                  auipc      s11, 622143
                  lui        s9, 593778
                  lh         a5, 1010(s7) #end riscv_load_store_rand_instr_stream_2
                  c.srli     a2, 6
                  c.lui      s7, 13
                  c.addi     s0, -6
                  c.lui      s7, 8
                  c.addi     t4, 15
                  c.addi     a6, -1
                  c.addi     s9, 28
                  c.addi     t4, -30
                  auipc      s6, 321189
                  c.li       t3, 9
                  lui        s10, 416364
                  c.addi     a7, -22
                  c.lui      s3, 4
                  lui        s0, 1002896
                  auipc      t5, 707159
                  c.addi     t5, -2
                  c.slli     gp, 25
                  lui        s0, 363118
                  c.addi     s7, 23
                  lui        s0, 497990
                  c.add      s1, a5
                  c.addi     s9, 2
                  c.addi     a2, -32
                  c.addi     s1, 16
                  sltiu      s9, t6, 175
                  lui        s3, 941123
                  c.addi     s11, -15
                  c.srli     a2, 14
                  c.slli     a7, 5
                  c.addi     t4, 4
                  lui        s9, 296275
                  div        t2, ra, s7
                  c.srli     a4, 28
                  lui        a2, 154571
                  c.addi     a5, -12
                  c.addi     t6, 9
                  slti       s5, t2, 488
                  bgeu       s1, s4, 835f
                  bgeu       sp, t0, 833f
833:              slti       s3, s3, -546
                  c.addi     s11, 12
835:              c.addi     t4, -29
                  c.slli     a0, 15
                  c.lui      a7, 15
                  slt        s8, s3, a7
                  la         s4, data_page_8+1914 #start riscv_load_store_rand_instr_stream_6
                  lh         s2, 1848(s4)
                  lh         gp, -106(s4)
                  lbu        t5, -1651(s4)
                  lb         t6, 125(s4)
                  lbu        a0, 589(s4)
                  c.addi     s6, 1
                  c.addi     s1, -27
                  lui        s5, 408305
                  lh         s10, 942(s4)
                  auipc      a3, 76968
                  auipc      t4, 41440
                  sb         s1, 1666(s4)
                  lw         zero, 1682(s4)
                  sh         t2, 1008(s4)
                  c.srli     s0, 12
                  sra        s6, ra, t0
                  c.addi     a3, 15
                  c.srai     a2, 1
                  lbu        s5, -1349(s4)
                  sb         s7, 987(s4)
                  c.slli     a4, 14
                  lbu        t1, 381(s4)
                  c.addi     t5, -29
                  c.slli     t3, 7
                  lb         s3, -1385(s4)
                  c.addi     a3, 29
                  auipc      s2, 241224
                  lui        t3, 697796
                  sb         s6, -1129(s4)
                  sb         t5, 1153(s4)
                  c.add      s1, s0
                  auipc      s11, 497814
                  lhu        s9, 284(s4)
                  c.srli     a4, 23
                  c.srai     a3, 15
                  sltiu      s9, t0, -34
                  lbu        s2, -1487(s4)
                  mulh       a4, s5, t1
                  lw         t6, -138(s4)
                  lh         a0, 1224(s4)
                  sb         ra, 790(s4)
                  lw         s0, -1442(s4)
                  sb         a1, 1539(s4)
                  sh         a4, -1468(s4) #end riscv_load_store_rand_instr_stream_6
                  lui        s10, 93247
                  c.addi     s8, 11
                  nop
                  lw         ra, 4(sp)
                  c.srli     a5, 16
                  xor        s9, ra, s7
                  lw         t0, 8(sp)
                  srli       t5, ra, 28
                  lui        s7, 489441
                  c.lui      a7, 12
                  lui        gp, 977950
                  addi       sp, sp, 12
                  lui        s3, 398188
                  c.or       a5, a4
1223:             ret
sub_2:            c.addi     s8, 24
                  addi       sp, sp, -52
                  sw         ra, 4(sp)
                  c.srai     s0, 1
                  sw         t0, 8(sp)
                  and        t2, sp, a5
                  bne        s4, s6, 13f
                  c.addi     a0, 5
                  auipc      s2, 294055
                  c.slli     s8, 10
                  auipc      a5, 919610
                  div        s2, sp, a7
                  auipc      a0, 61255
                  addi       zero, zero, 837
                  lui        s11, 735493
                  fence.i
                  c.srli     a0, 17
                  c.addi     t6, -5
                  lui        t1, 369023
13:               mulhsu     t5, ra, t1
                  auipc      t1, 1021732
                  lui        s7, 101891
                  c.srli     a2, 11
                  c.addi     t6, -26
                  c.srli     a1, 24
                  c.srli     a0, 6
                  auipc      a3, 618039
                  sub        t2, t4, s5
                  c.slli     s4, 6
                  lui        t6, 644219
                  fence.i
                  auipc      t3, 239341
                  bge        t3, a7, 40f
                  c.addi     s11, 1
                  auipc      s4, 532772
                  auipc      a4, 983874
                  c.srai     a4, 12
                  add        a2, t5, a1
                  auipc      t1, 140184
                  c.addi     a7, -12
                  c.slli     a6, 3
                  c.addi     a1, 29
                  lui        a3, 888512
                  c.slli     t1, 1
                  sll        zero, t4, s0
                  auipc      s5, 560976
40:               auipc      s5, 425284
                  c.addi     t4, -1
                  slti       s5, a4, 90
                  auipc      t1, 185586
                  blt        a5, a1, 57f
                  bge        s6, s3, 59f
                  c.srli     a0, 28
                  c.addi     s7, -32
                  c.srli     a5, 24
                  c.addi     a5, -2
                  addi       t2, t4, 161
                  lui        s4, 565411
                  c.andi     a2, 24
                  nop
                  sltiu      s4, a3, -243
                  bne        t5, s11, j_sub_2_sub_3_4 #branch to jump instr
                  c.addi     s10, 17
                  c.lui      s3, 22
                  c.srli     s1, 3
                  c.addi     a1, 27
j_sub_2_sub_3_4:  jal        ra, sub_3
                  c.addi     t3, 15
                  c.srli     s0, 3
                  c.addi     t4, -14
                  lui        gp, 695883
                  c.addi     t5, -21
57:               c.lui      s9, 30
                  c.addi     a1, 11
59:               c.beqz     a4, 75f
                  c.addi     t5, 25
                  c.lui      s2, 5
                  c.lui      a2, 15
                  lui        zero, 580532
                  c.srli     s1, 25
                  c.lui      t3, 19
                  mulhu      s6, s10, a7
                  lui        a4, 68259
                  c.addi     t5, 13
                  lui        a1, 888147
                  c.slli     a3, 13
                  andi       t4, s1, 804
                  sll        s1, t4, a3
                  c.addi     s11, -20
                  auipc      s4, 86342
75:               lui        a4, 588383
                  c.mv       a1, t4
                  c.srai     a1, 15
                  bge        s0, s4, 85f
                  c.addi     s1, -11
                  lui        a3, 373043
                  c.addi     a5, -27
                  c.srai     a3, 11
                  lui        s10, 716826
                  c.addi     s7, 2
85:               auipc      t5, 75055
                  div        t4, s1, t4
                  lw         ra, 4(sp)
                  slti       t2, t2, -375
                  lw         t0, 8(sp)
                  c.and      a4, a5
                  c.addi     s6, -18
                  c.slli     s9, 8
                  addi       sp, sp, 52
                  c.srli     a4, 10
                  c.lui      a2, 24
                  c.addi     gp, 27
                  lui        t2, 427688
113:              ret
sub_5:            c.addi     s10, 17
                  ori        t6, s7, 668
                  addi       sp, sp, -24
                  c.addi     t3, -24
                  sw         ra, 4(sp)
                  auipc      s4, 609837
                  lui        t2, 198958
                  c.addi     s9, 26
                  c.addi     a6, 11
                  sw         t0, 8(sp)
                  c.slli     s8, 29
                  c.addi     s3, 29
                  c.addi     s8, 18
                  c.addi     t2, -21
                  c.slli     t5, 2
                  c.addi     a4, 12
                  c.addi     gp, 24
                  c.slli     a2, 15
                  c.addi     s6, -24
                  rem        a0, t0, s7
                  c.srai     s0, 11
                  c.srli     a3, 24
                  c.addi     s2, 7
                  lui        a0, 652615
                  c.srli     a1, 27
                  c.srli     a5, 6
                  c.srli     a5, 2
                  remu       t4, sp, t6
                  lui        t3, 223018
                  fence.i
                  auipc      a2, 1000328
                  bgeu       s2, zero, 21f
21:               lui        s7, 474112
                  c.add      a1, a2
                  mul        t4, a5, t1
                  bge        a5, t4, 25f
25:               c.slli     s8, 18
                  bge        t5, s5, 46f
                  auipc      zero, 828307
                  c.slli     s3, 30
                  c.addi     s9, -28
                  auipc      a4, 941833
                  c.srai     a5, 26
                  lui        t6, 906393
                  c.slli     s9, 12
                  c.lui      s10, 25
                  addi       a6, ra, 355
                  c.srai     a3, 6
                  c.srai     a2, 14
                  c.slli     a4, 1
                  auipc      t2, 984037
                  c.slli     t2, 11
                  lui        s10, 312443
                  c.addi     a7, 24
                  c.addi     t5, 5
                  c.srai     a5, 26
                  c.addi     gp, 18
46:               lui        s9, 793662
                  ori        gp, t4, -949
                  lui        s5, 742865
                  c.lui      gp, 12
                  auipc      s0, 92681
                  c.addi     t3, 24
                  la         s3, data_page_16+2405 #start riscv_load_store_rand_instr_stream_6
                  lbu        s9, -507(s3)
                  lb         zero, -543(s3)
                  sw         s11, 79(s3)
                  remu       a3, t1, tp
                  c.addi     s4, -6
                  c.addi     a1, -24
                  and        t5, a3, zero
                  c.lui      a4, 9
                  lh         s5, -1805(s3)
                  lb         s7, -500(s3)
                  c.addi     a1, -29
                  lbu        a6, 844(s3)
                  lb         t5, 662(s3)
                  c.srli     a0, 22
                  auipc      t4, 403778
                  c.addi     t4, 31
                  slti       s6, a4, 145
                  c.addi     s8, -29
                  c.lui      s9, 15
                  c.lui      a6, 23
                  c.slli     a7, 28
                  auipc      s5, 1007528
                  lbu        s0, -1035(s3)
                  mulh       a0, ra, t6
                  c.srai     a0, 14
                  lbu        s10, -1378(s3)
                  lui        zero, 657450
                  c.srli     a1, 1
                  c.srli     a1, 11
                  lh         s1, -505(s3)
                  c.addi     s11, -8
                  sb         gp, 1083(s3)
                  sb         gp, 1188(s3)
                  lbu        s4, -1186(s3)
                  sb         s1, -1512(s3)
                  sb         s11, 1416(s3)
                  sh         t0, -719(s3)
                  sb         s10, -586(s3)
                  sb         t4, -798(s3)
                  lb         a2, -1984(s3)
                  c.slli     a1, 31
                  lhu        t5, -1437(s3)
                  sb         a3, 1474(s3)
                  sb         a2, 722(s3)
                  c.addi     a1, 13
                  c.lui      t4, 26
                  lbu        t6, 702(s3)
                  c.srai     a0, 23
                  sb         gp, 1395(s3) #end riscv_load_store_rand_instr_stream_6
                  mulhu      s1, s7, a0
                  c.srai     a3, 26
                  c.lui      t3, 4
                  la         s0, data_page_3+1965 #start riscv_load_store_rand_instr_stream_1
                  lui        s1, 665129
                  c.addi     s8, 12
                  c.srli     a4, 3
                  xori       t5, zero, -680
                  c.lui      t2, 4
                  lui        s7, 458478
                  sb         a0, 131(s0)
                  c.addi     s5, -17
                  c.addi     s11, -16
                  lui        s6, 877433
                  c.srli     a3, 22
                  sh         a4, 1133(s0)
                  lb         t2, 599(s0)
                  lh         zero, 1809(s0)
                  sb         a0, 98(s0)
                  lui        s6, 309908
                  lh         s1, 1431(s0)
                  c.srai     a5, 9
                  lbu        gp, -1773(s0)
                  auipc      s10, 355095
                  c.srai     s1, 12
                  auipc      t2, 274497
                  sw         s11, -33(s0)
                  lb         a6, 1187(s0)
                  ori        s8, t5, 310
                  lb         t2, 700(s0)
                  lh         zero, -1135(s0)
                  lui        a3, 915641
                  c.slli     s7, 13
                  c.srli     s1, 7
                  c.srai     a1, 1
                  rem        a1, ra, s2
                  fence
                  c.addi     a3, -18
                  lbu        s6, -244(s0)
                  c.srai     a4, 11
                  or         t4, a6, gp
                  sb         a4, 1239(s0)
                  c.addi     s4, 8
                  c.lui      a3, 3
                  lb         a3, -1634(s0)
                  lui        s1, 988625
                  lh         gp, 437(s0) #end riscv_load_store_rand_instr_stream_1
                  c.srli     a5, 5
                  c.srai     a5, 9
                  c.addi     s8, -13
                  remu       a2, s11, tp
                  lui        a2, 1014521
                  c.addi     gp, -27
                  andi       s7, t4, -53
                  auipc      t4, 122026
                  c.slli     s11, 18
                  c.srai     a2, 31
                  c.andi     s1, -27
                  lui        s2, 646566
                  c.srli     s1, 15
                  c.addi     s11, 18
                  c.srai     a2, 14
                  c.addi     s10, -10
                  c.addi     s2, -29
                  c.addi     a6, 15
                  c.lui      a4, 20
                  auipc      gp, 559339
                  sub        a3, s0, ra
                  c.addi     a1, -23
                  lui        t2, 180921
                  c.bnez     a2, 83f
                  c.addi     s5, -32
                  c.addi     s6, 16
                  lui        a5, 344534
                  c.addi     s2, -13
83:               c.srli     a4, 18
                  addi       t6, s9, 587
                  c.srai     s1, 6
                  lui        s5, 431271
                  auipc      a6, 470890
                  auipc      s9, 735481
                  lui        a2, 978383
                  c.slli     s7, 9
                  c.srli     a3, 6
                  auipc      s1, 637575
                  auipc      s4, 597479
                  c.addi     s6, -24
                  c.addi     s2, -25
                  c.addi     s3, 2
                  lui        zero, 150506
                  c.lui      a4, 1
                  lui        a3, 66510
                  lui        s3, 403130
                  c.lui      s8, 18
                  auipc      s9, 654632
                  auipc      t3, 551872
                  c.addi     t3, -28
                  lui        t3, 760732
                  fence
                  xori       s5, s1, -1007
                  c.addi     t1, 25
                  c.lui      s6, 13
                  lui        s4, 1044207
                  auipc      t5, 955243
                  c.lui      s5, 30
                  c.xor      s1, a2
                  lui        a6, 79413
                  c.addi     a5, -29
                  c.srai     a2, 17
                  c.addi     s8, -8
                  andi       a2, a7, -371
                  c.addi     s1, 29
                  c.slli     s10, 8
                  lui        s6, 940230
                  c.slli     s10, 25
                  auipc      zero, 540412
                  slti       t6, s7, 227
                  c.xor      a1, a5
                  lui        s10, 525618
                  lui        s5, 612274
                  c.lui      t5, 2
                  auipc      gp, 86686
                  c.slli     t2, 13
                  c.addi     s10, 31
                  c.srai     a2, 23
                  c.addi     s5, 2
                  sltu       a6, a5, t0
                  c.addi     gp, 20
                  c.addi     a4, -10
                  c.addi     s9, -26
                  c.slli     s2, 15
                  lui        s3, 286923
                  auipc      s1, 85485
                  c.srai     a0, 9
                  auipc      s10, 18287
                  c.addi     t6, -1
                  c.addi     a2, -5
                  auipc      s10, 338274
                  c.slli     s10, 29
                  c.slli     a1, 29
                  c.nop
                  c.srli     s1, 12
                  lui        t1, 267640
                  bne        s0, a1, 165f
                  c.addi     t2, -23
                  c.addi     a2, -7
                  c.srli     s1, 22
                  divu       t5, a3, t1
                  auipc      t6, 62340
                  rem        a1, s2, s7
                  slli       a7, s4, 28
                  div        a3, t6, a0
                  c.addi     t4, -23
                  c.slli     s10, 29
                  auipc      s7, 347135
                  c.addi     s6, 16
                  c.lui      a5, 29
165:              c.srli     a2, 2
                  auipc      t4, 381701
                  c.addi     t3, -20
                  c.slli     t1, 9
                  lui        t1, 516526
                  remu       s2, s0, s5
                  c.addi     a0, 22
                  c.addi     s5, 12
                  c.addi     t3, -7
                  bge        gp, t2, 186f
                  auipc      s7, 635521
                  c.addi     t5, -22
                  lui        gp, 76888
                  c.lui      s11, 12
                  c.srai     s0, 17
                  c.xor      a0, s0
                  c.or       s1, s1
                  c.srli     a3, 26
                  auipc      t3, 889782
                  slti       s11, a4, -574
                  c.lui      gp, 10
186:              auipc      s9, 506578
                  c.lui      s3, 12
                  auipc      s6, 952240
                  auipc      s3, 43033
                  c.addi     t5, -29
                  divu       t1, a0, s6
                  c.addi     a5, 16
                  c.nop
                  c.addi     t5, 23
                  c.addi     t1, -3
                  auipc      a6, 724928
                  c.lui      a1, 26
                  srai       a5, t3, 11
                  andi       gp, a4, -204
                  auipc      s11, 154027
                  c.addi     s7, -5
                  c.lui      t6, 18
                  c.addi     a5, -32
                  auipc      s0, 896057
                  c.lui      s9, 28
                  c.srai     a3, 11
                  c.lui      s7, 10
                  c.addi     s7, -24
                  c.nop
                  nop
                  c.or       s0, s0
                  srli       a5, zero, 28
                  c.srli     s1, 5
                  c.addi     a6, 18
                  lui        s5, 468288
                  c.beqz     a0, 222f
                  lui        s5, 310311
                  fence
                  xor        a5, t5, s1
                  nop
                  sll        s2, s0, s1
222:              lui        s6, 805233
                  c.addi     s0, 7
                  sltu       s1, s0, a6
                  c.slli     a4, 31
                  bgeu       s7, a6, 240f
                  add        a4, ra, s9
                  lui        a6, 845203
                  lui        t4, 643507
                  c.srli     s1, 4
                  or         zero, s6, s4
                  c.srli     a3, 18
                  auipc      t1, 644217
                  c.addi     s3, 26
                  lui        s7, 362071
                  sra        s8, t6, t1
                  c.addi     s10, 6
                  c.lui      s1, 25
                  c.srai     a1, 27
240:              c.srai     a5, 30
                  add        s0, gp, a0
                  c.srai     a0, 19
                  lui        s1, 377734
                  auipc      t6, 278530
                  c.addi     a0, 8
                  c.addi     s10, -19
                  ori        t5, s3, 903
                  c.addi     t6, -26
                  beq        s11, s11, 261f
                  c.srai     s1, 28
                  slt        t3, s8, s6
                  lui        a2, 733610
                  ori        t4, sp, 448
                  sltiu      s3, s3, 854
                  auipc      s11, 647843
                  mul        gp, zero, s9
                  c.lui      s7, 15
                  auipc      s7, 485989
                  lui        s6, 539843
                  auipc      gp, 913414
261:              lui        a0, 54403
                  c.slli     s5, 12
                  c.addi     s5, 14
                  div        t5, t1, sp
                  c.addi     a2, 10
                  bgeu       s11, s0, 270f
                  c.srli     a0, 12
                  auipc      a5, 575684
                  auipc      s0, 67259
270:              auipc      t4, 696606
                  mulhu      a1, s2, ra
                  fence
                  lui        a5, 47442
                  c.addi     s8, 11
                  auipc      gp, 1008031
                  lui        s9, 1028111
                  auipc      s9, 171505
                  c.srli     a0, 10
                  lui        s2, 639816
                  srli       s3, a0, 14
                  c.addi     s4, -24
                  xor        s7, t0, s4
                  auipc      s3, 796407
                  auipc      s1, 912636
                  c.addi     a4, -22
                  c.lui      s10, 24
                  lui        t4, 196519
                  c.srai     s1, 1
                  c.addi     s2, 30
                  lui        a1, 314718
                  c.addi     s1, 27
                  c.slli     s6, 11
                  fence.i
                  c.addi     a4, -26
                  addi       s7, a1, 136
                  c.srai     a3, 28
                  c.addi     s10, -28
                  c.srai     a0, 2
                  c.slli     t2, 24
                  lui        t5, 29
                  rem        t6, a1, a3
                  c.slli     s9, 15
                  c.addi     t1, -26
                  c.addi     s7, 25
                  lui        s7, 58169
                  la         t6, data_page_6+2369 #start riscv_load_store_rand_instr_stream_4
                  lbu        s5, 1662(t6)
                  lb         t1, -376(t6)
                  c.addi     t2, -14
                  lui        a5, 53772
                  c.addi     s5, 30
                  c.addi     s11, -9
                  div        a6, a5, t0
                  lb         t5, -1231(t6)
                  c.addi     s4, -28
                  c.lui      s2, 23
                  mulhu      s10, s1, t5
                  lbu        s7, -130(t6)
                  lb         a6, 294(t6)
                  sb         s1, 662(t6)
                  lbu        s6, -1188(t6)
                  lbu        a3, 615(t6)
                  sb         ra, -1732(t6)
                  sb         s8, 1641(t6)
                  c.slli     s5, 16
                  lbu        s3, 1142(t6)
                  c.slli     a2, 13
                  lui        zero, 655601
                  lb         s4, 1196(t6)
                  c.srai     s0, 11
                  lui        s10, 827865
                  c.addi     t1, -8
                  lhu        t3, 1253(t6)
                  lb         s10, 130(t6)
                  lb         a7, 1409(t6)
                  sb         a2, -1898(t6)
                  auipc      t1, 276922
                  auipc      a4, 360448
                  lhu        t1, 355(t6)
                  c.addi     t4, -28
                  auipc      s1, 316578
                  auipc      gp, 379533
                  lb         s8, 1614(t6)
                  remu       s0, a5, gp
                  c.srai     a2, 6
                  lhu        s3, 949(t6)
                  divu       t1, s3, t3
                  lbu        a3, 851(t6)
                  sb         a1, -758(t6)
                  xori       a7, s6, -765
                  lbu        a7, 293(t6) #end riscv_load_store_rand_instr_stream_4
                  c.addi     s7, 6
                  auipc      s10, 449337
                  lui        t3, 952062
                  c.srai     s1, 27
                  lui        s10, 111213
                  c.addi     a4, -18
                  lui        s8, 602305
                  c.srai     a3, 18
                  c.srli     a4, 8
                  lui        a1, 74113
                  lui        t4, 420645
                  mulhu      s11, a3, a5
                  c.slli     t6, 12
                  xori       t3, s8, 792
                  c.srli     a0, 31
                  c.addi     gp, 3
                  c.srli     s1, 12
                  c.addi     s3, 28
                  c.addi     a6, 21
                  c.srli     a2, 18
                  c.addi     s9, 19
                  lui        gp, 221168
                  lui        t5, 383961
                  c.li       t5, -26
                  c.andi     a5, -6
                  c.addi     a1, -30
                  ori        s9, t2, -233
                  c.srai     a3, 19
                  c.srli     a1, 11
                  auipc      s10, 874763
                  c.srli     a2, 29
                  c.addi     t2, 26
                  c.addi     a4, -25
                  c.srai     a1, 16
                  c.srai     a2, 17
                  c.addi     s8, 19
                  auipc      t5, 508950
                  bge        s3, tp, 346f
                  c.addi     a3, -2
                  c.addi     a4, 20
346:              sltu       s7, tp, s2
                  c.addi     s3, -11
                  lui        t1, 788799
                  c.nop
                  rem        s6, s5, s4
                  c.slli     a1, 9
                  lui        s7, 630037
                  c.srli     s1, 31
                  c.addi     a5, -27
                  c.addi     a0, 23
                  c.andi     s0, -29
                  lui        s2, 752773
                  auipc      a5, 1036298
                  srai       a7, a4, 25
                  sltiu      a0, s2, -750
                  auipc      t5, 790094
                  auipc      a3, 516756
                  c.slli     gp, 19
                  auipc      s9, 415043
                  c.addi     a7, -12
                  c.lui      s5, 25
                  c.slli     s1, 8
                  xor        s7, s3, s9
                  c.addi     s0, -8
                  c.slli     a0, 9
                  c.addi     s8, 8
                  c.lui      a2, 22
                  fence
                  c.srli     a0, 7
                  c.addi     t2, -31
                  c.addi     t1, -8
                  c.addi     s3, 16
                  c.addi     s3, 23
                  mulhu      a3, a6, s4
                  xor        s0, gp, s9
                  c.srai     a1, 27
                  auipc      t2, 378304
                  c.lui      s0, 14
                  c.addi     a7, -12
                  sltiu      zero, t4, 376
                  c.srai     s0, 24
                  c.addi     s2, -9
                  c.slli     s4, 21
                  lui        s1, 593795
                  c.slli     s0, 25
                  c.addi     gp, -16
                  or         a1, t4, sp
                  add        t3, t3, s0
                  c.slli     t6, 31
                  auipc      a1, 474962
                  c.sub      a2, s1
                  xori       s10, s10, 579
                  c.lui      t1, 28
                  c.addi     a3, 4
                  c.li       s9, -30
                  slti       t5, t2, 142
                  c.srli     a1, 31
                  mul        a3, a2, t4
                  c.addi     s2, -5
                  c.addi     s3, 11
                  c.addi     s5, 30
                  c.addi     a6, 27
                  slt        s4, s0, a5
                  c.slli     s10, 5
                  c.addi     a3, -2
                  c.addi     s1, 29
                  c.addi     a4, 13
                  c.addi     t6, 1
                  c.addi     a3, 31
                  slli       gp, a0, 17
                  mul        s10, a0, s9
                  mul        t4, t5, t0
                  lui        t4, 382843
                  srl        s6, s11, gp
                  lui        s1, 373058
                  lui        s0, 3016
                  xor        a6, t3, zero
                  auipc      s7, 63813
                  c.lui      a1, 2
                  c.slli     s3, 23
                  c.srli     a0, 10
                  auipc      s8, 113666
                  fence.i
                  auipc      s10, 599169
                  c.addi     t4, 7
                  c.lui      a3, 11
                  lui        s9, 34008
                  bne        a3, s10, 435f
                  auipc      a7, 724833
435:              c.addi     s4, -19
                  c.addi     gp, 24
                  divu       t1, a0, t1
                  c.addi     a1, -13
                  lui        a0, 453520
                  c.addi     s3, 5
                  andi       a7, s5, 609
                  c.addi     t5, 26
                  c.addi     a2, -4
                  c.srai     a5, 14
                  bne        s7, s4, 460f
                  c.srli     a3, 31
                  auipc      a3, 174758
                  c.srli     a2, 24
                  auipc      a5, 973182
                  auipc      s0, 421984
                  c.lui      a6, 16
                  c.addi     a4, 28
                  c.addi     s11, -6
                  c.nop
                  c.li       gp, 12
                  c.srai     a1, 15
                  c.xor      a1, a3
                  c.addi     a5, -7
                  c.nop
460:              lui        a1, 300750
                  la         a1, data_page_19+2481 #start riscv_load_store_rand_instr_stream_8
                  auipc      a5, 191283
                  lhu        t4, -1053(a1)
                  sh         a1, -1565(a1)
                  c.addi     t2, 21
                  c.lui      a7, 9
                  lbu        s0, -1360(a1)
                  lb         s6, -899(a1)
                  auipc      s8, 884444
                  auipc      s6, 862922
                  lb         s4, 108(a1)
                  lui        s9, 198615
                  sb         a5, -486(a1)
                  lb         s3, -1160(a1)
                  sltiu      a6, ra, 819
                  sh         a0, -381(a1)
                  c.addi     t5, 15
                  lh         a0, 1407(a1)
                  sb         a1, 238(a1)
                  c.addi     s9, 10
                  lb         s10, -788(a1)
                  c.srli     a2, 27
                  sw         tp, -597(a1)
                  lh         t5, -1599(a1)
                  sb         a6, -759(a1)
                  sb         s0, -1675(a1)
                  lb         s4, 1082(a1)
                  lhu        t6, 1173(a1)
                  c.lui      s11, 13
                  lb         t3, -1379(a1)
                  sb         t0, -1288(a1)
                  mulhsu     t3, s4, t4
                  c.addi     t5, 21
                  lb         s5, 586(a1)
                  c.srli     a3, 7
                  lb         s9, 604(a1)
                  lui        s1, 589244
                  div        t2, s8, t0
                  lb         t3, -1347(a1)
                  c.addi     s9, -15
                  lb         t4, 1288(a1)
                  sb         s11, -1210(a1)
                  c.addi     a3, 21
                  and        s4, s1, a5
                  c.lui      s9, 3
                  lh         s8, 105(a1)
                  sb         a6, -1293(a1)
                  lbu        zero, -1232(a1)
                  sh         ra, -899(a1)
                  lhu        t5, -1495(a1)
                  lb         s2, 832(a1) #end riscv_load_store_rand_instr_stream_8
                  c.slli     s5, 1
                  auipc      s5, 4404
                  c.srli     a2, 5
                  c.addi     s2, 1
                  lui        s0, 667360
                  c.sub      s1, a0
                  c.addi     a1, 4
                  mulh       s0, s5, a4
                  c.srai     a3, 12
                  divu       s1, a0, t6
                  lui        s8, 252068
                  lui        t4, 551972
                  c.srli     s0, 5
                  slti       a0, s9, 620
                  lui        s7, 401881
                  lui        a5, 695918
                  sltu       s3, zero, a3
                  c.addi     t3, 16
                  c.srli     a3, 3
                  lui        s0, 777712
                  c.addi     s11, -17
                  c.addi     a0, 13
                  c.slli     s10, 5
                  c.srai     a0, 21
                  bge        s1, t6, 486f
486:              lui        s4, 982320
                  c.srli     s1, 12
                  auipc      s5, 946946
                  c.addi     t6, 29
                  c.addi     s0, -32
                  auipc      t2, 554370
                  c.srli     a0, 20
                  c.addi     s3, -21
                  c.srli     a3, 5
                  lui        a1, 347988
                  c.addi     s1, 29
                  c.srli     a3, 31
                  auipc      s11, 888273
                  sltu       s9, s8, tp
                  auipc      a4, 821068
                  c.srai     a2, 9
                  c.srai     a0, 23
                  srli       t1, a7, 25
                  auipc      t5, 637433
                  auipc      t6, 1047547
                  c.slli     s1, 3
                  auipc      a6, 775678
                  lui        t2, 539869
                  c.slli     s9, 22
                  sltiu      s7, s0, -463
                  c.lui      s6, 24
                  auipc      s3, 370108
                  c.srli     a4, 24
                  c.srli     s0, 9
                  c.addi     s6, -15
                  auipc      t2, 124264
                  andi       s1, tp, 411
                  c.lui      t4, 20
                  auipc      s2, 93541
                  c.srai     a3, 7
                  and        s11, t4, a3
                  c.addi     a2, -13
                  c.addi     s10, -5
                  lui        a4, 813346
                  c.addi     a5, 5
                  c.addi     a2, -20
                  c.addi     a6, -11
                  c.srli     a5, 10
                  c.srai     a2, 14
                  lui        s3, 1033014
                  c.srai     a0, 17
                  c.xor      a1, a1
                  c.addi     s1, -25
                  c.lui      t2, 21
                  c.lui      t5, 28
                  c.addi     a1, -13
                  c.nop
                  lui        a3, 790744
                  c.addi     t1, -5
                  c.slli     a3, 17
                  c.lui      s3, 26
                  c.srli     s0, 25
                  c.bnez     a2, 546f
                  c.addi     t5, 15
                  c.slli     a7, 23
546:              and        s8, s2, a3
                  beq        s10, tp, 553f
                  auipc      a4, 931209
                  c.slli     s10, 30
                  c.bnez     a4, 568f
                  c.addi     a1, 25
                  lui        a6, 1017795
553:              c.slli     a6, 4
                  lui        gp, 348999
                  c.addi     s11, 23
                  fence
                  c.slli     s5, 15
                  c.srai     a4, 20
                  c.lui      t3, 16
                  c.slli     a4, 27
                  divu       s9, gp, a2
                  slli       a3, s9, 9
                  c.addi     t4, -2
                  c.lui      a7, 27
                  c.addi     gp, 6
                  la         s0, data_page_12+2214 #start riscv_load_store_rand_instr_stream_3
                  c.lui      s9, 6
                  lb         t1, -655(s0)
                  c.slli     t6, 10
                  c.srli     a0, 28
                  sb         a7, -945(s0)
                  divu       a2, zero, sp
                  lhu        a4, -170(s0)
                  lb         s4, 1644(s0)
                  sw         s1, -302(s0)
                  c.sub      a1, a5
                  lh         a7, 1412(s0)
                  auipc      s6, 571158
                  lbu        t4, -1735(s0)
                  c.srai     a2, 30
                  c.addi     t5, -10
                  c.addi     s8, 10
                  c.addi     a3, -6
                  auipc      s4, 846
                  addi       t4, s0, 686
                  lhu        a0, -80(s0)
                  c.lui      a3, 20
                  c.addi     t4, 10
                  slti       a1, s3, -764
                  c.lui      a0, 27
                  sb         s8, -490(s0)
                  lui        s8, 440069
                  lb         s8, 169(s0)
                  c.srli     s1, 15
                  remu       t1, t2, a0
                  lw         t2, -1694(s0)
                  lui        a1, 308156
                  c.srai     a2, 27
                  sb         s0, -1268(s0)
                  lh         a5, 1466(s0)
                  c.lui      a7, 19
                  c.addi     a4, 25
                  lbu        s6, 116(s0)
                  c.addi     s5, 19
                  srl        a3, t1, s8
                  lui        t5, 186129
                  auipc      s10, 953418
                  c.addi     s9, -4
                  lbu        t5, 1338(s0)
                  sb         s2, 867(s0)
                  sltiu      zero, s9, 206
                  sra        s9, t6, s9
                  sb         zero, -81(s0)
                  lbu        a3, 1344(s0) #end riscv_load_store_rand_instr_stream_3
                  and        a4, zero, a4
                  c.addi     s2, 29
568:              c.addi     s7, 6
                  c.addi     s2, -20
                  c.srli     a2, 29
                  xori       t6, t5, 242
                  c.addi     a1, 25
                  c.addi     s7, 21
                  c.beqz     a1, 594f
                  c.addi     t5, -11
                  lui        t5, 301793
                  srli       t3, t0, 17
                  lui        t3, 817177
                  c.slli     t2, 29
                  divu       a5, s2, a1
                  c.addi     t3, -30
                  c.addi     s11, -18
                  c.andi     a1, -12
                  c.xor      s0, a4
                  c.beqz     s0, 605f
                  c.addi     s5, -14
                  c.addi     t4, -9
                  c.srai     a5, 30
                  c.lui      a5, 31
                  addi       a7, a0, 798
                  c.addi     gp, 26
                  c.addi     a2, 3
                  c.addi     s2, 5
594:              c.addi     t3, -32
                  nop
                  sra        zero, t4, s11
                  lui        a3, 197611
                  c.lui      a4, 22
                  fence
                  auipc      s11, 953963
                  srli       a3, s3, 15
                  c.slli     s1, 26
                  auipc      s6, 369227
                  beq        t1, s0, 623f
605:              c.lui      s5, 9
                  ori        a0, tp, 91
                  c.addi     a5, 21
                  lui        s7, 718281
                  c.addi     s10, -22
                  addi       s1, a5, -253
                  auipc      s10, 636489
                  lui        s10, 1030968
                  lui        gp, 862362
                  c.lui      a2, 12
                  c.sub      a1, a5
                  c.lui      t4, 25
                  c.srli     a5, 13
                  c.addi     s9, 16
                  c.addi     s7, -5
                  lui        gp, 384321
                  c.srli     a0, 11
                  lui        s9, 600434
                  la         s0, data_page_14+2468 #start riscv_load_store_rand_instr_stream_7
                  sb         a5, 1277(s0)
                  auipc      s10, 994330
                  c.srli     a5, 5
                  c.sw       s1, 60(s0)
                  lbu        t5, -1433(s0)
                  lb         t6, -770(s0)
                  lbu        t6, -1788(s0)
                  lui        s9, 267173
                  lw         t6, 1152(s0)
                  c.addi     s9, 6
                  addi       zero, t3, 694
                  lb         a7, -1863(s0)
                  c.srai     a5, 8
                  lb         a2, 1413(s0)
                  sb         t5, 33(s0)
                  sw         a7, 1620(s0)
                  c.addi     a3, 29
                  lui        zero, 87130
                  c.srai     s1, 5
                  c.lw       a3, 100(s0)
                  lb         a2, 1222(s0)
                  sh         s9, -1130(s0)
                  sb         zero, -1995(s0)
                  lb         t3, 1357(s0)
                  lb         t4, -1821(s0)
                  sltu       t3, a6, a6
                  lh         zero, 312(s0)
                  c.srli     a1, 30
                  sb         s5, 103(s0)
                  lbu        s6, -1226(s0) #end riscv_load_store_rand_instr_stream_7
623:              c.slli     a1, 31
                  c.addi     gp, 10
                  c.srli     a4, 26
                  lui        s4, 666080
                  c.srai     a0, 6
                  c.mv       s8, ra
                  c.srai     a3, 20
                  c.srli     s1, 28
                  c.slli     s11, 29
                  c.addi     s7, -9
                  c.lui      a1, 15
                  c.addi     s8, 25
                  c.srai     a3, 9
                  c.srli     s0, 3
                  c.srli     a1, 5
                  c.li       a5, 12
                  c.addi     t4, -13
                  auipc      s6, 468969
                  auipc      s1, 259499
                  la         t4, data_page_6+2683 #start riscv_load_store_rand_instr_stream_0
                  lui        s0, 210517
                  lb         s6, -1578(t4)
                  sb         s3, 1020(t4)
                  sltu       a4, a1, s1
                  lui        s4, 418110
                  auipc      s6, 1026683
                  c.slli     s9, 26
                  auipc      s8, 1034627
                  c.li       a4, 14
                  c.lui      t2, 21
                  c.addi     a2, -14
                  c.slli     a7, 4
                  c.addi     a5, 11
                  sub        a1, t1, s11
                  auipc      s1, 168359
                  auipc      s3, 705571
                  c.addi     a3, 19
                  lhu        a7, 629(t4)
                  lui        s11, 95510
                  c.addi     a0, 16
                  c.slli     s3, 6
                  c.srai     s0, 5
                  lb         s1, -318(t4)
                  lbu        s0, 1392(t4)
                  c.addi     s3, 24
                  c.srai     a1, 26
                  auipc      t5, 190162
                  c.addi     t3, 19
                  lb         s4, -958(t4)
                  lbu        a5, -1451(t4)
                  lui        a5, 107854
                  c.lui      s0, 6
                  c.addi     a6, -5
                  sb         zero, 269(t4)
                  lui        s10, 399921
                  sb         s2, -1414(t4)
                  sb         s2, 432(t4) #end riscv_load_store_rand_instr_stream_0
                  lui        a7, 140159
                  lui        t6, 142506
                  slti       s2, ra, -705
                  lui        s1, 702685
                  c.or       s0, a1
                  c.lui      s11, 26
                  c.addi     s8, -16
                  auipc      s7, 135311
                  auipc      a2, 719063
                  xor        a6, sp, gp
                  c.lui      t5, 20
                  c.slli     a2, 14
                  mulh       s5, t6, a5
                  c.addi     t6, -7
                  rem        a6, s5, a4
                  c.and      a1, s1
                  c.srli     a2, 18
                  auipc      s1, 279791
                  fence.i
                  c.slli     t3, 6
                  c.srli     a0, 4
                  c.lui      gp, 12
                  c.srli     a0, 11
                  c.addi     s6, 6
                  slti       t6, a1, 460
                  lui        s5, 191580
                  add        s7, s10, s0
                  c.srai     a2, 14
                  c.addi     a1, 13
                  c.addi     a5, -25
                  lui        t3, 951345
                  c.lui      a2, 23
                  c.bnez     s1, 682f
                  lui        t3, 459971
                  div        gp, t0, t0
                  lui        s8, 853177
                  c.addi     s7, 8
                  ori        a7, s11, 1021
                  divu       t1, zero, a7
                  c.addi     a6, -3
682:              c.addi     a0, -26
                  lui        s1, 1015170
                  auipc      t1, 714368
                  srl        s3, s8, t0
                  auipc      s8, 59292
                  c.slli     a5, 22
                  divu       t6, s1, s5
                  c.addi     s0, 21
                  c.lui      t1, 31
                  mulh       t6, s1, a5
                  c.slli     a6, 20
                  c.slli     s5, 26
                  c.srai     s0, 14
                  andi       s6, s9, 166
                  la         gp, data_page_11+2517 #start riscv_load_store_rand_instr_stream_10
                  sb         gp, -1335(gp)
                  c.addi     a3, -7
                  lui        a2, 264901
                  lbu        t3, 625(gp)
                  c.lui      t2, 12
                  lui        s11, 818141
                  sb         a1, -887(gp)
                  sb         t1, 1521(gp)
                  lui        a6, 241328
                  sb         zero, 814(gp)
                  sb         s5, -1988(gp)
                  auipc      t4, 826958
                  lb         a6, -345(gp)
                  auipc      a4, 499204
                  c.srli     a0, 23
                  sb         a3, 1466(gp)
                  sb         s5, 986(gp)
                  c.addi     s11, -26
                  lb         s6, -1716(gp)
                  c.lui      t2, 2
                  auipc      t1, 324575
                  c.addi     s2, -12
                  divu       t4, a3, s2
                  auipc      t5, 851210
                  lw         zero, -97(gp)
                  divu       a6, s7, s11
                  sh         a7, -541(gp)
                  lbu        a4, -520(gp)
                  sh         a0, 1105(gp)
                  lbu        a4, -154(gp)
                  sb         s7, -754(gp)
                  lbu        a3, 570(gp)
                  lbu        a6, 1008(gp)
                  sb         s3, 549(gp)
                  lb         zero, -2040(gp)
                  lb         s9, -894(gp)
                  c.addi     s6, -20
                  sb         a1, -594(gp)
                  c.lui      s9, 28
                  lhu        a0, -1833(gp)
                  lbu        a3, -1565(gp)
                  lhu        s6, -87(gp)
                  sb         s8, 653(gp)
                  c.slli     a2, 19
                  sb         a1, 177(gp)
                  c.srli     a2, 10
                  c.addi     s2, -23
                  c.srai     s0, 19
                  sb         s7, 161(gp)
                  lb         s1, -736(gp)
                  sb         a5, -1978(gp) #end riscv_load_store_rand_instr_stream_10
                  c.lui      s6, 9
                  slti       s0, a5, -329
                  auipc      s8, 671326
                  c.addi     gp, 11
                  c.srai     a2, 9
                  c.slli     s0, 17
                  c.andi     s1, 26
                  c.lui      a6, 18
                  c.srli     s0, 8
                  c.srli     a0, 27
                  auipc      zero, 94912
                  auipc      s2, 429313
                  c.srai     a3, 6
                  lui        a3, 73132
                  c.sub      a3, s0
                  and        s8, t6, t6
                  lui        a2, 838514
                  lui        s11, 91999
                  lui        s1, 363789
                  c.addi     s3, 14
                  c.andi     a1, 23
                  c.addi     t4, 2
                  c.nop
                  auipc      s4, 435059
                  lui        t6, 418643
                  c.addi     t5, 28
                  auipc      s2, 244757
                  fence.i
                  c.srai     a4, 2
                  beq        t0, s3, 729f
                  c.lui      a2, 25
                  c.addi     t4, 29
                  auipc      a0, 329504
729:              c.slli     t3, 13
                  c.addi     s6, -24
                  c.srli     a2, 30
                  c.andi     s1, 21
                  c.mv       s3, s1
                  lui        s2, 441743
                  auipc      a4, 256952
                  c.srli     s1, 25
                  auipc      a0, 380780
                  c.addi     s2, 6
                  lui        s2, 21214
                  auipc      s5, 760982
                  auipc      s6, 798681
                  c.slli     a3, 8
                  c.addi     a7, 2
                  c.srli     a1, 20
                  c.lui      s4, 23
                  c.addi     s4, -30
                  c.addi     gp, -15
                  mulhsu     s5, s6, a6
                  c.lui      a0, 25
                  c.lui      t2, 8
                  blt        s7, zero, 769f
                  add        t5, s0, s0
                  lui        s2, 113600
                  auipc      s2, 703225
                  c.srli     a4, 21
                  mulhsu     a7, s8, t4
                  sub        s1, t3, s6
                  sll        a5, s1, s7
                  lui        a4, 58276
                  lui        s4, 41495
                  c.slli     s9, 5
                  c.or       a3, a3
                  c.addi     gp, 30
                  c.nop
                  c.lui      a6, 2
                  c.addi     gp, 10
                  c.addi     s6, -10
                  c.addi     t4, 26
769:              mulhu      a5, t6, t5
                  auipc      t4, 158209
                  or         a4, s5, s10
                  c.addi     a1, 15
                  auipc      a1, 808002
                  bge        s3, zero, 782f
                  and        t2, s0, t3
                  c.addi     s7, 17
                  c.addi     a2, 8
                  la         t4, data_page_19+1386 #start riscv_load_store_rand_instr_stream_9
                  auipc      s1, 92293
                  sb         a4, 534(t4)
                  c.srli     a4, 29
                  lui        s0, 427202
                  sb         s0, 1175(t4)
                  lb         s10, 1650(t4)
                  sb         zero, -1307(t4)
                  sh         ra, 300(t4)
                  lui        t2, 574006
                  lhu        zero, 844(t4)
                  slt        s1, s1, s3
                  lh         a6, 56(t4)
                  sh         sp, 1862(t4)
                  lw         a6, 470(t4)
                  lui        s5, 796712
                  c.srai     a2, 15
                  lui        t5, 296372
                  lh         gp, 116(t4)
                  c.addi     s4, -25
                  auipc      t5, 109422
                  c.addi     a0, -10
                  lb         s6, 988(t4)
                  c.srai     a2, 6
                  lui        s5, 648961
                  c.slli     s1, 13
                  sb         a4, 43(t4)
                  lb         s8, 501(t4)
                  lbu        s9, 324(t4)
                  lb         a2, -337(t4)
                  c.add      a1, s0
                  lhu        s10, 950(t4)
                  lh         a0, -686(t4)
                  and        s6, t6, a7
                  sh         a0, -798(t4)
                  add        t3, s5, t5
                  auipc      a1, 136849
                  div        gp, a6, a1
                  mulhu      s4, s4, a6
                  c.srai     a5, 29
                  lui        s1, 322865
                  lbu        a5, 1366(t4)
                  sb         a1, 1191(t4)
                  lbu        a5, 743(t4) #end riscv_load_store_rand_instr_stream_9
                  c.addi     s5, 22
                  c.addi     a3, 29
                  c.addi     gp, -18
                  c.mv       s3, a5
782:              bne        t4, s0, 794f
                  auipc      t4, 420366
                  mul        a4, s7, a7
                  auipc      gp, 1000316
                  auipc      a5, 955631
                  sll        s6, ra, a1
                  auipc      a6, 29054
                  c.or       s0, a5
                  c.bnez     s0, 805f
                  c.srli     a1, 13
                  c.addi     t5, -24
                  c.lui      a3, 26
794:              c.addi     gp, 3
                  div        zero, t4, a2
                  c.andi     a5, -16
                  c.addi     a6, -31
                  c.addi     s6, 18
                  auipc      s6, 712142
                  add        gp, a2, a1
                  c.slli     a5, 22
                  sub        t1, a3, s7
                  c.addi     a1, 3
                  c.srai     a0, 20
805:              c.srai     a0, 6
                  c.addi     t1, -5
                  c.addi     a2, 19
                  c.lui      s7, 2
                  lui        s5, 986505
                  c.addi     t3, -23
                  bgeu       tp, sp, 825f
                  lui        a3, 560411
                  c.slli     t5, 6
                  c.addi     a5, 30
                  c.addi     s1, -1
                  c.slli     t4, 12
                  beq        ra, a2, 821f
                  auipc      zero, 644120
                  lui        a7, 929037
                  mulhu      t1, a6, t1
821:              auipc      a0, 659441
                  c.addi     s5, -13
                  c.and      s1, a4
                  c.lui      a2, 16
825:              c.srli     a4, 24
                  c.mv       s10, t2
                  c.lui      a1, 20
                  c.addi     a2, 6
                  ori        s3, s5, 672
                  remu       s11, s2, s2
                  c.addi     s8, 10
                  c.addi     t6, -23
                  lui        s4, 34579
                  auipc      t4, 787194
                  c.addi     s7, 10
                  auipc      t2, 277338
                  auipc      zero, 66789
                  lui        gp, 572861
                  lui        s4, 231713
                  c.bnez     a2, 858f
                  c.srli     a2, 14
                  c.addi     t6, -26
                  auipc      a7, 405994
                  mulhu      s2, a7, a1
                  c.addi     s4, 7
                  srai       a6, s10, 19
                  auipc      s9, 230715
                  c.addi     a5, -32
                  c.addi     t5, -31
                  bgeu       s4, s11, 858f
                  lui        a4, 144163
                  lui        s2, 592796
                  c.slli     s11, 22
                  c.srli     a0, 20
                  auipc      gp, 190133
                  c.slli     a5, 3
                  c.or       s1, a4
858:              srli       s6, t4, 29
                  c.addi     s3, 4
                  c.addi     s10, -6
                  c.addi     s3, -20
                  c.addi     a6, -18
                  auipc      s0, 356994
                  lui        s8, 74376
                  c.andi     s1, -21
                  c.addi     t1, -21
                  c.lui      a2, 24
                  c.srli     a0, 23
                  c.srli     a0, 2
                  c.addi     a1, 18
                  c.slli     s10, 20
                  mulh       t2, t3, zero
                  c.and      a4, s0
                  c.and      a2, a5
                  lui        gp, 838147
                  c.or       s1, a4
                  lui        s0, 112447
                  c.srai     a1, 2
                  lui        t2, 549559
                  auipc      t1, 570371
                  mulh       a1, a6, t2
                  c.addi     s7, 25
                  auipc      t4, 735893
                  c.addi     a7, -31
                  c.slli     a6, 11
                  c.addi     s8, 9
                  c.addi     a4, -6
                  c.srai     a2, 17
                  c.srli     a5, 28
                  add        s8, t1, t2
                  sltiu      t2, s1, 881
                  auipc      t1, 157160
                  slt        t1, t4, t6
                  c.srai     a0, 8
                  slt        s2, gp, s4
                  divu       s3, s6, sp
                  c.li       gp, -32
                  c.slli     a3, 10
                  c.addi     a6, 25
                  c.slli     a7, 8
                  c.addi     s10, 10
                  or         s5, s3, a2
                  addi       t4, a7, 285
                  lui        a7, 547233
                  lui        s8, 432116
                  c.srli     a3, 4
                  c.srai     s1, 26
                  c.srli     a4, 27
                  sltiu      t5, a3, -95
                  c.lui      a4, 30
                  c.or       a3, a4
                  c.srai     a1, 30
                  c.slli     a6, 21
                  c.lui      a6, 7
                  auipc      t3, 638464
                  auipc      a0, 688798
                  c.lui      s10, 31
                  remu       s1, s8, t3
                  lui        a0, 706906
                  fence.i
                  c.srli     s1, 12
                  c.addi     s1, 31
                  c.nop
                  c.addi     s3, 18
                  and        s7, s9, s7
                  c.addi     s7, -13
                  c.slli     s9, 14
                  auipc      s9, 800182
                  auipc      s6, 528664
                  lui        s10, 120824
                  c.srli     a4, 25
                  auipc      s7, 320182
                  c.addi     a6, 9
                  bgeu       s6, t1, 939f
                  srai       t5, gp, 14
                  c.srli     a5, 25
                  c.addi     s1, 30
                  c.slli     t6, 31
939:              div        a3, t5, s2
                  c.and      a1, a3
                  c.add      s0, a4
                  c.lui      s10, 7
                  c.slli     s9, 25
                  auipc      t2, 270788
                  auipc      a6, 800165
                  lui        t5, 971953
                  c.bnez     a5, 950f
                  bltu       tp, s5, 967f
                  srai       s11, a6, 30
950:              lui        zero, 705352
                  c.lui      s2, 29
                  c.slli     t6, 12
                  c.slli     s2, 9
                  la         a3, data_page_13+1933 #start riscv_load_store_rand_instr_stream_5
                  sw         t6, -141(a3)
                  lb         s10, 1925(a3)
                  auipc      t3, 396639
                  sb         s4, 1998(a3)
                  c.addi     t3, -10
                  c.or       a1, a2
                  sb         a1, 431(a3)
                  lb         s11, 952(a3)
                  sw         gp, -1425(a3)
                  lb         a1, 245(a3)
                  lb         a5, -1392(a3)
                  lbu        t4, 384(a3)
                  sb         s3, -1088(a3)
                  remu       s6, a2, a2
                  lbu        a6, -712(a3)
                  sb         s8, 863(a3)
                  c.addi     gp, 9
                  c.slli     t5, 18
                  lb         t1, -1124(a3)
                  lui        a0, 841237
                  lw         t4, -1829(a3)
                  lb         s3, 1634(a3)
                  sb         s1, 1389(a3)
                  sb         a6, -1833(a3)
                  lbu        a7, 1642(a3)
                  lb         a6, 1367(a3)
                  sub        t5, s6, zero
                  andi       s6, sp, 415
                  lhu        a5, -1579(a3)
                  c.srai     a0, 23
                  lb         a2, -1192(a3)
                  sh         s9, 1507(a3)
                  lbu        a0, 922(a3)
                  lbu        t4, 366(a3)
                  auipc      zero, 411753
                  lw         s4, 263(a3)
                  sb         s2, 1422(a3)
                  c.slli     t2, 18
                  sb         ra, -1196(a3)
                  lh         a7, 491(a3)
                  c.or       a1, s1
                  lb         t3, 1938(a3) #end riscv_load_store_rand_instr_stream_5
                  c.addi     s8, -30
                  auipc      a7, 129552
                  c.addi     s7, -7
                  c.addi     s7, -8
                  fence
                  c.srai     a2, 1
                  c.addi     a3, 20
                  auipc      t2, 902484
                  c.lui      a6, 26
                  c.srai     a3, 31
                  auipc      a2, 84707
                  auipc      t2, 295356
                  c.lui      a2, 30
967:              lui        s1, 151341
                  lui        gp, 990002
                  c.addi     a1, -2
                  remu       a6, a5, a2
                  auipc      s8, 692726
                  c.addi     t1, 31
                  c.srli     a3, 25
                  c.slli     s4, 30
                  lui        a3, 743252
                  c.addi     s4, 4
                  c.lui      s8, 4
                  c.addi     a2, 23
                  lui        a1, 344571
                  bltu       s10, t6, 988f
                  auipc      s2, 199215
                  c.addi     a3, -16
                  lui        zero, 58022
                  c.addi     a5, 14
                  auipc      a3, 625863
                  c.addi     t2, 14
                  auipc      a4, 689965
988:              c.addi     gp, 19
                  c.lui      t4, 22
                  c.srli     a4, 26
                  c.lui      a0, 29
                  lui        gp, 171972
                  c.slli     s3, 7
                  c.addi     a5, 19
                  c.addi     s2, -32
                  c.srai     a0, 26
                  divu       s10, gp, a7
                  c.srai     a1, 16
                  c.addi     s1, -17
                  c.srli     s0, 5
                  c.srli     a1, 23
                  auipc      zero, 420876
                  c.lui      s8, 26
                  c.srai     a0, 28
                  auipc      s8, 424396
                  c.addi     s2, 25
                  lui        a7, 271594
                  c.addi     s1, 5
                  bge        s8, ra, 1011f
                  auipc      s3, 111701
1011:             c.slli     t2, 25
                  c.addi     t5, 21
                  c.lui      s2, 21
                  c.addi     a5, -26
                  c.lui      s10, 5
                  c.lui      s9, 27
                  mulhu      s3, a2, a4
                  c.addi     gp, 14
                  beq        a7, t6, 1032f
                  auipc      s6, 397841
                  srli       t6, s0, 30
                  c.srli     a5, 9
                  lui        s7, 899350
                  fence.i
                  c.addi     s5, -29
                  c.slli     s10, 6
                  srai       a2, s2, 28
                  slli       a3, s10, 0
                  c.srai     s0, 28
                  c.addi     s4, -32
                  mul        gp, t1, tp
1032:             lui        a7, 66735
                  auipc      a1, 646217
                  c.addi     s4, -6
                  auipc      zero, 51508
                  c.addi     gp, 10
                  c.lui      s2, 7
                  c.addi     t5, -24
                  c.slli     s9, 12
                  srl        s11, sp, s4
                  c.addi     s4, -18
                  auipc      t3, 971276
                  c.srli     a3, 23
                  auipc      a1, 987132
                  xori       gp, a3, -67
                  c.lui      s7, 23
                  xori       a2, gp, -16
                  c.lui      s5, 21
                  c.addi     s9, -21
                  c.addi     t1, -31
                  c.slli     s5, 13
                  addi       s1, a5, -85
                  auipc      s11, 34531
                  auipc      a7, 38922
                  c.lui      a5, 18
                  c.addi     t5, -19
                  c.srai     a0, 18
                  mulhu      s10, t1, t1
                  c.lui      t6, 2
                  auipc      a7, 326963
                  lui        s9, 659275
                  c.srli     a4, 2
                  auipc      a2, 557043
                  auipc      t4, 755606
                  lui        a4, 877548
                  c.lui      s3, 31
                  fence
                  lui        s1, 945955
                  c.srai     s0, 16
                  c.addi     s8, 2
                  lui        s1, 404259
                  slt        s1, s10, s3
                  sltiu      t5, t6, 763
                  c.addi     s10, 2
                  srli       t5, a1, 2
                  c.addi     t5, -2
                  lui        t3, 830401
                  c.addi     s4, -6
                  lui        t5, 639418
                  ori        s7, a4, 27
                  c.slli     t4, 10
                  auipc      s8, 421192
                  c.srli     s1, 6
                  add        s4, ra, t5
                  c.srai     a5, 18
                  sltu       s9, a3, a5
                  c.slli     s8, 15
                  auipc      a3, 806516
                  c.addi     s11, -16
                  sll        s3, t4, s5
                  c.addi     s6, 20
                  lui        t5, 425495
                  c.nop
                  c.slli     a4, 14
                  c.li       a0, -10
                  c.srai     a3, 24
                  lui        s0, 50202
                  c.addi     s1, 24
                  c.or       a4, a4
                  divu       s10, s6, t6
                  la         s9, data_page_1+1793 #start riscv_load_store_rand_instr_stream_2
                  c.addi     s8, -1
                  c.addi     t1, 25
                  lhu        s5, -521(s9)
                  lbu        s11, 1539(s9)
                  andi       s1, a1, 115
                  lb         s4, 558(s9)
                  lbu        s1, -1574(s9)
                  lb         t1, 1378(s9)
                  lb         s3, 393(s9)
                  lb         s1, 2030(s9)
                  sh         t1, -801(s9)
                  sb         s10, -860(s9)
                  lh         a1, 933(s9)
                  ori        a4, a5, 783
                  c.addi     s11, 13
                  c.or       a2, a3
                  c.addi     t2, 18
                  sltu       a2, s8, s5
                  c.slli     t6, 5
                  lb         a3, 1210(s9)
                  sb         sp, -794(s9)
                  sltu       t5, sp, s7
                  rem        t1, a5, s6
                  lui        s10, 669637
                  sb         a5, 1072(s9)
                  lbu        zero, -138(s9)
                  sb         gp, 288(s9)
                  srli       s1, tp, 23
                  lbu        s7, 1888(s9)
                  c.lui      a6, 8
                  auipc      t6, 650938
                  c.addi     a0, 5
                  c.srai     a0, 19
                  c.slli     a2, 8
                  lui        a0, 797472
                  sb         a5, -1406(s9)
                  c.addi     a1, -21
                  lhu        s1, -779(s9)
                  c.srli     a0, 3
                  sltiu      t1, s8, 223
                  c.srli     s1, 30
                  sll        s1, t2, a2
                  sh         s9, 1215(s9)
                  c.srli     a3, 14
                  lbu        t5, -11(s9)
                  lh         t1, 243(s9)
                  lbu        t2, -68(s9) #end riscv_load_store_rand_instr_stream_2
                  c.addi     a6, -8
                  mulhsu     t5, s10, sp
                  lui        s0, 692758
                  lui        a4, 125600
                  auipc      a0, 1041390
                  c.addi     s0, -30
                  c.slli     a5, 31
                  c.andi     s1, 6
                  c.addi     s2, 30
                  c.addi     t1, -7
                  c.srai     a0, 19
                  bne        s7, tp, 1131f
                  lui        a0, 267637
                  c.addi     a6, 27
                  c.slli     s4, 16
                  c.srai     a4, 25
                  c.srai     a5, 26
                  c.addi     a1, -3
                  c.addi     a3, -11
                  c.srli     s0, 16
                  c.srai     a2, 10
                  xori       a3, s0, 793
                  c.lui      t1, 8
                  c.srai     a5, 1
                  c.slli     a0, 25
                  sltiu      a3, s1, 210
                  c.addi     s1, -14
                  c.srai     a2, 9
                  slti       s10, s6, -177
                  auipc      s3, 724233
1131:             lui        a4, 850562
                  c.or       a1, a1
                  c.lui      s1, 17
                  c.srli     a2, 12
                  c.addi     s4, 23
                  and        a1, s10, s3
                  lui        t5, 560417
                  c.slli     s10, 30
                  lui        s6, 816578
                  c.addi     t2, -25
                  lui        s3, 740890
                  c.srli     a0, 21
                  auipc      t2, 585615
                  c.slli     s10, 20
                  and        t4, s10, a1
                  lui        s3, 717872
                  c.and      s1, a0
                  auipc      t3, 36024
                  c.addi     s7, -6
                  srl        s5, s10, t0
                  c.addi     t1, 6
                  c.addi     s2, -19
                  c.bnez     s0, 1160f
                  lui        a6, 314327
                  auipc      zero, 234042
                  c.andi     a5, -14
                  div        a6, t6, a5
                  c.addi     t6, -13
                  divu       s6, t2, s9
1160:             c.addi     s10, 26
                  c.srli     a2, 25
                  auipc      s4, 57376
                  fence
                  auipc      s5, 533101
                  bne        a7, a3, 1171f
                  c.addi     s7, 8
                  mulhu      s8, t4, s4
                  c.addi     t5, -7
                  lui        s8, 132279
                  c.addi     s0, -28
1171:             c.addi     s4, -17
                  auipc      s4, 421931
                  c.addi     s2, 25
                  lui        a7, 961171
                  c.srai     a1, 19
                  c.addi     s2, 6
                  c.addi     a7, -30
                  c.addi     a1, -28
                  xor        t6, sp, zero
                  srli       a0, a7, 1
                  c.lui      s1, 14
                  slt        s7, t6, s2
                  c.srli     s0, 13
                  lui        s9, 150906
                  c.sub      a1, a4
                  c.srai     a2, 3
                  c.addi     s5, 2
                  c.addi     s5, -31
                  c.srai     a1, 16
                  c.srai     a2, 6
                  lw         ra, 4(sp)
                  lw         t0, 8(sp)
                  addi       sp, sp, 24
                  add        a0, s11, a6
                  c.srai     a0, 19
                  auipc      t3, 997852
                  c.addi     t6, 8
                  c.srai     a0, 17
1706:             ret
init_machine_mode:
                  li a0, 0x581900
                  csrw 0x300, a0 # MSTATUS
                  li a0, 0x0
                  csrw 0x304, a0 # MIE
                  mret
write_tohost:     
                  sw gp, tohost, t5

_exit:            
                  j write_tohost

.data
.pushsection .tohost,"aw",@progbits;
.align 6; .global tohost; tohost: .dword 0;
.align 6; .global fromhost; fromhost: .dword 0;
.popsection;
.align 4;
data_page_0:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
data_page_1:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
data_page_2:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
data_page_3:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
data_page_4:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
data_page_5:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
data_page_6:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
data_page_7:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
data_page_8:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
data_page_9:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
data_page_10:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
data_page_11:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
data_page_12:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
data_page_13:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
data_page_14:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
data_page_15:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
data_page_16:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
data_page_17:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
data_page_18:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
data_page_19:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.align 4;
.align 5
_user_stack_start:
.rept 4999
.4byte 0x0
.endr
_user_stack_end:
.4byte 0x0
_kernel_start: .align 12
smode_accessible_umode_program:beq        a0, tp, smode_accessible_umode_program_stack_p
smode_accessible_umode_program_stack_p:addi       sp, sp, -16
                  slti       s9, s2, 285
                  sw         ra, 4(sp)
                  sw         t0, 8(sp)
                  c.srli     a4, 27
                  c.and      a0, a2
                  c.mv       gp, a1
                  and        t2, zero, s10
                  c.addi     s5, 2
                  andi       s11, t0, -859
                  c.add      a3, a0
                  c.addi     a1, 26
                  slt        t1, s4, t2
                  c.addi     a7, -8
                  bltu       s7, ra, 21f
                  c.addi     s10, -31
                  auipc      a0, 708382
                  auipc      s9, 115845
                  lui        a4, 517715
                  c.srai     s1, 17
                  auipc      s6, 944678
                  c.srai     s0, 25
                  c.bnez     a2, 32f
                  c.lui      t5, 4
                  c.lui      s5, 9
                  auipc      t6, 1000076
                  c.srli     a2, 9
                  c.addi     t1, -28
                  addi       s5, gp, -263
                  nop
21:               c.addi     s7, -10
                  c.addi     s10, 27
                  c.srli     a4, 26
                  c.addi     t2, 4
                  c.lui      s3, 12
                  c.srai     s1, 4
                  lui        s8, 377736
                  lui        s10, 12008
                  slli       s8, a1, 29
                  c.srai     a3, 31
                  c.srli     a0, 5
32:               c.addi     s0, 5
                  lui        s10, 112575
                  c.slli     t6, 2
                  auipc      a1, 796427
                  c.addi     t2, -26
                  c.srli     s1, 26
                  blt        s1, a0, 40f
                  c.addi     s6, 13
40:               c.srai     s1, 18
                  c.slli     t6, 31
                  lui        s7, 732899
                  mulhu      a7, sp, zero
                  c.addi     t4, 21
                  c.li       s1, -16
                  c.slli     s2, 4
                  xori       a2, s6, -549
                  c.addi     a7, 5
                  c.addi     s9, 21
                  c.addi     a7, 9
                  c.addi     a4, -1
                  auipc      t4, 656888
                  c.addi     a5, -19
                  and        s11, sp, zero
                  c.slli     s4, 3
                  nop
                  c.addi     t5, -22
                  c.srli     a0, 5
                  c.slli     t3, 8
                  auipc      a2, 381305
                  lui        s1, 792774
                  c.slli     s0, 1
                  c.addi     a2, -29
                  c.addi     a6, 28
                  c.lui      a2, 7
                  c.beqz     s0, 73f
                  beq        s11, ra, 84f
                  c.srai     a3, 14
                  lui        s6, 471083
                  auipc      s1, 777529
                  bne        t0, t6, 86f
                  sltu       a4, a4, t6
73:               sub        t4, s5, t3
                  c.srai     a4, 15
                  c.srli     a0, 23
                  xori       a5, zero, -580
                  c.lui      s8, 16
                  c.srli     a0, 8
                  c.xor      a4, a1
                  c.addi     t5, 12
                  c.addi     t5, -30
                  auipc      s10, 201137
                  c.addi     s9, 27
84:               lui        s3, 30957
                  lui        zero, 30375
86:               c.addi     a5, 25
                  bne        tp, s7, 88f
88:               c.addi     gp, 22
                  or         zero, t3, s11
                  c.addi     s4, 24
                  c.slli     t3, 15
                  c.addi     s0, -24
                  c.addi     a4, 15
                  lui        s0, 622620
                  and        s2, a6, s7
                  auipc      t1, 321490
                  c.addi     a6, 22
                  c.srli     a2, 24
                  lui        s6, 326530
                  lui        s4, 364587
                  c.addi     s11, -20
                  lui        t4, 964916
                  auipc      a6, 761314
                  lui        a7, 819076
                  c.addi     t5, -9
                  c.addi     a3, 16
                  c.slli     s8, 23
                  div        s6, s0, s11
                  c.slli     a2, 2
                  c.srai     a2, 3
                  la         a7, kernel_data_page_0+1464 #start riscv_load_store_rand_instr_stream_0
                  sh         a7, 1774(a7)
                  auipc      t4, 522543
                  c.add      a0, s1
                  lbu        t6, -1456(a7)
                  c.srli     s1, 30
                  lb         t2, -809(a7)
                  lbu        s9, -935(a7)
                  c.addi     t2, 23
                  auipc      s3, 163451
                  c.srai     s0, 2
                  c.lui      s8, 6
                  lbu        s7, 1314(a7)
                  c.lui      gp, 26
                  remu       s5, a7, s0
                  lui        s10, 155164
                  lh         s9, 1158(a7)
                  lh         gp, -322(a7)
                  c.srli     a4, 22
                  c.addi     s5, 18
                  c.addi     s9, 18
                  auipc      zero, 689249
                  lui        t2, 988798
                  c.addi     a6, 15
                  auipc      t1, 409029
                  c.and      a4, s0
                  xori       a5, s8, -624
                  lh         s4, 26(a7)
                  sh         s10, 1120(a7)
                  c.srli     a4, 24
                  c.lui      t5, 22
                  c.lui      s1, 9
                  auipc      a5, 206043
                  c.addi     a0, -17
                  andi       t6, a1, -290
                  c.addi     a1, 9
                  sll        s1, s5, ra
                  lbu        s8, 1643(a7) #end riscv_load_store_rand_instr_stream_0
                  c.addi     s8, -9
                  auipc      s8, 410673
                  c.slli     s3, 13
                  mulh       s4, a2, gp
                  c.addi     s9, -20
                  c.lui      s11, 13
                  c.lui      a0, 26
                  c.li       t1, -27
                  c.andi     a2, 23
                  xori       s8, s1, -711
                  beq        s6, s8, 132f
                  c.srai     a4, 18
                  c.srai     a5, 28
                  xori       t1, a7, 270
                  sub        a3, s4, a0
                  sub        zero, s0, a2
                  beq        s8, s5, 132f
                  xor        t6, s3, tp
                  auipc      a4, 272489
                  c.srai     s0, 16
                  c.addi     t2, 27
132:              c.addi     s3, 22
                  srli       s3, a7, 17
                  c.addi     a0, 21
                  c.addi     a0, 29
                  auipc      t4, 248703
                  c.addi     s11, -16
                  sltiu      a2, s2, 648
                  c.addi     a7, 12
                  rem        s11, t1, s4
                  c.addi     s7, 27
                  divu       gp, s1, a6
                  srai       s10, a3, 21
                  c.addi     a3, -13
                  blt        s6, sp, 165f
                  auipc      a7, 314790
                  c.addi     t6, -22
                  slt        a6, t4, s7
                  auipc      a1, 146879
                  sra        t2, tp, s7
                  rem        s1, a6, sp
                  lui        s5, 688607
                  c.srli     s1, 15
                  c.srai     a2, 25
                  auipc      t3, 193745
                  c.lui      s11, 22
                  c.srai     a1, 12
                  lui        a5, 259171
                  c.slli     a3, 25
                  lui        s11, 241725
                  c.slli     s2, 13
                  c.addi     gp, 8
                  xor        s3, zero, a6
                  c.srai     s1, 18
165:              c.srli     a4, 11
                  auipc      t5, 444694
                  divu       s1, s4, s0
                  c.srai     s0, 23
                  xor        s11, a1, s10
                  c.lui      s11, 11
                  c.srai     a3, 21
                  c.addi     s0, -29
                  c.addi     s5, -1
                  c.slli     a4, 25
                  c.lui      a4, 26
                  lui        t6, 550287
                  c.addi     s1, 3
                  c.addi     a6, -21
                  c.addi     t3, 2
                  auipc      s1, 1011668
                  auipc      a5, 698744
                  c.lui      t5, 25
                  c.lui      t6, 13
                  c.srli     a5, 23
                  rem        a1, s0, s1
                  c.addi     s2, -18
                  c.addi     a3, 22
                  c.srli     s1, 2
                  sub        s5, ra, s0
                  c.srai     s1, 5
                  bge        a0, sp, 193f
                  sub        a2, s0, a4
193:              lui        s11, 962634
                  c.addi     s10, -11
                  or         zero, t3, s8
                  c.srai     a0, 12
                  la         a4, kernel_data_page_1+2745 #start riscv_load_store_rand_instr_stream_3
                  srli       s10, t6, 10
                  lbu        t4, 636(a4)
                  sb         s3, 373(a4)
                  c.srli     a2, 26
                  c.or       s1, s1
                  c.addi     s1, 6
                  c.addi     t5, 31
                  auipc      t2, 668207
                  c.addi     a7, 1
                  lh         a7, 985(a4)
                  c.srli     a0, 28
                  lb         zero, -1814(a4)
                  sltu       a1, t6, s2
                  lh         t5, -1843(a4)
                  lb         a6, 885(a4)
                  lb         zero, -1805(a4)
                  c.addi     a7, -15
                  c.slli     s11, 2
                  sb         s2, -1790(a4)
                  c.addi     s2, 31
                  fence
                  andi       a5, a2, 698
                  lhu        s0, -2039(a4)
                  c.srai     a5, 28
                  sb         t5, 509(a4)
                  mul        s9, s0, s2
                  c.addi     a2, 28
                  c.slli     s7, 27
                  c.addi     t4, -2
                  c.addi     s3, -20
                  c.addi     a3, 15
                  c.addi     t2, -1
                  lb         s8, -936(a4)
                  sb         t6, -34(a4)
                  c.srai     a0, 14
                  c.lui      a0, 4
                  sh         s9, -647(a4)
                  lui        s1, 645195
                  sh         s8, -297(a4)
                  lui        a6, 249393
                  lhu        t5, 1221(a4) #end riscv_load_store_rand_instr_stream_3
                  c.lui      t6, 18
                  c.lui      a6, 22
                  auipc      s11, 436868
                  c.slli     t5, 28
                  rem        t2, s5, a3
                  c.or       a3, a4
                  addi       t1, t6, -904
                  sll        s5, t6, t5
                  slli       s10, s8, 3
                  lui        s3, 645628
                  c.srai     a1, 19
                  c.addi     s3, 4
                  c.addi     s6, 25
                  la         a3, kernel_data_page_0+2537 #start riscv_load_store_rand_instr_stream_2
                  lbu        a0, 1533(a3)
                  lb         a5, -762(a3)
                  sb         s2, 144(a3)
                  c.or       a0, a3
                  sltu       a7, t0, gp
                  lbu        s4, -1956(a3)
                  add        s8, t1, tp
                  lb         s7, -1654(a3)
                  sb         s8, -765(a3)
                  lh         s4, -1997(a3)
                  lb         s1, 1002(a3)
                  c.slli     a6, 4
                  c.addi     t1, 6
                  sb         tp, -802(a3)
                  c.srai     a4, 23
                  lui        a4, 262474
                  lb         s10, -586(a3)
                  lbu        s1, 292(a3)
                  lb         s11, -757(a3)
                  sh         t3, -799(a3)
                  sw         t4, -105(a3)
                  lb         s0, 346(a3)
                  lbu        a0, -1971(a3)
                  c.addi     a2, -31
                  c.lui      s6, 14
                  lui        s8, 860298
                  lb         t3, 1418(a3) #end riscv_load_store_rand_instr_stream_2
                  lui        s1, 344664
                  auipc      a2, 904143
                  c.addi     t3, -21
                  c.addi     t5, -23
                  auipc      s11, 343901
                  add        s6, zero, a5
                  slti       a6, s4, 37
                  auipc      a1, 631189
                  c.srai     s1, 15
                  la         s7, kernel_data_page_1+2281 #start riscv_load_store_rand_instr_stream_1
                  c.addi     t4, -8
                  auipc      s6, 198280
                  auipc      s0, 800727
                  c.lui      s5, 19
                  auipc      a6, 728725
                  sb         sp, 268(s7)
                  c.slli     s5, 26
                  lb         zero, -652(s7)
                  c.addi     t4, -11
                  lb         a6, -214(s7)
                  sb         s10, 1668(s7)
                  c.srai     a1, 26
                  auipc      t1, 306634
                  c.mv       s3, s2
                  c.addi     a7, -14
                  c.addi     s8, 24
                  c.and      s1, s0
                  lbu        t1, 556(s7)
                  c.xor      a0, s1
                  lbu        t2, -1372(s7)
                  c.addi     s9, 24
                  sb         t0, 188(s7)
                  c.slli     s6, 11
                  sb         s1, -249(s7)
                  c.addi     t5, -14
                  c.li       a6, 21
                  sb         s8, -745(s7)
                  c.srai     a4, 15
                  auipc      s5, 597192
                  add        s5, a3, a3
                  lh         a7, -1005(s7)
                  auipc      zero, 349376
                  sub        a4, a6, a0
                  lbu        a3, 53(s7)
                  auipc      a1, 323523
                  c.addi     a0, 21
                  c.addi     s6, -6
                  lui        s10, 339222
                  c.addi     a6, 17
                  lh         s11, -1935(s7)
                  lbu        s8, -1008(s7)
                  lb         a4, -426(s7) #end riscv_load_store_rand_instr_stream_1
                  auipc      s7, 731599
                  lui        zero, 342309
                  c.addi     s9, -4
                  auipc      a2, 209561
                  auipc      s6, 172073
                  c.addi     t5, -2
                  lui        a3, 541333
                  andi       t2, s2, -735
                  c.lui      t4, 11
                  bge        s6, s9, 244f
                  auipc      s10, 988590
                  xori       s7, s2, 861
                  c.add      a2, a4
                  c.nop
                  auipc      s3, 618873
                  c.lui      s10, 30
                  auipc      a7, 411801
                  c.srai     a1, 5
                  auipc      s11, 94283
                  c.addi     s8, 12
                  c.srli     a3, 27
                  lui        s6, 391376
                  srli       a6, t1, 23
                  c.srli     a5, 20
                  auipc      t4, 249893
244:              c.sub      a5, a5
                  auipc      s1, 985670
                  c.lui      s0, 1
                  c.addi     a5, -8
                  c.addi     a2, 22
                  fence
                  c.addi     a3, 26
                  sub        gp, zero, t1
                  c.lui      a6, 15
                  c.srli     a2, 5
                  auipc      s3, 810267
                  auipc      a4, 372737
                  lui        t1, 173595
                  addi       s11, s9, 144
                  c.srli     a2, 1
                  lui        gp, 785757
                  c.srai     a2, 9
                  c.lui      t2, 11
                  c.addi     s3, 2
                  sltiu      t3, s1, 574
                  c.slli     t4, 21
                  lui        t3, 466465
                  slt        a2, s11, t5
                  c.xor      a3, a0
                  c.li       t3, 31
                  c.lui      t3, 2
                  div        a2, a1, tp
                  c.lui      s0, 12
                  lui        a1, 598810
                  c.addi     a1, 23
                  auipc      a2, 840977
                  c.addi     t5, -25
                  auipc      s0, 1013910
                  c.addi     s4, -2
                  c.lui      s5, 9
                  c.nop
                  srai       t2, s4, 30
                  c.xor      a5, a1
                  c.lui      a6, 18
                  divu       s9, zero, s4
                  lui        s2, 5037
                  bne        s8, t0, 305f
                  c.lui      s10, 4
                  c.lui      t1, 24
                  auipc      a0, 287641
                  c.slli     s6, 17
                  auipc      t5, 10161
                  rem        t5, t5, t0
                  xor        s0, s2, s6
                  c.srai     a1, 8
                  c.srai     s0, 23
                  c.add      a4, a2
                  auipc      s5, 941473
                  c.addi     a4, -15
                  c.addi     s0, 6
                  c.addi     s3, 27
                  lui        s5, 132551
                  c.srli     a4, 16
                  lui        a7, 455126
                  or         a5, a3, a2
                  add        t6, a6, a1
305:              c.addi     s8, 25
                  auipc      s7, 177074
                  add        a0, gp, s3
                  c.addi     s9, -27
                  lui        s7, 998327
                  auipc      s10, 334964
                  andi       t3, s4, 468
                  c.addi     a4, 10
                  c.addi     s10, -18
                  lui        t4, 540712
                  c.addi     t4, -3
                  c.xor      a0, s1
                  lui        t1, 756499
                  c.srli     a5, 22
                  c.srai     s0, 23
                  c.srai     s1, 3
                  c.srli     s1, 20
                  auipc      a1, 571505
                  c.addi     a4, -19
                  lui        s6, 901152
                  auipc      s0, 924399
                  auipc      s11, 115717
                  c.addi     s8, -4
                  c.srli     a2, 25
                  lui        t3, 94061
                  c.addi     s1, -20
                  lui        gp, 320155
                  c.srli     s0, 24
                  c.addi     a1, 3
                  c.srli     a1, 19
                  auipc      t1, 785078
                  c.addi     t4, -20
                  lui        a0, 792132
                  c.addi     t6, -19
                  c.addi     a5, -1
                  c.addi     s6, 3
                  bge        t1, a7, 345f
                  bltu       ra, s4, 362f
                  c.srli     a2, 15
                  c.add      a3, s1
345:              c.addi     t4, 14
                  slti       a3, t5, -305
                  lui        a5, 771065
                  sll        a3, t6, a4
                  lui        s5, 689013
                  bne        a5, t0, 365f
                  c.addi     s3, 2
                  auipc      a6, 611057
                  auipc      a4, 931667
                  c.addi     a3, 4
                  bge        s1, t1, 371f
                  auipc      a2, 990094
                  lui        s2, 217172
                  c.srli     a2, 14
                  lui        a7, 827276
                  c.addi     t2, 31
                  lui        s3, 536402
362:              fence
                  lui        a0, 496235
                  auipc      s10, 187410
365:              lui        a6, 81873
                  c.addi     t1, -26
                  c.add      a5, a1
                  c.addi     t3, -7
                  c.slli     s11, 2
                  c.slli     a3, 13
371:              c.srai     a4, 18
                  c.addi     s11, 19
                  auipc      a0, 806565
                  andi       s1, a4, 69
                  or         a7, tp, a7
                  auipc      s3, 602867
                  auipc      t2, 995397
                  c.addi     t4, -26
                  c.addi     t6, 5
                  c.slli     a4, 29
                  c.addi     a1, -31
                  c.lui      t1, 23
                  c.addi     s10, 1
                  lui        s8, 434256
                  c.lui      t5, 7
                  c.slli     s2, 11
                  xori       s7, tp, -60
                  c.srai     a1, 8
                  c.addi     s4, -6
                  auipc      a3, 666992
                  c.slli     a3, 23
                  c.lui      t5, 26
                  lui        t2, 540186
                  c.lui      t5, 10
                  sll        s7, s1, t2
                  c.and      a2, s0
                  c.lui      s5, 2
                  auipc      a2, 424092
                  c.slli     a3, 1
                  lw         ra, 4(sp)
                  lw         t0, 8(sp)
                  c.srai     a4, 16
                  sub        s6, t6, t3
                  c.lui      gp, 3
                  addi       sp, sp, 16
                  lui        a6, 359866
568:              ret
smode_program:    c.lui      s3, 22
                  addi       sp, sp, -28
                  sw         ra, 4(sp)
                  c.srai     a4, 12
                  sw         t0, 8(sp)
                  auipc      s5, 1037305
                  sub        s0, tp, t5
                  c.srai     a2, 7
                  c.addi     t4, 23
                  lui        t6, 970756
                  lui        t5, 775092
                  mulhu      s7, s0, t5
                  srl        a0, t0, t3
                  c.addi     a0, -8
                  blt        s9, a1, 13f
                  lui        s4, 826922
                  auipc      s3, 476110
                  c.srli     s0, 3
                  auipc      s2, 4639
13:               c.lui      a7, 22
                  c.addi     t6, -24
                  auipc      s11, 102019
                  c.addi     s2, 3
                  sra        s8, t5, t4
                  sub        t5, tp, s1
                  c.addi     s8, -24
                  c.addi     a6, 10
                  c.addi     t1, -28
                  c.addi     s7, 11
                  lui        s9, 29154
                  c.lui      t3, 20
                  c.addi     a7, -23
                  auipc      s9, 216368
                  c.srli     a5, 1
                  c.addi     s3, -15
                  lui        s7, 675665
                  lui        s10, 542476
                  c.srai     a3, 16
                  c.srli     a1, 13
                  c.slli     t6, 25
                  auipc      a0, 56741
                  auipc      s0, 473303
                  c.sub      a4, a5
                  c.srli     a0, 25
                  auipc      s5, 674872
                  bne        a2, t5, 46f
                  bge        a2, zero, 51f
                  c.addi     a6, 20
                  c.addi     a3, 24
                  c.add      a5, a2
                  c.addi     s3, -7
                  c.slli     t3, 4
46:               c.addi     s7, 5
                  c.srli     a3, 16
                  c.addi     s6, -7
                  sltu       a6, a7, a1
                  auipc      a3, 135879
51:               c.addi     s8, -20
                  auipc      a4, 186409
                  c.slli     t2, 13
                  c.addi     a2, -8
                  c.addi     gp, 29
                  c.addi     s5, 10
                  sub        t5, s6, zero
                  c.srli     a1, 9
                  c.addi     a0, 26
                  c.slli     s9, 8
                  c.srai     s1, 30
                  lui        s11, 94082
                  lui        s10, 177632
                  c.addi     s5, 19
                  c.addi     s6, 4
                  c.beqz     a1, 81f
                  c.srli     a3, 6
                  fence.i
                  c.lui      t6, 1
                  sll        a5, s7, s11
                  c.addi     a4, -19
                  bgeu       a1, s5, 76f
                  lui        a6, 692146
                  c.slli     a2, 25
                  c.addi     s2, 20
76:               c.srai     s0, 14
                  c.srai     s0, 27
                  c.srli     a5, 24
                  c.addi     t2, -28
                  c.lui      s10, 23
81:               c.addi     s10, -19
                  c.addi     t5, -8
                  c.addi     s9, 15
                  c.slli     s5, 29
                  c.or       s1, a1
                  rem        a3, t5, s6
                  auipc      t1, 161159
                  c.slli     a1, 11
                  bgeu       a3, s9, 98f
                  c.addi     s6, 10
                  c.srli     a4, 25
                  c.slli     s4, 16
                  c.and      a4, a2
                  c.addi     s9, 2
                  mulh       t6, a6, gp
                  c.addi     t1, 18
                  c.addi     gp, -10
98:               c.slli     a5, 18
                  sltiu      s0, t4, -796
                  lui        t4, 725426
                  srli       s5, a7, 16
                  c.addi     t5, 17
                  c.slli     a6, 1
                  auipc      a0, 9977
                  remu       a3, a0, s11
                  xor        a5, zero, a3
                  lui        s10, 352214
                  c.lui      t3, 30
                  c.slli     a0, 21
                  c.addi     a4, 1
                  c.addi     a3, 30
                  lui        t6, 766527
                  c.srli     a3, 29
                  c.addi     a3, -14
                  nop
                  and        a3, s5, a5
                  c.addi     s1, -21
                  bltu       t5, s4, 123f
                  c.lui      s8, 14
                  ori        t5, t6, -164
                  sltu       s11, t5, t3
                  c.addi     a4, 21
123:              c.srai     s1, 21
                  c.srli     a5, 31
                  c.srli     a1, 8
                  andi       a0, a1, 633
                  divu       s5, a2, s3
                  fence
                  auipc      a3, 462317
                  c.slli     s2, 26
                  lui        s5, 752404
                  auipc      t2, 374602
                  la         s8, kernel_data_page_0+2002 #start riscv_load_store_rand_instr_stream_3
                  sb         a2, 391(s8)
                  c.slli     t2, 31
                  c.srai     a0, 26
                  lbu        t4, -1132(s8)
                  c.lui      a7, 25
                  c.addi     s2, 13
                  lbu        s5, 1413(s8)
                  auipc      a4, 546436
                  rem        t6, s5, a7
                  c.addi     s5, -27
                  lw         s3, -722(s8)
                  c.addi     s3, -10
                  c.and      a3, s0
                  auipc      a3, 730366
                  sb         zero, 1821(s8)
                  c.lui      a3, 22
                  lb         a6, -851(s8)
                  lb         s0, -1828(s8)
                  sw         gp, 1426(s8)
                  c.lui      s1, 5
                  lw         a1, 1110(s8)
                  lbu        t4, 803(s8)
                  lb         t1, 1700(s8)
                  c.addi     a4, -8
                  lb         a6, 1241(s8)
                  sb         s7, -1739(s8)
                  c.addi     a5, -4
                  c.addi     s7, -2
                  c.srli     a0, 11
                  lhu        s4, -1020(s8)
                  lbu        s2, -657(s8)
                  sltiu      t1, s1, 336
                  lbu        t1, 69(s8)
                  lbu        s11, 277(s8)
                  c.addi     s0, -31
                  sh         sp, -1556(s8)
                  lui        s7, 619794
                  lb         s2, 277(s8)
                  xor        a7, a5, s7
                  c.srli     s0, 10
                  c.srli     a1, 13
                  lb         a0, -1925(s8) #end riscv_load_store_rand_instr_stream_3
                  c.addi     t4, -20
                  bge        s6, zero, 136f
                  c.bnez     a2, 142f
136:              beq        sp, s2, 137f
137:              c.srai     a1, 31
                  c.srai     s0, 25
                  slli       s3, zero, 8
                  c.addi     a5, -11
                  lui        s3, 5433
142:              auipc      t2, 297040
                  auipc      s2, 212751
                  c.slli     s1, 26
                  c.addi     a6, -5
                  c.slli     a0, 13
                  lui        a1, 888920
                  c.addi     a5, -18
                  c.slli     s10, 13
                  c.addi     s1, -26
                  c.addi     s10, -20
                  lui        a4, 1046828
                  xori       t5, a6, -219
                  c.addi     s7, 15
                  c.beqz     a2, 165f
                  c.addi     s2, -19
                  c.or       a5, a2
                  c.addi     a6, -25
                  c.addi     a1, 4
                  c.slli     gp, 30
                  c.addi     s10, 1
                  lui        s10, 928340
                  slli       s6, s10, 1
                  auipc      t1, 321084
165:              c.addi     a2, 10
                  slt        a5, tp, t4
                  sub        s3, tp, sp
                  auipc      s5, 168951
                  lui        s3, 605837
                  c.beqz     s0, 176f
                  auipc      gp, 731510
                  c.addi     s1, -17
                  c.addi     a7, 23
                  auipc      t4, 840696
                  c.srai     a3, 12
176:              or         t6, tp, s11
                  lui        s3, 899602
                  rem        s3, t6, t0
                  c.addi     s10, 19
                  auipc      a0, 863481
                  auipc      s5, 844234
                  c.srli     a1, 28
                  sra        t4, s5, s9
                  c.srai     a5, 24
                  sra        s3, s7, s9
                  lui        s3, 142006
                  c.addi     a7, -17
                  lui        s2, 617024
                  auipc      s10, 691485
                  lui        a4, 343649
                  divu       a3, a4, gp
                  c.addi     a1, -26
                  c.addi     a7, 15
                  fence
                  sub        a2, a6, a4
                  auipc      s6, 285892
                  c.srai     a5, 20
                  c.slli     a5, 8
                  auipc      t6, 358266
                  c.addi     a5, -9
                  c.add      a3, s1
                  beq        s2, t3, 213f
                  c.slli     a5, 1
                  c.addi     a3, 25
                  c.srai     a5, 20
                  c.addi     s9, -21
                  auipc      s5, 1022214
                  c.addi     t3, -25
                  lui        a4, 111769
                  c.lui      s1, 25
                  c.srli     a1, 30
                  c.or       s1, s0
213:              c.slli     s0, 20
                  auipc      zero, 274584
                  c.addi     s8, 7
                  c.addi     t2, 26
                  c.addi     s1, -21
                  c.addi     s2, -16
                  fence
                  auipc      s11, 878135
                  bge        s10, t4, 237f
                  auipc      s0, 439613
                  mul        s7, s9, a1
                  mul        s8, a7, s5
                  lui        s1, 450101
                  c.srai     a3, 10
                  c.addi     t5, -20
                  c.addi     t1, -21
                  c.addi     a1, 27
                  mulhu      s10, a3, ra
                  c.addi     t3, -28
                  mulhsu     t1, s3, t2
                  c.addi     s0, 3
                  srli       t4, a6, 13
                  c.slli     t4, 20
                  lui        s11, 455114
237:              c.srli     a2, 3
                  c.addi     a2, 30
                  c.addi     a3, -14
                  xor        s3, s10, s6
                  c.srli     a4, 25
                  c.slli     a1, 1
                  c.srli     a3, 20
                  c.lui      a1, 30
                  c.addi     s9, 1
                  sra        s4, s9, t2
                  lui        t3, 396236
                  auipc      s2, 707596
                  c.srli     a5, 10
                  c.addi     a3, 24
                  c.lui      s0, 7
                  c.srai     a4, 6
                  la         a5, kernel_data_page_0+1787 #start riscv_load_store_rand_instr_stream_0
                  lb         s10, 1612(a5)
                  lbu        s4, 242(a5)
                  c.slli     a0, 10
                  nop
                  c.srli     a3, 3
                  c.lui      a6, 3
                  c.lui      t3, 22
                  c.addi     s6, 20
                  lui        a0, 508582
                  c.addi     s0, -10
                  lbu        s7, -1430(a5)
                  c.srli     a4, 10
                  lbu        s7, -1734(a5)
                  lui        s10, 58698
                  auipc      s1, 119437
                  sh         a5, 467(a5)
                  c.lui      s2, 23
                  lhu        s1, 113(a5)
                  div        s10, sp, a1
                  sb         t2, -1488(a5)
                  nop
                  sh         gp, -1509(a5)
                  lb         a7, 1036(a5)
                  c.addi     a7, -26
                  c.addi     s4, -8
                  lhu        a6, -709(a5)
                  or         s8, s7, s7
                  c.slli     gp, 5
                  c.addi     s8, -5
                  lui        s9, 447944
                  c.srai     s1, 20
                  c.srli     a2, 5
                  c.slli     s5, 28
                  c.srai     s0, 27
                  auipc      s11, 904047
                  c.srai     a3, 15
                  lbu        s11, 1009(a5)
                  lb         s3, 1929(a5) #end riscv_load_store_rand_instr_stream_0
                  lui        a4, 929818
                  c.srli     a5, 27
                  c.bnez     s1, 274f
                  c.addi     a4, 22
                  c.addi     s1, -7
                  c.addi     t2, -31
                  c.li       s10, 0
                  lui        s6, 89265
                  c.addi     a0, -14
                  c.srai     s1, 24
                  c.addi     s8, -13
                  lui        t6, 451359
                  c.and      a5, s0
                  bgeu       tp, t0, 270f
                  lui        t4, 580146
                  c.addi     a6, -12
                  c.addi     t2, -5
270:              c.addi     t2, -22
                  c.addi     t3, 7
                  c.srli     s1, 29
                  c.addi     s4, -3
274:              bge        s6, sp, 291f
                  c.addi     s1, 12
                  auipc      s6, 1038806
                  c.addi     s6, -4
                  c.addi     s4, 16
                  auipc      s0, 92163
                  lui        a2, 757430
                  remu       s10, gp, s1
                  lui        t6, 486181
                  c.srai     a5, 16
                  c.addi     t4, -12
                  c.addi     s9, 6
                  c.lui      gp, 23
                  lui        a0, 824894
                  auipc      a2, 726770
                  c.addi     a6, 29
                  c.lui      a6, 29
291:              c.addi     t4, 1
                  c.srai     a4, 16
                  lui        t4, 23609
                  sltiu      s5, s2, 656
                  c.srai     s0, 7
                  la         s5, kernel_data_page_1+1220 #start riscv_load_store_rand_instr_stream_1
                  lui        s10, 954890
                  c.and      s1, a2
                  lui        a5, 485728
                  lw         s7, -948(s5)
                  sw         a6, 1804(s5)
                  auipc      t6, 993810
                  lb         s2, 1523(s5)
                  sb         t1, 715(s5)
                  sb         t6, 775(s5)
                  c.addi     a1, 15
                  auipc      s9, 877148
                  lhu        s9, 752(s5)
                  c.addi     s3, -26
                  c.and      s1, a5
                  mulhu      s1, s6, s7
                  lbu        t5, -611(s5)
                  sb         a2, 1720(s5)
                  auipc      a6, 773986
                  srai       s9, tp, 21
                  c.or       s0, a4
                  c.addi     s7, 28
                  or         t2, zero, tp
                  c.xor      a1, a4
                  auipc      t3, 311531
                  lh         t1, -672(s5)
                  lh         s10, 1552(s5)
                  lb         a6, 245(s5)
                  c.mv       s3, s0
                  sra        t1, s3, t0
                  auipc      a4, 510224
                  lhu        s11, -1082(s5)
                  lui        s9, 77963
                  auipc      t4, 572054
                  lbu        s2, -483(s5)
                  auipc      s3, 902637
                  sb         ra, 2023(s5)
                  c.srli     a2, 10
                  sltiu      a7, a5, 78
                  c.srai     a3, 29
                  sb         s0, 137(s5) #end riscv_load_store_rand_instr_stream_1
                  auipc      t1, 139925
                  lui        s1, 715750
                  auipc      t4, 752277
                  lui        s2, 422756
                  c.lui      t4, 5
                  remu       zero, a0, s0
                  lui        s2, 399740
                  slli       s7, a5, 23
                  blt        t3, a0, 311f
                  lui        t6, 1047014
                  c.lui      s9, 25
                  sll        s7, s8, s5
                  c.srli     s0, 16
                  c.addi     a3, -3
                  c.lui      s3, 19
311:              slli       a6, s6, 2
                  c.srai     a3, 19
                  bge        s5, s10, 329f
                  c.addi     t4, -6
                  c.addi     a0, 19
                  c.srli     a1, 27
                  auipc      a0, 68806
                  c.addi     a4, -13
                  lui        t1, 967159
                  c.addi     a5, 2
                  c.srai     a3, 24
                  andi       a2, t5, 552
                  c.addi     s1, 27
                  nop
                  c.addi     s9, 30
                  lui        s5, 81954
                  c.nop
                  c.addi     a5, -26
329:              xor        s8, t2, gp
                  slli       s9, a1, 24
                  c.addi     s7, 24
                  ori        a3, s3, -85
                  c.addi     t1, 4
                  c.xor      a2, a0
                  add        s7, ra, a4
                  slt        gp, s10, s10
                  c.srli     a5, 9
                  c.slli     s8, 3
                  lui        a4, 1023096
                  c.addi     a4, -29
                  c.li       t5, -10
                  lui        s7, 981347
                  auipc      t3, 253618
                  div        a6, t5, gp
                  auipc      t4, 196771
                  auipc      s5, 741845
                  div        a7, s3, a7
                  auipc      s7, 224360
                  lui        s0, 549848
                  c.srai     a3, 9
                  or         s1, s8, t6
                  c.addi     s6, -14
                  c.addi     t6, -14
                  lui        t4, 236555
                  c.srai     a5, 6
                  lui        s7, 311862
                  sub        s4, a6, t5
                  c.addi     s7, -4
                  c.lui      s4, 2
                  and        t1, t6, s9
                  lui        a0, 75957
                  c.addi     a5, -30
                  auipc      zero, 175502
                  lui        a2, 466881
                  lui        s2, 24063
                  divu       t6, s5, a4
                  la         s10, kernel_data_page_0+2143 #start riscv_load_store_rand_instr_stream_2
                  rem        t2, t5, t4
                  xor        gp, a6, gp
                  sra        t5, s7, t6
                  nop
                  auipc      a4, 58689
                  c.srli     a1, 17
                  sb         gp, -2044(s10)
                  c.lui      a0, 17
                  lw         a7, 1489(s10)
                  auipc      s5, 203657
                  sb         tp, -1262(s10)
                  sh         s8, 1413(s10)
                  lb         a2, -1477(s10)
                  lbu        a4, 1910(s10)
                  sll        a0, a0, t4
                  auipc      s9, 890883
                  lb         t4, 1888(s10)
                  lb         t4, -1603(s10)
                  sh         s11, 787(s10)
                  lbu        s3, -1113(s10)
                  c.srai     a0, 1
                  sh         ra, 1753(s10)
                  lb         a0, -1614(s10)
                  c.addi     s6, 15
                  lb         gp, 1677(s10)
                  lhu        s3, -1493(s10)
                  c.addi     a5, -1
                  sb         s8, 1008(s10)
                  c.or       a2, s0
                  c.addi     t1, 19
                  srl        a2, s7, t2
                  lhu        s1, 359(s10)
                  auipc      s11, 1028714
                  fence.i
                  lb         s6, -1546(s10)
                  sb         s3, 880(s10)
                  lbu        gp, 1260(s10) #end riscv_load_store_rand_instr_stream_2
                  sra        gp, a5, a7
                  c.lui      s10, 11
                  auipc      t2, 556397
                  c.addi     a3, -24
                  auipc      s8, 321650
                  c.addi     t1, -7
                  c.addi     a3, 13
                  c.lui      a3, 21
                  c.addi     a4, -8
                  c.addi     gp, -16
                  c.lui      t5, 16
                  bge        zero, zero, 380f
                  sra        gp, s2, s8
380:              addi       a2, s10, -862
                  c.srli     a2, 21
                  auipc      a1, 680635
                  c.srli     a3, 4
                  divu       a6, s6, t3
                  auipc      gp, 679090
                  lui        s4, 1029578
                  c.srli     a2, 26
                  c.srai     s0, 14
                  c.addi     t4, 15
                  c.srli     s1, 3
                  c.srai     a3, 31
                  c.addi     a5, -10
                  remu       s8, gp, t0
                  c.addi     a1, 20
                  c.lui      s4, 23
                  lui        s1, 638756
                  c.addi     s3, -11
                  c.addi     a2, 12
                  slli       a6, s6, 4
                  c.srai     a3, 11
                  lui        a6, 408342
                  auipc      gp, 113507
                  lw         ra, 4(sp)
                  c.srai     a3, 1
                  lw         t0, 8(sp)
                  addi       sp, sp, 28
                  c.srli     a5, 20
                  or         t3, s10, t5
                  c.srli     a3, 30
                  sltiu      a4, t6, 46
                  c.srli     a1, 12
579:              ret
smode_ls_umem_program:bne        a4, s3, smode_ls_umem_program_stack_p
                  auipc      s6, 319544
smode_ls_umem_program_stack_p:addi       sp, sp, -56
                  sw         ra, 4(sp)
                  c.slli     a6, 15
                  sw         t0, 8(sp)
                  srl        s8, zero, ra
                  c.lui      t2, 27
                  c.srai     a4, 11
                  c.addi     a0, -1
                  c.addi     s9, -31
                  lui        s9, 889383
                  c.slli     s8, 20
                  c.lui      s4, 19
                  c.slli     a0, 16
                  auipc      s11, 324830
                  lui        t4, 62171
                  c.srai     a4, 25
                  fence.i
                  mulhu      zero, a4, t0
                  c.srli     a1, 29
                  c.addi     a5, 10
                  c.slli     a6, 21
                  c.addi     s8, -25
                  c.addi     a6, -23
                  c.addi     a5, 28
                  c.addi     a3, 2
                  c.slli     s2, 13
                  c.srli     a4, 19
                  c.add      a1, a2
                  auipc      gp, 970329
                  lui        a6, 424558
                  c.addi     a3, 30
                  c.addi     s6, 17
                  lui        a5, 384221
                  c.addi     t5, 10
                  lui        s8, 853827
                  c.addi     a3, 4
                  c.slli     a1, 5
                  c.addi     s9, -4
                  c.mv       s7, s2
                  c.lui      gp, 17
                  fence.i
                  c.slli     a1, 23
                  lui        zero, 836261
                  blt        s7, ra, 43f
                  c.lui      t5, 25
                  srai       s11, t4, 10
                  div        gp, s8, a5
                  addi       s8, t4, -253
                  c.addi     s6, -11
43:               bltu       a6, a2, 57f
                  c.srai     s0, 20
                  auipc      s0, 534619
                  c.andi     a4, -11
                  c.addi     s1, 5
                  c.srai     s1, 21
                  c.srai     a1, 31
                  slt        a3, a3, ra
                  c.addi     s1, 23
                  c.srli     a4, 4
                  c.slli     a2, 14
                  c.addi     s6, 4
                  bgeu       t1, gp, 74f
                  lui        t6, 16790
57:               c.slli     t4, 22
                  c.addi     s10, 5
                  lui        a6, 277040
                  c.slli     t3, 28
                  c.slli     a0, 24
                  slti       a3, s3, -820
                  lui        s0, 208965
                  c.srai     a3, 17
                  auipc      a7, 98462
                  auipc      a0, 1023559
                  c.addi     a0, 16
                  c.addi     s5, 9
                  sltu       a6, a7, s10
                  mulhu      s8, a6, zero
                  lui        t4, 1000117
                  lui        a5, 436226
                  c.addi     t5, -23
74:               c.srai     a2, 18
                  lui        s6, 1037687
                  div        s6, a0, a0
                  c.addi     a2, 7
                  sltiu      s1, a5, -906
                  sra        s1, t6, s6
                  c.addi     s9, -30
                  auipc      a7, 733681
                  c.add      a0, a1
                  c.addi     t5, 14
                  c.addi     t3, -26
                  auipc      s7, 308369
                  xor        s9, t1, t0
                  c.add      a2, a2
                  lui        t1, 1025608
                  lui        t4, 863360
                  c.addi     s5, 13
                  c.srai     a4, 30
                  auipc      t6, 631840
                  ori        s5, s7, -462
                  fence
                  c.slli     a2, 2
                  c.addi     a4, 2
                  c.srai     s0, 30
                  c.addi     s7, 13
                  c.srai     a1, 17
                  auipc      s5, 123438
                  auipc      t3, 642928
                  lui        s4, 761911
                  divu       s4, a2, t3
                  c.addi     s0, 15
                  c.srli     a5, 29
                  c.srai     a2, 1
                  auipc      a0, 1039052
                  auipc      s3, 590015
                  divu       t3, sp, t4
                  mulhu      a1, s11, gp
                  c.srli     a3, 27
                  nop
                  sltiu      s4, zero, 306
                  mul        s3, gp, s10
                  lui        t3, 205731
                  la         s6, kernel_data_page_0+1184 #start riscv_load_store_rand_instr_stream_1
                  lhu        t4, -146(s6)
                  lui        t6, 569171
                  c.addi     s7, -15
                  lw         a2, -668(s6)
                  c.srli     a4, 27
                  c.srai     a5, 3
                  lui        s3, 935624
                  c.or       a2, s1
                  lbu        t2, -886(s6)
                  sll        t1, a6, s0
                  nop
                  c.slli     s0, 8
                  srai       t2, s3, 17
                  c.lui      t6, 3
                  lui        s11, 293045
                  lb         a0, -1119(s6)
                  lhu        s1, -1022(s6)
                  c.srai     a4, 25
                  lbu        t2, 767(s6)
                  c.lui      s11, 16
                  c.slli     t2, 21
                  lui        s5, 728792
                  addi       a6, a0, -757
                  c.addi     gp, 25
                  auipc      t6, 84758
                  lh         t2, 1608(s6)
                  sb         a0, 207(s6)
                  c.addi     s4, 7
                  lb         s9, 1954(s6)
                  addi       s2, a4, -353
                  c.srli     s0, 12
                  sb         t3, 2039(s6)
                  c.addi     s8, -27
                  lb         a6, 432(s6)
                  srli       a4, s6, 19
                  lbu        a6, 1630(s6)
                  c.addi     s0, -23
                  ori        s5, s1, 497
                  sb         t5, -319(s6)
                  c.addi     s1, -14
                  c.srli     a5, 31
                  lb         t2, 1298(s6) #end riscv_load_store_rand_instr_stream_1
                  lui        s4, 556939
                  auipc      s0, 130454
                  auipc      s10, 391449
                  c.addi     t3, -16
                  c.slli     a7, 17
                  auipc      a7, 595694
                  c.slli     t3, 27
                  c.slli     s5, 16
                  auipc      a2, 563380
                  lui        s10, 108975
                  blt        s4, s2, 127f
127:              c.addi     a2, 1
                  c.srai     a5, 13
                  c.srli     a4, 1
                  c.addi     a3, -1
                  andi       s3, s5, -302
                  c.slli     a1, 28
                  lui        t3, 53241
                  c.lui      t4, 11
                  c.or       a5, a4
                  c.addi     a6, 2
                  lui        s1, 832189
                  lui        s9, 73927
                  c.addi     a3, -27
                  c.addi     s7, -15
                  lui        a7, 700114
                  c.srli     a4, 17
                  sra        s0, s1, s10
                  c.addi     t5, 1
                  c.slli     a5, 12
                  andi       a5, s6, -985
                  bgeu       gp, t6, 167f
                  addi       a2, a2, -607
                  auipc      s11, 503040
                  c.addi     t4, -1
                  lui        a3, 436025
                  c.addi     t5, -15
                  c.addi     gp, -17
                  c.mv       s10, tp
                  c.srli     a1, 4
                  c.srai     s1, 30
                  c.addi     a1, -18
                  c.addi     t3, 24
                  auipc      a2, 113320
                  c.lui      gp, 19
                  fence
                  c.addi     s10, -9
                  sll        s7, s4, s0
                  c.lui      t5, 24
                  lui        s2, 872195
                  c.srli     a1, 17
167:              lui        t5, 588025
                  srl        s0, a6, a1
                  c.srli     a3, 20
                  xor        zero, a6, t2
                  lui        s8, 596859
                  c.lui      a7, 8
                  auipc      a6, 532888
                  auipc      t4, 258271
                  auipc      s6, 366145
                  c.addi     s3, 26
                  c.lui      a4, 13
                  auipc      s6, 66244
                  lui        s9, 221853
                  c.addi     a1, 13
                  auipc      s3, 228780
                  c.addi     a7, -17
                  c.slli     s8, 18
                  remu       s6, ra, zero
                  c.slli     t4, 31
                  c.addi     s11, -21
                  c.slli     t6, 12
                  c.addi     s10, -22
                  srai       a7, t5, 16
                  c.addi     t3, -15
                  c.srli     a3, 5
                  bne        gp, t1, 205f
                  c.addi     a3, 3
                  c.addi     t4, 22
                  c.slli     s11, 11
                  c.addi     s11, 13
                  c.srli     a0, 21
                  c.addi     gp, 24
                  c.addi     t4, -21
                  c.srai     a0, 27
                  divu       s8, t3, s5
                  sra        s11, a4, a2
                  lui        a0, 559336
                  auipc      s4, 862930
                  la         s3, kernel_data_page_0+1250 #start riscv_load_store_rand_instr_stream_0
                  sltiu      s5, zero, 678
                  c.addi     s9, -15
                  lbu        a6, 1620(s3)
                  lw         s9, 1794(s3)
                  lbu        gp, 1533(s3)
                  and        zero, t6, s11
                  c.addi     s5, -12
                  lb         a0, 1527(s3)
                  sb         a6, 1129(s3)
                  auipc      s4, 275900
                  lui        s8, 768375
                  c.add      a5, a0
                  c.lui      s8, 12
                  sb         s10, -1153(s3)
                  sh         ra, 818(s3)
                  lb         s8, 1432(s3)
                  auipc      s6, 515841
                  c.slli     a6, 28
                  sb         s4, -229(s3)
                  lbu        s5, 555(s3)
                  c.srai     a1, 9
                  c.addi     s4, 24
                  c.srai     s0, 24
                  c.srli     a1, 22
                  c.lui      t5, 14
                  lui        a1, 985078
                  lb         s0, 532(s3)
                  c.addi     a1, -28
                  remu       s5, a4, t0
                  lbu        s8, 796(s3)
                  ori        s7, t1, 159
                  lbu        t2, -55(s3)
                  lb         t6, 1899(s3)
                  lui        t5, 70725
                  lh         a4, 1828(s3)
                  lbu        a0, 1680(s3)
                  lbu        a1, 1496(s3)
                  lhu        a2, 236(s3)
                  c.addi     a6, -3
                  c.slli     s11, 3
                  lb         a7, -435(s3)
                  c.addi     a6, -21
                  c.addi     s9, -23
                  c.addi     s0, -3
                  lbu        a6, 1465(s3) #end riscv_load_store_rand_instr_stream_0
205:              c.addi     t6, -17
                  lui        a3, 323779
                  beq        s6, s8, 208f
208:              auipc      t3, 300808
                  lui        zero, 182377
                  bne        zero, a7, 224f
                  divu       a5, s8, t2
                  auipc      zero, 425330
                  c.addi     t1, 20
                  bne        s1, s8, 229f
                  lui        s7, 885352
                  fence.i
                  c.addi     t1, -27
                  sltu       s1, s10, a3
                  lui        s0, 387937
                  c.andi     a3, -12
                  lui        s10, 159508
                  auipc      t5, 198946
                  sltiu      a1, a4, 734
224:              auipc      t1, 405215
                  xori       s3, s10, -109
                  andi       zero, a2, 567
                  c.addi     s9, -11
                  c.addi     a3, 9
229:              lui        s6, 879168
                  lui        t3, 139610
                  c.lui      s7, 16
                  auipc      s8, 375273
                  addi       s10, s6, -275
                  c.srli     a2, 22
                  auipc      a0, 292090
                  c.addi     s4, -13
                  c.addi     a0, -12
                  c.addi     a3, -20
                  c.addi     s3, 24
                  srai       s3, s5, 10
                  lui        s7, 378631
                  blt        t3, a4, 244f
                  c.addi     gp, -29
244:              lui        a5, 1036742
                  lui        s6, 310929
                  c.lui      s8, 19
                  c.srli     a2, 20
                  c.addi     t1, -2
                  c.addi     s5, -23
                  c.addi     s7, -3
                  lui        a0, 1002582
                  lui        a3, 130125
                  c.addi     t4, -28
                  sll        s1, s6, s0
                  mul        s2, s4, a0
                  c.addi     t3, 28
                  c.addi     s7, 19
                  lui        a6, 388435
                  lui        s2, 681049
                  c.srai     a1, 15
                  c.slli     a1, 21
                  mul        s10, s7, t0
                  c.srai     s0, 22
                  lui        a4, 368207
                  remu       a7, a5, t5
                  c.and      a4, s1
                  div        s5, s6, zero
                  c.srai     a1, 23
                  auipc      a3, 102118
                  c.addi     s10, -14
                  c.addi     a5, -10
                  auipc      s4, 858449
                  c.addi     t2, -25
                  c.addi     t6, 23
                  divu       a0, s6, s1
                  auipc      a5, 508030
                  c.slli     a7, 1
                  c.srli     a5, 30
                  c.addi     t6, -23
                  c.add      s1, a5
                  c.addi     a3, 26
                  c.srli     a0, 17
                  fence
                  ori        s5, s3, -752
                  c.srai     s0, 9
                  c.addi     t1, 19
                  mulhu      t4, a6, a4
                  c.slli     t6, 5
                  mulhu      s8, s10, t3
                  lui        s10, 965917
                  bltu       s6, s2, 295f
                  c.addi     a0, -5
                  c.addi     s7, -5
                  auipc      t6, 977943
295:              c.srai     s1, 23
                  c.addi     a7, 17
                  c.slli     s1, 30
                  auipc      s2, 724487
                  srai       a7, s11, 25
                  c.srli     s0, 3
                  c.addi     gp, 23
                  c.and      a3, a4
                  fence
                  fence
                  lui        gp, 474128
                  auipc      t1, 747784
                  auipc      s2, 607717
                  c.sub      s0, s0
                  add        a7, s9, t6
                  lui        a5, 74285
                  c.sub      a5, a4
                  c.addi     t1, 18
                  c.slli     s3, 4
                  c.addi     s3, -2
                  mulh       a1, ra, s11
                  la         s6, kernel_data_page_0+2071 #start riscv_load_store_rand_instr_stream_2
                  lb         a4, 1022(s6)
                  lbu        s11, -1829(s6)
                  c.lui      a1, 15
                  c.lui      a5, 15
                  lw         t6, 1921(s6)
                  lbu        s8, 942(s6)
                  nop
                  lbu        t4, 1048(s6)
                  lbu        a6, 1260(s6)
                  c.srli     a0, 22
                  lb         s4, 478(s6)
                  remu       s1, a7, s9
                  lhu        s0, -541(s6)
                  c.lui      t4, 8
                  lb         s7, 11(s6)
                  sw         s1, 1913(s6)
                  lhu        a4, 1163(s6)
                  lui        s11, 334221
                  c.addi     gp, 17
                  lh         s1, -1073(s6)
                  c.or       a0, s0
                  c.lui      t1, 16
                  c.srai     s1, 12
                  lb         s10, 90(s6)
                  lbu        s5, -819(s6)
                  c.addi     s11, -30
                  c.addi     s2, 15
                  c.xor      a5, a2
                  lbu        t4, 86(s6)
                  lbu        a5, 1204(s6)
                  lb         s10, 382(s6)
                  c.srai     a3, 30
                  lh         t2, 1207(s6)
                  sb         t0, -910(s6)
                  lbu        a1, 1237(s6)
                  lb         a6, -544(s6)
                  lb         s3, -148(s6)
                  c.addi     gp, 6
                  c.addi     s1, 15
                  c.addi     t6, -10
                  auipc      s10, 1006281
                  lbu        t4, 226(s6)
                  lui        a1, 149225
                  sh         tp, -2015(s6)
                  lbu        s7, 791(s6) #end riscv_load_store_rand_instr_stream_2
                  lui        gp, 830315
                  slti       s4, s9, -618
                  auipc      s10, 948712
                  c.lui      s7, 2
                  lui        t4, 976982
                  c.addi     s7, -28
                  lui        s2, 41485
                  lui        a7, 281498
                  c.nop
                  auipc      a4, 354139
                  lui        a7, 456507
                  lui        s7, 152167
                  c.addi     t1, 16
                  c.lui      s0, 11
                  divu       a2, a2, zero
                  c.addi     s0, 17
                  auipc      a1, 54552
                  auipc      t6, 401709
                  c.addi     s2, 31
                  c.mv       a3, s6
                  c.addi     t5, -7
                  c.addi     a2, -3
                  c.srli     a0, 20
                  bne        t2, a3, 356f
                  lui        gp, 553987
                  c.addi     s7, -26
                  lui        t2, 653027
                  srl        zero, t0, s0
                  lui        t3, 932721
                  c.slli     s4, 24
                  c.addi     s10, 23
                  c.slli     s6, 26
                  c.srli     a1, 19
                  lui        s9, 75522
                  lui        a1, 776604
                  c.lui      s6, 20
                  c.addi     s6, 19
                  c.lui      a7, 7
                  lui        a0, 841653
                  c.andi     s1, -29
356:              srai       a3, t1, 8
                  mulhsu     a3, a7, s0
                  c.lui      s10, 7
                  lui        t2, 784820
                  c.slli     s7, 31
                  lui        t5, 356513
                  slli       s1, ra, 27
                  lui        t2, 925729
                  c.srai     a0, 10
                  c.srli     a4, 1
                  auipc      s10, 726799
                  c.srai     a1, 21
                  lui        s0, 940379
                  c.addi     s11, 21
                  lui        a2, 727277
                  lui        a3, 221342
                  c.lui      s1, 3
                  c.slli     s2, 18
                  auipc      t3, 371865
                  sll        s4, a4, s3
                  c.srli     a4, 10
                  c.addi     t3, 9
                  c.srli     a1, 4
                  lui        a2, 1039633
                  c.srli     a5, 16
                  sltiu      t4, s3, 819
                  blt        a0, a5, 387f
                  xori       a0, s5, -829
                  c.slli     a6, 14
                  lui        t2, 222631
                  la         a7, kernel_data_page_1+2343 #start riscv_load_store_rand_instr_stream_3
                  lui        a1, 554261
                  sh         a7, -267(a7)
                  sb         zero, 1524(a7)
                  lhu        t2, 763(a7)
                  lhu        s7, 639(a7)
                  lbu        s0, -226(a7)
                  c.srli     a5, 24
                  sb         t3, 1537(a7)
                  sb         t3, -280(a7)
                  c.addi     t3, 5
                  sb         s7, -646(a7)
                  lbu        t4, 308(a7)
                  lbu        t4, -1860(a7)
                  lb         t2, 1048(a7)
                  sb         ra, 278(a7)
                  c.srai     s0, 7
                  sb         t6, -1698(a7)
                  lb         a5, -186(a7)
                  sh         s1, -701(a7)
                  lui        a4, 169766
                  lb         t2, -220(a7)
                  lb         t1, -1326(a7)
                  lb         a3, -1329(a7)
                  sh         s8, 209(a7)
                  c.srli     a5, 14
                  lbu        zero, 1532(a7)
                  lbu        s4, -890(a7)
                  sh         t1, 1387(a7)
                  c.slli     gp, 12
                  lb         s1, 798(a7)
                  sb         ra, -179(a7)
                  lb         gp, 902(a7)
                  sltiu      t3, t6, -138
                  lbu        s10, -2041(a7)
                  c.addi     t3, -32
                  c.slli     t5, 4
                  sh         s7, -953(a7)
                  c.addi     a5, 8
                  lb         s3, 166(a7)
                  sb         s7, -1191(a7) #end riscv_load_store_rand_instr_stream_3
                  lui        s7, 518449
387:              auipc      a4, 689994
                  auipc      t4, 920306
                  c.addi     a3, -15
                  remu       a5, s3, tp
                  c.addi     s2, 25
                  auipc      s11, 366492
                  c.srai     s1, 23
                  c.addi     a3, 19
                  slti       gp, a1, -988
                  c.slli     t1, 30
                  mulhu      a0, s6, a4
                  c.addi     a7, -7
                  mulh       t3, sp, zero
                  c.addi     a6, -30
                  c.addi     s3, 25
                  mulh       s3, t3, a7
                  c.srli     a2, 26
                  lw         ra, 4(sp)
                  c.slli     s0, 18
                  lw         t0, 8(sp)
                  c.srai     a0, 21
                  xori       t1, gp, -289
                  c.addi     a1, 30
                  c.addi     t2, -32
                  addi       sp, sp, 56
                  lui        t5, 33875
597:              ret
.align 12
mtvec_handler:    
                  csrrw sp, 0x340, sp
                  add sp, tp, zero
                  1: addi sp, sp, -128
                  sw  x0, 0(sp)
                  sw  x1, 4(sp)
                  sw  x2, 8(sp)
                  sw  x3, 12(sp)
                  sw  x4, 16(sp)
                  sw  x5, 20(sp)
                  sw  x6, 24(sp)
                  sw  x7, 28(sp)
                  sw  x8, 32(sp)
                  sw  x9, 36(sp)
                  sw  x10, 40(sp)
                  sw  x11, 44(sp)
                  sw  x12, 48(sp)
                  sw  x13, 52(sp)
                  sw  x14, 56(sp)
                  sw  x15, 60(sp)
                  sw  x16, 64(sp)
                  sw  x17, 68(sp)
                  sw  x18, 72(sp)
                  sw  x19, 76(sp)
                  sw  x20, 80(sp)
                  sw  x21, 84(sp)
                  sw  x22, 88(sp)
                  sw  x23, 92(sp)
                  sw  x24, 96(sp)
                  sw  x25, 100(sp)
                  sw  x26, 104(sp)
                  sw  x27, 108(sp)
                  sw  x28, 112(sp)
                  sw  x29, 116(sp)
                  sw  x30, 120(sp)
                  sw  x31, 124(sp)
                  csrr a1, 0x342 # MCAUSE
                  srli a1, a1, 31
                  bne a1, x0, mmode_intr_handler
                  csrr a1, 0x342 # MCAUSE
                  csrr x31, 0x341 # MEPC
                  csrr x29, 0x300 # MSTATUS
                  li a2, 0x8 # ECALL_UMODE
                  beq a1, a2, ecall_handler
                  li a2, 0x9 # ECALL_SMODE
                  beq a1, a2, ecall_handler
                  li a2, 0xb # ECALL_MMODE
                  beq a1, a2, ecall_handler
                  li a2, 0x1
                  beq a1, a2, pt_fault_handler
                  li a2, 0x5
                  beq a1, a2, pt_fault_handler
                  li a2, 0x7
                  beq a1, a2, pt_fault_handler
                  li a2, 0xc
                  beq a1, a2, pt_fault_handler
                  li a2, 0xd
                  beq a1, a2, pt_fault_handler
                  li a2, 0xf
                  beq a1, a2, pt_fault_handler
                  li a2, 0x2 # ILLEGAL_INSTRUCTION
                  beq a1, a2, illegal_instr_handler
                  csrr x30, 0x343 # MTVAL
                  1: jal x1, test_done 

ecall_handler:    
                  j write_tohost
illegal_instr_handler:
                  csrr  x31, mepc
                  addi  x31, x31, 4
                  csrw  mepc, x31
                  lw  x0, 0(sp)
                  lw  x1, 4(sp)
                  lw  x2, 8(sp)
                  lw  x3, 12(sp)
                  lw  x4, 16(sp)
                  lw  x5, 20(sp)
                  lw  x6, 24(sp)
                  lw  x7, 28(sp)
                  lw  x8, 32(sp)
                  lw  x9, 36(sp)
                  lw  x10, 40(sp)
                  lw  x11, 44(sp)
                  lw  x12, 48(sp)
                  lw  x13, 52(sp)
                  lw  x14, 56(sp)
                  lw  x15, 60(sp)
                  lw  x16, 64(sp)
                  lw  x17, 68(sp)
                  lw  x18, 72(sp)
                  lw  x19, 76(sp)
                  lw  x20, 80(sp)
                  lw  x21, 84(sp)
                  lw  x22, 88(sp)
                  lw  x23, 92(sp)
                  lw  x24, 96(sp)
                  lw  x25, 100(sp)
                  lw  x26, 104(sp)
                  lw  x27, 108(sp)
                  lw  x28, 112(sp)
                  lw  x29, 116(sp)
                  lw  x30, 120(sp)
                  lw  x31, 124(sp)
                  addi sp, sp, 128
                  add tp, sp, zero
                  csrrw sp, 0x340, sp
                  mret

pt_fault_handler: 
                  nop

.align 12
mmode_intr_handler:
                  csrr  a1, 0x300 # MSTATUS;
                  csrr  a1, 0x304 # MIE;
                  csrr  a1, 0x344 # MIP;
                  csrrc a1, 0x344, a1 # MIP;
                  lw  x0, 0(sp)
                  lw  x1, 4(sp)
                  lw  x2, 8(sp)
                  lw  x3, 12(sp)
                  lw  x4, 16(sp)
                  lw  x5, 20(sp)
                  lw  x6, 24(sp)
                  lw  x7, 28(sp)
                  lw  x8, 32(sp)
                  lw  x9, 36(sp)
                  lw  x10, 40(sp)
                  lw  x11, 44(sp)
                  lw  x12, 48(sp)
                  lw  x13, 52(sp)
                  lw  x14, 56(sp)
                  lw  x15, 60(sp)
                  lw  x16, 64(sp)
                  lw  x17, 68(sp)
                  lw  x18, 72(sp)
                  lw  x19, 76(sp)
                  lw  x20, 80(sp)
                  lw  x21, 84(sp)
                  lw  x22, 88(sp)
                  lw  x23, 92(sp)
                  lw  x24, 96(sp)
                  lw  x25, 100(sp)
                  lw  x26, 104(sp)
                  lw  x27, 108(sp)
                  lw  x28, 112(sp)
                  lw  x29, 116(sp)
                  lw  x30, 120(sp)
                  lw  x31, 124(sp)
                  addi sp, sp, 128
                  add tp, sp, zero
                  csrrw sp, 0x340, sp
                  mret;

.data
.align 4;
kernel_data_page_0:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
kernel_data_page_1:
.align 12
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.word 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000, 0x00000000
.align 4;
.align 5
_kernel_stack_start:
.rept 4999
.4byte 0x0
.endr
_kernel_stack_end:
.4byte 0x0
_kernel_end: nop
