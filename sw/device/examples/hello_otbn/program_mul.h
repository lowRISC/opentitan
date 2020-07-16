// python test/programs.py -O carray -s mul_256x256
static const uint32_t code [] = {
    0x00000213, // addi x4, x0, 0
    0x0000420b, // bn.lid x4, 0(x0)
    0x00100213, // addi x4, x0, 1
    0x0040420b, // bn.lid x4, 1(x0)
    0x00200213, // addi x4, x0, 2
    0x0080420b, // bn.lid x4, 2(x0)
    0x00300213, // addi x4, x0, 3
    0x00c0420b, // bn.lid x4, 3(x0)
    0x0010105b, // bn.mulqacc.z w0.0, w1.0, 0
    0x0810205b, // bn.mulqacc w0.1, w1.0, 64
    0x4210215b, // bn.mulqacc.so w2.l, w0.0, w1.1, 64
    0x1010005b, // bn.mulqacc w0.2, w1.0, 0
    0x0a10005b, // bn.mulqacc w0.1, w1.1, 0
    0x0410005b, // bn.mulqacc w0.0, w1.2, 0
    0x1810205b, // bn.mulqacc w0.3, w1.0, 64
    0x1210205b, // bn.mulqacc w0.2, w1.1, 64
    0x0c10205b, // bn.mulqacc w0.1, w1.2, 64
    0x6610215b, // bn.mulqacc.so w2.u, w0.0, w1.3, 64
    0x1a10005b, // bn.mulqacc w0.3, w1.1, 0
    0x1410005b, // bn.mulqacc w0.2, w1.2, 0
    0x0e10005b, // bn.mulqacc w0.1, w1.3, 0
    0x1c10205b, // bn.mulqacc w0.3, w1.2, 64
    0x561021db, // bn.mulqacc.so w3.l, w0.2, w1.3, 64
    0x7e1001db, // bn.mulqacc.so w3.u, w0.3, w1.3, 0
    0x00000213, // addi x4, x0, 0
    0x0000520b, // bn.sid x4, 0(x0)
    0x00100213, // addi x4, x0, 1
    0x0040520b, // bn.sid x4, 1(x0)
    0x00200213, // addi x4, x0, 2
    0x0080520b, // bn.sid x4, 2(x0)
    0x00300213, // addi x4, x0, 3
    0x00c0520b, // bn.sid x4, 3(x0)
};
