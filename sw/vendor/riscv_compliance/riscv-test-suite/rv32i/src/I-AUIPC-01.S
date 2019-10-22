# RISC-V Compliance Test I-AUIPC-01
#
# Copyright (c) 2017, Codasip Ltd.
# Copyright (c) 2018, Imperas Software Ltd. Additions
# All rights reserved.
#
# Redistribution and use in source and binary forms, with or without
# modification, are permitted provided that the following conditions are met:
#      * Redistributions of source code must retain the above copyright
#        notice, this list of conditions and the following disclaimer.
#      * Redistributions in binary form must reproduce the above copyright
#        notice, this list of conditions and the following disclaimer in the
#        documentation and/or other materials provided with the distribution.
#      * Neither the name of the Codasip Ltd., Imperas Software Ltd. nor the
#        names of its contributors may be used to endorse or promote products
#        derived from this software without specific prior written permission.
#
# THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS
# IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO,
# THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
# PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL Codasip Ltd., Imperas Software Ltd.
# BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
# DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
# LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
# ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
# (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
# THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
#
# Specification: RV32I Base Integer Instruction Set, Version 2.0
# Description: Testing instruction AUIPC.

#include "compliance_test.h"
#include "compliance_io.h"
#include "test_macros.h"

# Test Virtual Machine (TVM) used by program.
RV_COMPLIANCE_RV32M

# Test code region
RV_COMPLIANCE_CODE_BEGIN

    RVTEST_IO_INIT
    RVTEST_IO_ASSERT_GPR_EQ(x31, x0, 0x00000000)
    RVTEST_IO_WRITE_STR(x31, "# Test Begin\n")

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A - general test of AUIPC\n");

    # Addresses for test data and results
    la      x14, test_A_data
    la      x15, test_A_res

    # Register initialization
    lw      x1, 0(x14)
    li      x2, 0x00001004
    li      x3, 0xFFFFF008
    li      x4, 0x7FFFF00C
    li      x5, 0x80000010

    add     x2, x1, x2
    add     x3, x1, x3
    add     x4, x1, x4
    add     x5, x1, x5

    # Test
test_A:
    auipc   x6, 0x0
    auipc   x7, 0x1
    auipc   x16, 0xFFFFF
    auipc   x29, 0x7FFFF
    auipc   x31, 0x80000

    xor     x6, x6, x1
    xor     x7, x7, x2
    xor     x16, x16, x3
    xor     x29, x29, x4
    xor     x31, x31, x5

    # Store results
    sw      x6, 0(x15)
    sw      x7, 4(x15)
    sw      x16, 8(x15)
    sw      x29, 12(x15)
    sw      x31, 16(x15)

    //
    // Assert
    //
    RVTEST_IO_CHECK()
    RVTEST_IO_ASSERT_GPR_EQ(x15, x6,  0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x15, x7,  0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x15, x16, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x15, x29, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x15, x31, 0x00000000)

    RVTEST_IO_WRITE_STR(x31, "# Test part A1  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part B - test AUIPC overwrites low bits\n");

    # Addresses for test data and results
    la      x17, test_B_data
    la      x16, test_B_res

    # Register initialization
    li      x1, 0x11111111
    li      x2, 0x22222222
    li      x15, 0x33333333
    li      x28, 0x44444444
    li      x30, 0x55555555

    lw      x3, 0(x17)
    li      x4, 0x80000000
    li      x5, 0x7FFFF004
    li      x6, 0x00000008
    li      x7, 0x0000100C
    li      x8, 0xFFFFF010

    add     x4, x3, x4
    add     x5, x3, x5
    add     x6, x3, x6
    add     x7, x3, x7
    add     x8, x3, x8

    # Test
test_B:
    auipc   x1, 0x80000
    auipc   x2, 0x7FFFF
    auipc   x15, 0
    auipc   x28, 1
    auipc   x30, 0xFFFFF

    xor     x1, x1, x4
    xor     x2, x2, x5
    xor     x15, x15, x6
    xor     x28, x28, x7
    xor     x30, x30, x8

    # Store results
    sw      x1, 0(x16)
    sw      x2, 4(x16)
    sw      x15, 8(x16)
    sw      x28, 12(x16)
    sw      x30, 16(x16)

    RVTEST_IO_ASSERT_GPR_EQ(x16, x1,  0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x16, x2,  0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x16, x15, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x16, x28, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x16, x30, 0x00000000)

    RVTEST_IO_WRITE_STR(x31, "# Test part A2  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part C - test loading address using auipc + addi or la alias\n");

    # Addresses for test data and results
    la      x18, test_C_data
    la      x17, test_C_res

test_C1:
    # Register initialization
    lw      x1, 0(x18)
    lw      x2, 4(x18)
    lw      x3, 8(x18)

    # Test
    la      x4,  test_C1
    la      x15, test_C2
    la      x30, test_C3

    # C1
    auipc   x5, 0x0
    addi    x5, x5, 0xFFFFFFDC

test_C2:
    # C2
    auipc   x16, 0x0
    addi    x16, x16, 0x0

    # C3
    auipc   x31, 0x0
    addi    x31, x31, 0x28

    xor     x4, x4, x1
    xor     x15, x15, x2
    xor     x30, x30, x3
    sub     x5, x5, x1
    xor     x16, x16, x2
    xor     x31, x31, x3

    # Store results
    sw      x4, 0(x17)
    sw      x15, 4(x17)
test_C3:
    sw      x30, 8(x17)
    sw      x5, 12(x17)
    sw      x16, 16(x17)
    sw      x31, 20(x17)

    RVTEST_IO_ASSERT_GPR_EQ(x17, x4,  0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x17, x15, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x17, x29, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x17, x5,  0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x17, x16, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x17, x31, 0x00000000)

    RVTEST_IO_WRITE_STR(x31, "# Test part A3  - Complete\n");

    RVTEST_IO_WRITE_STR(x31, "# Test End\n")

 # ---------------------------------------------------------------------------------------------
    # HALT
    RV_COMPLIANCE_HALT

RV_COMPLIANCE_CODE_END

# Input data section.
    .data
    .align 4

test_A_data:
    .word test_A
test_B_data:
    .word test_B
test_C_data:
    .word test_C1
    .word test_C2
    .word test_C3


# Output data section.
RV_COMPLIANCE_DATA_BEGIN
    .align 4

test_A_res:
    .fill 5, 4, -1
test_B_res:
    .fill 5, 4, -1
test_C_res:
    .fill 6, 4, -1

RV_COMPLIANCE_DATA_END
