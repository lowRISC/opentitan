# RISC-V Compliance Test I-SB-01
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
# Description: Testing instruction SB.

#include "compliance_test.h"
#include "compliance_io.h"
#include "test_macros.h"

# Test Virtual Machine (TVM) used by program.
RV_COMPLIANCE_RV32M

# Test code region
RV_COMPLIANCE_CODE_BEGIN

    RVTEST_IO_INIT
    RVTEST_IO_ASSERT_GPR_EQ(x31, x0, 0x00000000)
    RVTEST_IO_WRITE_STR(x31, "Test Begin\n")

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A1 - test base address + 0\n");

    # Address for test results
    la      x1, test_A1_res

    # Set memory
    li      x31, 0xAAAABBBB
    sw      x31, 0(x1)

    # Test
    li      x2, 0x11F1F222
    sb      x2, 0(x1)

    //
    // Assert
    //
    RVTEST_IO_CHECK()
    RVTEST_IO_ASSERT_GPR_EQ(x1, x2, 0x11F1F222)
    RVTEST_IO_ASSERT_GPR_EQ(x1, x31, 0xAAAABBBB)

    RVTEST_IO_WRITE_STR(x31, "# Test part A1  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A2 - test base address - 1\n");

    # Address for test results
    la      x5, test_A2_res + 1

    # Clear memory
    sw      x0, -1(x5)

    # Test
    li      x25, 0xF33344F4
    sb      x25, 0xFFFFFFFF(x5)

    RVTEST_IO_ASSERT_GPR_EQ(x5, x0, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x5, x25, 0xF33344F4)

    RVTEST_IO_WRITE_STR(x31, "# Test part A2  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A3 - test base address + 1\n");

    # Address for test results
    la      x8, test_A3_res - 1

    # Clear memory
    sw      x0, 1(x8)

    # Test
    li      x31, 0x55F5F666
    sb      x31, +1(x8)

    RVTEST_IO_ASSERT_GPR_EQ(x8, x0, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x8, x31, 0x55F5F666)

    RVTEST_IO_WRITE_STR(x31, "# Test part A3  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A4 - test base address - 2048\n");

    # Address for test results
    la      x11, test_A4_res + 2048

    # Clear memory
    sw      x0, -2048(x11)

    # Test
    li      x12, 0xF77788F8
    sb      x12, 0xFFFFF800(x11)

    RVTEST_IO_ASSERT_GPR_EQ(x11, x0, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x11, x12, 0xF77788F8)

    RVTEST_IO_WRITE_STR(x31, "# Test part A4  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A5 - test base address + 2047\n");

    # Address for test results
    la      x14, test_A5_res - 2047

    # Clear memory
    sw      x0, 2047(x14)

    # Test
    li      x15, 0x99090AAA
    sb      x15, 0x7FF(x14)

    RVTEST_IO_ASSERT_GPR_EQ(x14, x0, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x14, x15, 0x99090AAA)

    RVTEST_IO_WRITE_STR(x31, "# Test part A5  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part B - test base address + -4, -3, ... , 7\n");

    # Address for test results
    la      x17, test_B_res

    # Test
    li      x18, 0x1111110C
    li      x19, 0x222222CC
    li      x20, 0x333333BB
    li      x21, 0x4444440B
    li      x22, 0x555555EE
    li      x23, 0x6666660E
    li      x24, 0x7777770D
    li      x25, 0x888888DD
    li      x26, 0x999999F0
    li      x27, 0xAAAAAA00
    li      x28, 0xBBBBBBFF
    li      x29, 0xCCCCCC0F

    # Store results
    sb      x18, -4(x17)
    sb      x19, -3(x17)
    sb      x20, -2(x17)
    sb      x21, -1(x17)
    sb      x22, 0(x17)
    sb      x23, 1(x17)
    sb      x24, 2(x17)
    sb      x25, 3(x17)
    sb      x26, 4(x17)
    sb      x27, 5(x17)
    sb      x28, 6(x17)
    sb      x29, 7(x17)

    RVTEST_IO_ASSERT_GPR_EQ(x17, x18, 0x1111110C)
    RVTEST_IO_ASSERT_GPR_EQ(x17, x19, 0x222222CC)
    RVTEST_IO_ASSERT_GPR_EQ(x17, x20, 0x333333BB)
    RVTEST_IO_ASSERT_GPR_EQ(x17, x21, 0x4444440B)
    RVTEST_IO_ASSERT_GPR_EQ(x17, x22, 0x555555EE)
    RVTEST_IO_ASSERT_GPR_EQ(x17, x23, 0x6666660E)
    RVTEST_IO_ASSERT_GPR_EQ(x17, x24, 0x7777770D)
    RVTEST_IO_ASSERT_GPR_EQ(x17, x25, 0x888888DD)
    RVTEST_IO_ASSERT_GPR_EQ(x17, x26, 0x999999F0)
    RVTEST_IO_ASSERT_GPR_EQ(x17, x27, 0xAAAAAA00)
    RVTEST_IO_ASSERT_GPR_EQ(x17, x28, 0xBBBBBBFF)
    RVTEST_IO_ASSERT_GPR_EQ(x17, x29, 0xCCCCCC0F)

    RVTEST_IO_WRITE_STR(x31, "# Test part B  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part C - test store x0\n");

    # Address for test results
    la      x22, test_C_res

    # Set memory
    li      x1, 0x87654321
    sw      x1, 0(x22)

    # Test
    li      x0, 0x12345678
    sb      x0, 0(x22)

    RVTEST_IO_ASSERT_GPR_EQ(x22, x0, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x22, x1, 0x87654321)

    RVTEST_IO_WRITE_STR(x31, "# Test part C  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part D1 - test for forwarding (to address register)\n");

    # Address for test data
    la      x21, test_D1_data

    # Clear memory
    lw      x1, 0(x21)
    sw      x0, 0(x1)

    # Test
    li      x19, 0x11223344
    lw      x23, 0(x21)
    sb      x19, 0(x23)

    RVTEST_IO_ASSERT_GPR_EQ(x23, x19, 0x11223344)

    RVTEST_IO_WRITE_STR(x31, "# Test part D  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part D2 - test for forwarding (to data register)\n");

    # Address for test data
    la      x23, test_D2_data
    la      x24, test_D2_res

    # Clear memory
    sw      x0, 0(x24)

    # Test
    lw      x25, 0(x23)
    sb      x25, 0(x24)

    RVTEST_IO_ASSERT_GPR_EQ(x24, x25, 0x9ABCDEF0)

    RVTEST_IO_WRITE_STR(x31, "# Test part E  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part E1 - test war hazard (data register)\n");

    # Address for test results
    la      x26, test_E1_res

    # Clear memory
    sw      x0, 0(x26)

    # Test
    li      x25, 0x76543210
    sb      x25, 0(x26)
    mv      x25, x0

    RVTEST_IO_ASSERT_GPR_EQ(x26, x25, 0x00000000)

    RVTEST_IO_WRITE_STR(x31, "# Test part A1  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part E2 - test war hazard (address register)\n");

    # Address for test results
    la      x28, test_E2_res

    # Clear memory
    sw      x0, 0(x28)

    # Test
    li      x27, 0x89ABCDEF
    sb      x27, 0(x28)
    addi    x28, x28, -4

    RVTEST_IO_ASSERT_GPR_EQ(x28, x27, 0x89ABCDEF)

    RVTEST_IO_WRITE_STR(x31, "# Test part A2  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part F - test raw hazard in memory\n");

    # Address for test results
    la      x29, test_F_res

    # Clear memory
    sw      x0, 0(x29)
    sw      x0, 4(x29)

    # Test
    li      x27, 0x14725836
    sb      x27, 0(x29)
    lw      x30, 0(x29)
    sb      x30, 4(x29)

    RVTEST_IO_ASSERT_GPR_EQ(x29, x27, 0x14725836)
    RVTEST_IO_ASSERT_GPR_EQ(x29, x30, 0x00000036)

    RVTEST_IO_WRITE_STR(x31, "# Test part A3  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part G - test waw hazard in memory\n");

    # Address for test results
    la      x1, test_G_res

    # Clear memory
    sw      x0, 0(x1)

    # Test
    li      x2, 0x96385201
    li      x3, 0x25814963
    sb      x2, 0(x1)
    sb      x3, 0(x1)

    RVTEST_IO_ASSERT_GPR_EQ(x1, x2, 0x96385201)
    RVTEST_IO_ASSERT_GPR_EQ(x1, x3, 0x25814963)

    RVTEST_IO_WRITE_STR(x31, "# Test part A4  - Complete\n");

    RVTEST_IO_WRITE_STR(x31, "Test End\n")

 # ---------------------------------------------------------------------------------------------
    # HALT
    RV_COMPLIANCE_HALT

RV_COMPLIANCE_CODE_END

# Input data section.
    .data
    .align 4

test_D1_data:
    .word test_D1_res
test_D2_data:
    .word 0x9ABCDEF0


# Output data section.
RV_COMPLIANCE_DATA_BEGIN
    .align 4

test_A1_res:
    .fill 1, 4, -1
test_A2_res:
    .fill 1, 4, -1
test_A3_res:
    .fill 1, 4, -1
test_A4_res:
    .fill 1, 4, -1
test_A5_res:
    .fill 1, 4, -1
    .fill 1, 4, -1
test_B_res:
    .fill 2, 4, -1
test_C_res:
    .fill 1, 4, -1
test_D1_res:
    .fill 1, 4, -1
test_D2_res:
    .fill 1, 4, -1
test_E1_res:
    .fill 1, 4, -1
test_E2_res:
    .fill 1, 4, -1
test_F_res:
    .fill 2, 4, -1
test_G_res:
    .fill 1, 4, -1

RV_COMPLIANCE_DATA_END
