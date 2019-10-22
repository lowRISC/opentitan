# RISC-V Compliance Test I-BLT-01
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
# Description: Testing instruction BLT.

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
    RVTEST_IO_WRITE_STR(x31, "# Test part A1 - general test of value 0 with 0, 1, -1, MIN, MAX register values\n");

    # Addresses for test data and results
    la      x1, test_A1_data
    la      x2, test_A1_res

    # Load testdata
    lw      x3, 0(x1)

    # Register initialization
    li      x4, 0
    li      x5, 1
    li      x6, -1
    li      x7, 0x7FFFFFFF
    li      x8, 0x80000000
    li      x31, 0

    # Test
    blt     x3, x4, 1f
    ori     x31, x31, 0x1
1:
    blt     x3, x5, 1f
    ori     x31, x31, 0x2
1:
    blt     x3, x6, 1f
    ori     x31, x31, 0x4
1:
    blt     x3, x7, 1f
    ori     x31, x31, 0x8
1:
    blt     x3, x8, 1f
    ori     x31, x31, 0x10
1:

    # Store results
    sw      x3, 0(x2)
    sw      x4, 4(x2)
    sw      x5, 8(x2)
    sw      x6, 12(x2)
    sw      x7, 16(x2)
    sw      x8, 20(x2)
    sw      x31, 24(x2)

    //
    // Assert
    //
    RVTEST_IO_CHECK()
    RVTEST_IO_ASSERT_GPR_EQ(x2, x3, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x4, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x5, 0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x6, 0xFFFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x7, 0x7FFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x8, 0x80000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x31, 0x00000015)

    RVTEST_IO_WRITE_STR(x31, "# Test part A1  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A2 - general test of value 1 with 0, 1, -1, MIN, MAX register values\n");

    # Addresses for test data and results
    la      x1, test_A2_data
    la      x2, test_A2_res

    # Load testdata
    lw      x6, 0(x1)

    # Register initialization
    li      x7, 0
    li      x8, 1
    li      x9, -1
    li      x10, 0x7FFFFFFF
    li      x11, 0x80000000
    li      x31, 0

    # Test
    blt     x6, x7, 1f
    ori     x31, x31, 0x1
1:
    blt     x6, x8, 1f
    ori     x31, x31, 0x2
1:
    blt     x6, x9, 1f
    ori     x31, x31, 0x4
1:
    blt     x6, x10, 1f
    ori     x31, x31, 0x8
1:
    blt     x6, x11, 1f
    ori     x31, x31, 0x10
1:

    # Store results
    sw      x6, 0(x2)
    sw      x7, 4(x2)
    sw      x8, 8(x2)
    sw      x9, 12(x2)
    sw      x10, 16(x2)
    sw      x11, 20(x2)
    sw      x31, 24(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x6,  0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x7,  0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x8,  0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x9,  0xFFFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x10, 0x7FFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x11, 0x80000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x31, 0x00000017)

    RVTEST_IO_WRITE_STR(x31, "# Test part A2  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A3 - general test of value -1 with 0, 1, -1, MIN, MAX register values\n");

    # Addresses for test data and results
    la      x1, test_A3_data
    la      x2, test_A3_res

    # Load testdata
    lw      x12, 0(x1)

    # Register initialization
    li      x13, 0
    li      x14, 1
    li      x15, -1
    li      x16, 0x7FFFFFFF
    li      x17, 0x80000000
    li      x31, 0

    # Test
    blt     x12, x13, 1f
    ori     x31, x31, 0x1
1:
    blt     x12, x14, 1f
    ori     x31, x31, 0x2
1:
    blt     x12, x15, 1f
    ori     x31, x31, 0x4
1:
    blt     x12, x16, 1f
    ori     x31, x31, 0x8
1:
    blt     x12, x17, 1f
    ori     x31, x31, 0x10
1:

    # Store results
    sw      x12, 0(x2)
    sw      x13, 4(x2)
    sw      x14, 8(x2)
    sw      x15, 12(x2)
    sw      x16, 16(x2)
    sw      x17, 20(x2)
    sw      x31, 24(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x12, 0xFFFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x13, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x14, 0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x15, 0xFFFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x16, 0x7FFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x17, 0x80000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x31, 0x00000014)

    RVTEST_IO_WRITE_STR(x31, "# Test part A3  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A4 - general test of value 0x7FFFFFFF with 0, 1, -1, MIN, MAX register values\n");

    # Addresses for test data and results
    la      x1, test_A4_data
    la      x2, test_A4_res

    # Load testdata
    lw      x18, 0(x1)

    # Register initialization
    li      x19, 0
    li      x20, 1
    li      x21, -1
    li      x22, 0x7FFFFFFF
    li      x23, 0x80000000
    li      x31, 0

    # Test
    blt     x18, x19, 1f
    ori     x31, x31, 0x1
1:
    blt     x18, x20, 1f
    ori     x31, x31, 0x2
1:
    blt     x18, x21, 1f
    ori     x31, x31, 0x4
1:
    blt     x18, x22, 1f
    ori     x31, x31, 0x8
1:
    blt     x18, x23, 1f
    ori     x31, x31, 0x10
1:

    # Store results
    sw      x18, 0(x2)
    sw      x19, 4(x2)
    sw      x20, 8(x2)
    sw      x21, 12(x2)
    sw      x22, 16(x2)
    sw      x23, 20(x2)
    sw      x31, 24(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x18, 0x7FFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x19, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x20, 0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x21, 0xFFFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x22, 0x7FFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x23, 0x80000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x31, 0x0000001F)

    RVTEST_IO_WRITE_STR(x31, "# Test part A4  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A5 - general test of value 0x80000000 with 0, 1, -1, MIN, MAX register values\n");

    # Addresses for test data and results
    la      x1, test_A5_data
    la      x2, test_A5_res

    # Load testdata
    lw      x24, 0(x1)

    # Register initialization
    li      x25, 0
    li      x26, 1
    li      x27, -1
    li      x28, 0x7FFFFFFF
    li      x29, 0x80000000
    li      x31, 0

    # Test
    blt     x24, x25, 1f
    ori     x31, x31, 0x1
1:
    blt     x24, x26, 1f
    ori     x31, x31, 0x2
1:
    blt     x24, x27, 1f
    ori     x31, x31, 0x4
1:
    blt     x24, x28, 1f
    ori     x31, x31, 0x8
1:
    blt     x24, x29, 1f
    ori     x31, x31, 0x10
1:

    # Store results
    sw      x24, 0(x2)
    sw      x25, 4(x2)
    sw      x26, 8(x2)
    sw      x27, 12(x2)
    sw      x28, 16(x2)
    sw      x29, 20(x2)
    sw      x31, 24(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x24, 0x80000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x25, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x26, 0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x27, 0xFFFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x28, 0x7FFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x29, 0x80000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x31, 0x00000010)

    RVTEST_IO_WRITE_STR(x31, "# Test part A5  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part B - testing compare with x0\n");

    # Address for test results
    la      x27, test_B_res

    # Register initialization
    li      x1, 0
    li      x2, 1
    li      x3, -1
    li      x4, 0x7FFFFFFF
    li      x5, 0x80000000
    li      x31, 0

    # Test
    blt     x1, x0, 1f
    ori     x31, x31, 0x1
1:
    blt     x2, x0, 1f
    ori     x31, x31, 0x2
1:
    blt     x3, x0, 1f
    ori     x31, x31, 0x4
1:
    blt     x4, x0, 1f
    ori     x31, x31, 0x8
1:
    blt     x5, x0, 1f
    ori     x31, x31, 0x10
1:
    blt     x0, x1, 1f
    ori     x31, x31, 0x20
1:
    blt     x0, x2, 1f
    ori     x31, x31, 0x40
1:
    blt     x0, x3, 1f
    ori     x31, x31, 0x80
1:
    blt     x0, x4, 1f
    ori     x31, x31, 0x100
1:
    blt     x0, x5, 1f
    ori     x31, x31, 0x200
1:

    # Store results
    sw      x31, 0(x27)

    RVTEST_IO_ASSERT_GPR_EQ(x27, x31, 0x000002AB)

    RVTEST_IO_WRITE_STR(x31, "# Test part B  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part C - jumps forward, backward\n");

    # Address for test data and results
    la      x21, test_C_data
    la      x22, test_C_res

    # Load testdata
    lw      x31, 0(x21)

    # Register initialization
    li      x2, 0xFFFFFFFF
    li      x3, 0xFFFFFFFF
    li      x4, 0x0FEDCBA9

    # Test
    blt     x31, x0, 2f
    li      x2, 0
    li      x3, 0
    li      x4, 0

1:
    li      x3, 0x87654321
    blt     x31, x0, 3f
    li      x2, 0
    li      x3, 0
    li      x4, 0

2:
    li      x2, 0x9ABCDEF0
    blt     x31, x0, 1b
    li      x2, 0
    li      x3, 0
    li      x4, 0

3:

    # Store results
    sw      x0, 0(x22)
    sw      x2, 4(x22)
    sw      x3, 8(x22)
    sw      x4, 12(x22)

    RVTEST_IO_ASSERT_GPR_EQ(x22, x0, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x22, x2, 0x9ABCDEF0)
    RVTEST_IO_ASSERT_GPR_EQ(x22, x3, 0x87654321)
    RVTEST_IO_ASSERT_GPR_EQ(x22, x4, 0x0FEDCBA9)

    RVTEST_IO_WRITE_STR(x31, "# Test part C  - Complete\n");

    RVTEST_IO_WRITE_STR(x31, "# Test End\n")

 # ---------------------------------------------------------------------------------------------
    # HALT
    RV_COMPLIANCE_HALT

RV_COMPLIANCE_CODE_END

# Input data section.
    .data
    .align 4
test_A1_data:
    .word 0
test_A2_data:
    .word 1
test_A3_data:
    .word -1
test_A4_data:
    .word 0x7FFFFFFF
test_A5_data:
    .word 0x80000000
test_C_data:
    .word -1

# Output data section.
RV_COMPLIANCE_DATA_BEGIN
    .align 4

test_A1_res:
    .fill 7, 4, -1
test_A2_res:
    .fill 7, 4, -1
test_A3_res:
    .fill 7, 4, -1
test_A4_res:
    .fill 7, 4, -1
test_A5_res:
    .fill 7, 4, -1
test_B_res:
    .fill 1, 4, -1
test_C_res:
    .fill 4, 4, -1

RV_COMPLIANCE_DATA_END
