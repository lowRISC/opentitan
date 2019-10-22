# RISC-V Compliance Test I-XOR-01
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
# Description: Testing instruction XOR.

#include "compliance_test.h"
#include "compliance_io.h"
#include "test_macros.h"

# Test Virtual Machine (TVM) used by program.
RV_COMPLIANCE_RV32M

# Test code region.
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

    # Test
    xor     x4, x3, x4
    xor     x5, x3, x5
    xor     x6, x3, x6
    xor     x7, x3, x7
    xor     x8, x3, x8

    # Store results
    sw      x3, 0(x2)
    sw      x4, 4(x2)
    sw      x5, 8(x2)
    sw      x6, 12(x2)
    sw      x7, 16(x2)
    sw      x8, 20(x2)

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

    RVTEST_IO_WRITE_STR(x31, "# Test part A1  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A2 - general test of value 1 with 0, 1, -1, MIN, MAX register values\n");

    # Addresses for test data and results
    la      x1, test_A2_data
    la      x2, test_A2_res

    # Load testdata
    lw      x8, 0(x1)

    # Register initialization
    li      x9, 0
    li      x10, 1
    li      x11, -1
    li      x12, 0x7FFFFFFF
    li      x13, 0x80000000

    # Test
    xor     x9, x8, x9
    xor     x10, x8, x10
    xor     x11, x8, x11
    xor     x12, x8, x12
    xor     x13, x8, x13

    # Store results
    sw      x8, 0(x2)
    sw      x9, 4(x2)
    sw      x10, 8(x2)
    sw      x11, 12(x2)
    sw      x12, 16(x2)
    sw      x13, 20(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x8, 0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x9, 0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x10, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x11, 0xFFFFFFFE)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x12, 0x7FFFFFFE)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x13, 0x80000001)

    RVTEST_IO_WRITE_STR(x31, "# Test part A2  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A3 - general test of value -1 with 0, 1, -1, MIN, MAX register values\n");

    # Addresses for test data and results
    la      x1, test_A3_data
    la      x2, test_A3_res

    # Load testdata
    lw      x13, 0(x1)

    # Register initialization
    li      x14, 0
    li      x15, 1
    li      x16, -1
    li      x17, 0x7FFFFFFF
    li      x18, 0x80000000

    # Test
    xor     x14, x13, x14
    xor     x15, x13, x15
    xor     x16, x13, x16
    xor     x17, x13, x17
    xor     x18, x13, x18

    # Store results
    sw      x13, 0(x2)
    sw      x14, 4(x2)
    sw      x15, 8(x2)
    sw      x16, 12(x2)
    sw      x17, 16(x2)
    sw      x18, 20(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x13, 0xFFFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x14, 0xFFFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x15, 0xFFFFFFFE)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x16, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x17, 0x80000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x18, 0x7FFFFFFF)

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

    # Test execution
    xor     x19, x18, x19
    xor     x20, x18, x20
    xor     x21, x18, x21
    xor     x22, x18, x22
    xor     x23, x18, x23

    # Store results
    sw      x18, 0(x2)
    sw      x19, 4(x2)
    sw      x20, 8(x2)
    sw      x21, 12(x2)
    sw      x22, 16(x2)
    sw      x23, 20(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x18, 0x7FFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x19, 0x7FFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x20, 0x7FFFFFFE)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x21, 0x80000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x22, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x23, 0xFFFFFFFF)

    RVTEST_IO_WRITE_STR(x31, "# Test part A4  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A5 - general test of value 0x80000000 with 0, 1, -1, MIN, MAX register values\n");

    # Addresses for test data and results
    la      x1, test_A5_data
    la      x2, test_A5_res

    # Load testdata
    lw      x23, 0(x1)

    # Register initialization
    li      x24, 0
    li      x25, 1
    li      x26, -1
    li      x27, 0x7FFFFFFF
    li      x28, 0x80000000

    # Test
    xor     x24, x23, x24
    xor     x25, x23, x25
    xor     x26, x23, x26
    xor     x27, x23, x27
    xor     x28, x23, x28

    # Store results
    sw      x23, 0(x2)
    sw      x24, 4(x2)
    sw      x25, 8(x2)
    sw      x26, 12(x2)
    sw      x27, 16(x2)
    sw      x28, 20(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x23, 0x80000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x24, 0x80000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x25, 0x80000001)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x26, 0x7FFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x27, 0xFFFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x28, 0x00000000)

    RVTEST_IO_WRITE_STR(x31, "# Test part A5  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part B - testing forwarding between instructions\n");

    # Addresses for test data and results
    la      x25, test_B_data
    la      x26, test_B_res

    # Load testdata
    lw      x28, 0(x25)

    # Register initialization
    li      x4, 0x7F
    li      x5, 0x3F
    li      x6, 0x1F
    li      x7, 0x0F
    li      x8, 0x07
    li      x9, 0x03

    # Test
    xor     x29, x28, x4
    xor     x30, x29, x5
    xor     x31, x30, x6
    xor     x1, x31, x7
    xor     x2, x1, x8
    xor     x3, x2, x9

    # store results
    sw      x4, 0(x26)
    sw      x28, 4(x26)
    sw      x29, 8(x26)
    sw      x30, 12(x26)
    sw      x31, 16(x26)
    sw      x1, 20(x26)
    sw      x2, 24(x26)
    sw      x3, 28(x26)

    RVTEST_IO_ASSERT_GPR_EQ(x26, x4,  0x0000007F)
    RVTEST_IO_ASSERT_GPR_EQ(x26, x28, 0xABCDFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x26, x29, 0xABCDFF80)
    RVTEST_IO_ASSERT_GPR_EQ(x26, x30, 0xABCDFFBF)
    RVTEST_IO_ASSERT_GPR_EQ(x26, x31, 0xABCDFFA0)
    RVTEST_IO_ASSERT_GPR_EQ(x26, x1,  0xABCDFFAF)
    RVTEST_IO_ASSERT_GPR_EQ(x26, x2,  0xABCDFFA8)
    RVTEST_IO_ASSERT_GPR_EQ(x26, x3,  0xABCDFFAB)

    RVTEST_IO_WRITE_STR(x31, "# Test part B  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part C - testing writing to x0\n");

    # Addresses for test data and results
    la      x1, test_C_data
    la      x2, test_C_res

    # Load testdata
    lw      x28, 0(x1)

    # Register initialization
    li      x27, 0xF7FF8818

    # Test
    xor     x0, x28, x27

    # store results
    sw      x0, 0(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x0, 0x00000000)

    RVTEST_IO_WRITE_STR(x31, "# Test part C  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part D - testing forwarding throught x0\n");

    # Addresses for test data and results
    la      x1, test_D_data
    la      x2, test_D_res

    # Load testdata
    lw      x28, 0(x1)

    # Register initialization
    li      x27, 0xF7FF8818

    # Test
    xor     x0, x28, x27
    xor     x5, x0, x0

    # store results
    sw      x0, 0(x2)
    sw      x5, 4(x2)


    RVTEST_IO_ASSERT_GPR_EQ(x2, x0, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x5, 0x00000000)

    RVTEST_IO_WRITE_STR(x31, "# Test part D  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part E - testing moving (xor with x0)\n");

    # Addresses for test data and results
    la      x1, test_E_data
    la      x2, test_E_res

    # Load testdata
    lw      x3, 0(x1)

    # Test
    xor     x4, x3, x0
    xor     x5, x4, x0
    xor     x6, x0, x5
    xor     x14, x6, x0
    xor     x15, x14, x0
    xor     x16, x15, x0
    xor     x25, x0, x16
    xor     x26, x0, x25
    xor     x27, x26, x0

    # Store results
    sw      x4, 0(x2)
    sw      x26, 4(x2)
    sw      x27, 8(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x4, 0x36925814)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x26, 0x36925814)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x27, 0x36925814)

    RVTEST_IO_WRITE_STR(x31, "# Test part E  - Complete\n");

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
test_B_data:
    .word 0xABCDFFFF
test_C_data:
    .word 0x12345678
test_D_data:
    .word 0xFEDCBA98
test_E_data:
    .word 0x36925814

# Output data section.
RV_COMPLIANCE_DATA_BEGIN
    .align 4

test_A1_res:
    .fill 6, 4, -1
test_A2_res:
    .fill 6, 4, -1
test_A3_res:
    .fill 6, 4, -1
test_A4_res:
    .fill 6, 4, -1
test_A5_res:
    .fill 6, 4, -1
test_B_res:
    .fill 8, 4, -1
test_C_res:
    .fill 1, 4, -1
test_D_res:
    .fill 2, 4, -1
test_E_res:
    .fill 3, 4, -1

RV_COMPLIANCE_DATA_END     # End of test output data region.
