# RISC-V Compliance Test I-SLTU-01
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
# Description: Testing instruction SLTU.

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
    li      x4, 1
    li      x5, 0x7FFFFFFF
    li      x6, 0xFFFFFFFF
    li      x7, 0
    li      x8, 0x80000000

    # Test
    sltu   x4, x3, x4
    sltu   x5, x3, x5
    sltu   x6, x3, x6
    sltu   x7, x3, x7
    sltu   x8, x3, x8

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
    RVTEST_IO_ASSERT_GPR_EQ(x2, x4, 0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x5, 0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x6, 0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x7, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x8, 0x00000001)

    RVTEST_IO_WRITE_STR(x31, "# Test part A1  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A2 - general test of value 1 with 0, 1, -1, MIN, MAX register values\n");

    # Addresses for test data and results
    la      x1, test_A2_data
    la      x2, test_A2_res

    # Load testdata
    lw      x8, 0(x1)

    # Register initialization
    li      x9, 1
    li      x10, 0x7FFFFFFF
    li      x11, 0xFFFFFFFF
    li      x12, 0
    li      x13, 0x80000000

    # Test
    sltu   x9, x8, x9
    sltu   x10, x8, x10
    sltu   x11, x8, x11
    sltu   x12, x8, x12
    sltu   x13, x8, x13

    # Store results
    sw      x8, 0(x2)
    sw      x9, 4(x2)
    sw      x10, 8(x2)
    sw      x11, 12(x2)
    sw      x12, 16(x2)
    sw      x13, 20(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x8,  0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x9,  0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x10, 0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x11, 0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x12, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x13, 0x00000001)

    RVTEST_IO_WRITE_STR(x31, "# Test part A2  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A3 - general test of value -1 with 0, 1, -1, MIN, MAX register values\n");

    # Addresses for test data and results
    la      x1, test_A3_data
    la      x2, test_A3_res

    # Load testdata
    lw      x13, 0(x1)

    # Register initialization
    li      x14, 1
    li      x15, 0x7FFFFFFF
    li      x16, 0xFFFFFFFF
    li      x17, 0
    li      x18, 0x80000000

    # Test
    sltu   x14, x13, x14
    sltu   x15, x13, x15
    sltu   x16, x13, x16
    sltu   x17, x13, x17
    sltu   x18, x13, x18

    # Store results
    sw      x13, 0(x2)
    sw      x14, 4(x2)
    sw      x15, 8(x2)
    sw      x16, 12(x2)
    sw      x17, 16(x2)
    sw      x18, 20(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x13, 0xFFFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x14, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x15, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x16, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x17, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x18, 0x00000000)

    RVTEST_IO_WRITE_STR(x31, "# Test part A3  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A4 - general test of value 0x7FFFFFFF with 0, 1, -1, MIN, MAX register values\n");

    # Addresses for test data and results
    la      x1, test_A4_data
    la      x2, test_A4_res

    # Load testdata
    lw      x18, 0(x1)

    # Register initialization
    li      x19, 1
    li      x20, 0x7FFFFFFF
    li      x21, 0xFFFFFFFF
    li      x22, 0
    li      x23, 0x80000000

    # Test
    sltu   x19, x18, x19
    sltu   x20, x18, x20
    sltu   x21, x18, x21
    sltu   x22, x18, x22
    sltu   x23, x18, x23

    # Store results
    sw      x18, 0(x2)
    sw      x19, 4(x2)
    sw      x20, 8(x2)
    sw      x21, 12(x2)
    sw      x22, 16(x2)
    sw      x23, 20(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x18, 0x7FFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x19, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x20, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x21, 0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x22, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x23, 0x00000001)

    RVTEST_IO_WRITE_STR(x31, "# Test part A4  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A5 - general test of value 0x80000000 with 0, 1, -1, MIN, MAX register values\n");

    # Addresses for test data and results
    la      x1, test_A5_data
    la      x2, test_A5_res

    # Load testdata
    lw      x23, 0(x1)

    # Register initialization
    li      x24, 1
    li      x25, 0x7FFFFFFF
    li      x26, 0xFFFFFFFF
    li      x27, 0
    li      x28, 0x80000000

    # Test
    sltu   x24, x23, x24
    sltu   x25, x23, x25
    sltu   x26, x23, x26
    sltu   x27, x23, x27
    sltu   x28, x23, x28

    # Store results
    sw      x23, 0(x2)
    sw      x24, 4(x2)
    sw      x25, 8(x2)
    sw      x26, 12(x2)
    sw      x27, 16(x2)
    sw      x28, 20(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x23, 0x80000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x24, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x25, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x26, 0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x27, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x28, 0x00000000)

    RVTEST_IO_WRITE_STR(x31, "# Test part A5  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part B - testing writing to x0\n");

    # Addresses for test data and results
    la      x26, test_B_data
    la      x27, test_B_res

    # Load testdata
    lw      x1, 0(x26)

    # Register initialization
    li      x2, 0xFFFFFFFF

    # Test
    sltu    x0, x1, x2

    # Store results
    sw      x0, 0(x27)
    sw      x1, 4(x27)
    sw      x2, 8(x27)

    RVTEST_IO_ASSERT_GPR_EQ(x27, x0, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x27, x1, 0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x27, x2, 0xFFFFFFFF)

    RVTEST_IO_WRITE_STR(x31, "# Test part B  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part C - testing compare x0\n");

    # Addresses for test data and results
    la      x31, test_C_res

    # Register initialization
    li      x1, 1
    li      x2, 0x7FF
    li      x3, 0xFFFFFFFF
    li      x4, 0
    li      x5, 0xFFFFF800

    # Test
    sltu   x6, x0, x1
    sltu   x7, x0, x2
    sltu   x8, x0, x3
    sltu   x9, x0, x4
    sltu   x10, x0, x5
    sltu   x11, x1, x0
    sltu   x12, x2, x0
    sltu   x13, x3, x0
    sltu   x14, x4, x0
    sltu   x15, x5, x0

    # Store results
    sw      x6, 0(x31)
    sw      x7, 4(x31)
    sw      x8, 8(x31)
    sw      x9, 12(x31)
    sw      x10, 16(x31)
    sw      x11, 20(x31)
    sw      x12, 24(x31)
    sw      x13, 28(x31)
    sw      x14, 32(x31)
    sw      x15, 36(x31)

    RVTEST_IO_ASSERT_GPR_EQ(x31, x6,  0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x31, x7,  0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x31, x8,  0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x31, x9,  0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x31, x10, 0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x31, x11, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x31, x12, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x31, x13, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x31, x14, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x31, x15, 0x00000000)

    RVTEST_IO_WRITE_STR(x31, "# Test part C  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part D - testing forwarding between instructions\n");

    # Addresses for test data and results
    la      x31, test_D_res

    # Register initialization
    li      x3, 0x1

    # Test
    sltu   x1, x0, x3
    sltu   x2, x1, x3
    sltu   x28, x2, x3
    sltu   x29, x28, x3
    sltu   x30, x29, x3

    # Store results
    sw      x1, 0(x31)
    sw      x2, 4(x31)
    sw      x28, 8(x31)
    sw      x29, 12(x31)
    sw      x30, 16(x31)

    RVTEST_IO_ASSERT_GPR_EQ(x31, x1,  0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x31, x2,  0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x31, x28, 0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x31, x29, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x31, x30, 0x00000001)

    RVTEST_IO_WRITE_STR(x31, "# Test part D  - Complete\n");

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
    .word 1

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
    .fill 3, 4, -1
test_C_res:
    .fill 10, 4, -1
test_D_res:
    .fill 5, 4, -1


RV_COMPLIANCE_DATA_END
