# RISC-V Compliance Test I-XORI-01
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
# Description: Testing instruction XORI.

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
    RVTEST_IO_WRITE_STR(x31, "# Test part A1 - general test of value 0 with 0, 1, -1, MIN, MAX immediate values\n");

    # Addresses for test data and results
    la      x1, test_A1_data
    la      x2, test_A1_res

    # Load testdata
    lw      x3, 0(x1)

    # Test
    xori    x4, x3, 1
    xori    x5, x3, 0x7FF
    xori    x6, x3, 0xFFFFFFFF
    xori    x7, x3, 0
    xori    x8, x3, 0xFFFFF800

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
    RVTEST_IO_ASSERT_GPR_EQ(x2, x5, 0x000007FF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x6, 0xFFFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x7, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x8, 0xFFFFF800)

    RVTEST_IO_WRITE_STR(x31, "# Test part A1  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A2 - general test of value 1 with 0, 1, -1, MIN, MAX immediate values\n");

    # Addresses for test data and results
    la      x1, test_A2_data
    la      x2, test_A2_res

    # Load testdata
    lw      x8, 0(x1)

    # Test
    xori    x9, x8, 1
    xori    x10, x8, 0x7FF
    xori    x11, x8, 0xFFFFFFFF
    xori    x12, x8, 0
    xori    x13, x8, 0xFFFFF800

    # Store results
    sw      x8, 0(x2)
    sw      x9, 4(x2)
    sw      x10, 8(x2)
    sw      x11, 12(x2)
    sw      x12, 16(x2)
    sw      x13, 20(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x8,  0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x9,  0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x10, 0x000007FE)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x11, 0xFFFFFFFE)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x12, 0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x13, 0xFFFFF801)

    RVTEST_IO_WRITE_STR(x31, "# Test part A2  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A3 - general test of value -1 with 0, 1, -1, MIN, MAX immediate values\n");

    # Addresses for test data and results
    la      x1, test_A3_data
    la      x2, test_A3_res

    # Load testdata
    lw      x13, 0(x1)

    # Test
    xori    x14, x13, 1
    xori    x15, x13, 0x7FF
    xori    x16, x13, 0xFFFFFFFF
    xori    x17, x13, 0
    xori    x18, x13, 0xFFFFF800

    # Store results
    sw      x13, 0(x2)
    sw      x14, 4(x2)
    sw      x15, 8(x2)
    sw      x16, 12(x2)
    sw      x17, 16(x2)
    sw      x18, 20(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x13, 0xFFFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x14, 0xFFFFFFFE)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x15, 0xFFFFF800)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x16, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x17, 0xFFFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x18, 0x000007FF)

    RVTEST_IO_WRITE_STR(x31, "# Test part A3  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A4 - general test of value 0x7FFFFFFF with 0, 1, -1, MIN, MAX immediate values\n");

    # Addresses for test data and results
    la      x1, test_A4_data
    la      x2, test_A4_res

    # Load testdata
    lw      x18, 0(x1)

    # Test
    xori    x19, x18, 1
    xori    x20, x18, 0x7FF
    xori    x21, x18, 0xFFFFFFFF
    xori    x22, x18, 0
    xori    x23, x18, 0xFFFFF800

    # Store results
    sw      x18, 0(x2)
    sw      x19, 4(x2)
    sw      x20, 8(x2)
    sw      x21, 12(x2)
    sw      x22, 16(x2)
    sw      x23, 20(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x18, 0x7FFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x19, 0x7FFFFFFE)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x20, 0x7FFFF800)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x21, 0x80000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x22, 0x7FFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x23, 0x800007FF)

    RVTEST_IO_WRITE_STR(x31, "# Test part A4  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A5 - general test of value 0x80000000 with 0, 1, -1, MIN, MAX immediate values\n");

    # Addresses for test data and results
    la      x1, test_A5_data
    la      x2, test_A5_res

    # Load testdata
    lw      x23, 0(x1)

    # Test
    xori    x24, x23, 1
    xori    x25, x23, 0x7FF
    xori    x26, x23, 0xFFFFFFFF
    xori    x27, x23, 0
    xori    x28, x23, 0xFFFFF800

    # Store results
    sw      x23, 0(x2)
    sw      x24, 4(x2)
    sw      x25, 8(x2)
    sw      x26, 12(x2)
    sw      x27, 16(x2)
    sw      x28, 20(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x23, 0x80000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x24, 0x80000001)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x25, 0x800007FF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x26, 0x7FFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x27, 0x80000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x28, 0x7FFFF800)

    RVTEST_IO_WRITE_STR(x31, "# Test part A5  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part B - testing forwarding between instructions\n");

    # Addresses for test data and results
    la      x26, test_B_data
    la      x27, test_B_res

    # Load testdata
    lw      x28, 0(x26)

    # Test
    xori    x29, x28, 0x7F
    xori    x30, x29, 0x3F
    xori    x31, x30, 0x1F
    xori    x1, x31, 0x0F
    xori    x2, x1, 0x07
    xori    x3, x2, 0x03

    # Store results
    sw      x28, 0(x27)
    sw      x29, 4(x27)
    sw      x30, 8(x27)
    sw      x31, 12(x27)
    sw      x1, 16(x27)
    sw      x2, 20(x27)
    sw      x3, 24(x27)


    RVTEST_IO_ASSERT_GPR_EQ(x27, x28, 0xABCDFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x27, x29, 0xABCDFF80)
    RVTEST_IO_ASSERT_GPR_EQ(x27, x30, 0xABCDFFBF)
    RVTEST_IO_ASSERT_GPR_EQ(x27, x31, 0xABCDFFA0)
    RVTEST_IO_ASSERT_GPR_EQ(x27, x1,  0xABCDFFAF)
    RVTEST_IO_ASSERT_GPR_EQ(x27, x2,  0xABCDFFA8)
    RVTEST_IO_ASSERT_GPR_EQ(x27, x3,  0xABCDFFAB)

    RVTEST_IO_WRITE_STR(x31, "# Test part B  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part C - testing writing to x0\n");

    # Addresses for test data and results
    la      x1, test_C_data
    la      x2, test_C_res

    # Load testdata
    lw      x5, 0(x1)

    # Test
    xori    x0, x5, 1

    # Store results
    sw      x0, 0(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x0, 0x00000000)

    RVTEST_IO_WRITE_STR(x31, "# Test part C  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part D - testing forwarding throught x0\n");

    # Addresses for test data and results
    la      x1, test_D_data
    la      x2, test_D_res

    # Load testdata
    lw      x5, 0(x1)

    # Test
    xori    x0, x5, 1
    xori    x5, x0, 1

    # Store results
    sw      x0, 0(x2)
    sw      x5, 4(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x0, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x5, 0x00000001)

    RVTEST_IO_WRITE_STR(x31, "# Test part D  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part E - testing moving (xori with 0)\n");

    # Addresses for test data and results
    la      x1, test_E_data
    la      x2, test_E_res

    # Load testdata
    lw      x3, 0(x1)

    # Test
    xori    x4, x3, 0
    xori    x5, x4, 0
    xori    x6, x5, 0
    xori    x14, x6, 0
    xori    x15, x14, 0
    xori    x16, x15, 0
    xori    x25, x16, 0
    xori    x26, x25, 0
    xori    x27, x26, 0

    # Store results
    sw      x3, 0(x2)
    sw      x4, 4(x2)
    sw      x26, 8(x2)
    sw      x27, 12(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x3, 0x36925814)
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
    .fill 7, 4, -1
test_C_res:
    .fill 1, 4, -1
test_D_res:
    .fill 2, 4, -1
test_E_res:
    .fill 4, 4, -1

RV_COMPLIANCE_DATA_END
