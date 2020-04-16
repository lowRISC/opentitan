# RISC-V Compliance Test I-CSRRW-01
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
# Description: Testing instruction CSRRW.

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
    RVTEST_IO_WRITE_STR(x31, "# Test part A - general test of CSRRW\n");

    # Address for test results
    la      x15, test_A_res

    # Register initialization
    li      x1, 1
    li      x3, 0
    li      x5, -1
    li      x27, 0x7FFFFFFF
    li      x29, 0x80000000
    csrrw   x0, mscratch, x0

    # Test
    csrrw   x2, mscratch, x1
    csrrw   x4, mscratch, x3
    csrrw   x6, mscratch, x5
    csrrw   x28, mscratch, x27
    csrrw   x30, mscratch, x29
    csrrw   x31, mscratch, x0

    # Store results
    sw      x2, 0(x15)
    sw      x4, 4(x15)
    sw      x6, 8(x15)
    sw      x28, 12(x15)
    sw      x30, 16(x15)
    sw      x31, 20(x15)

    //
    // Assert
    //
    RVTEST_IO_CHECK()
    RVTEST_IO_ASSERT_GPR_EQ(x15, x2,  0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x15, x4,  0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x15, x6,  0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x15, x28, 0xFFFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x15, x30, 0x7FFFFFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x15, x31, 0x80000000)

    RVTEST_IO_WRITE_STR(x31, "# Test part A1  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part B - testing forwarding between instructions\n");

    # Address for test results
    la      x26, test_B_res

    # Register initialization
    li      x1, 0x12345678
    li      x2, 0x9ABCDEF0

    # Test
    csrrw   x0, mscratch, x1
    csrrw   x3, mscratch, x2
    csrrw   x4, mscratch, x3
    csrrw   x5, mscratch, x4
    csrrw   x6, mscratch, x0

    # store results
    sw      x3, 0(x26)
    sw      x4, 4(x26)
    sw      x5, 8(x26)
    sw      x6, 12(x26)

    RVTEST_IO_ASSERT_GPR_EQ(x26, x3, 0x12345678)
    RVTEST_IO_ASSERT_GPR_EQ(x26, x4, 0x9ABCDEF0)
    RVTEST_IO_ASSERT_GPR_EQ(x26, x5, 0x12345678)
    RVTEST_IO_ASSERT_GPR_EQ(x26, x6, 0x9ABCDEF0)

    RVTEST_IO_WRITE_STR(x31, "# Test part A2  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part C - testing writing to x0\n");

    # Address for test results
    la      x1, test_C_res

    # Register initialization
    li      x2, 0x42726E6F

    # Test
    csrrw   x0, mscratch, x2
    csrrw   x0, mscratch, x0

    # store results
    sw      x0, 0(x1)

    RVTEST_IO_ASSERT_GPR_EQ(x1, x0, 0x00000000)

    RVTEST_IO_WRITE_STR(x31, "# Test part A3  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part D - testing forwarding throught x0\n");

    # Address for test results
    la      x2, test_D_res

    # Register initialization
    li      x27, 0xF7FF8818

    # Test
    csrrw   x0, mscratch, x27
    csrrw   x0, mscratch, x0
    csrrw   x0, mscratch, x0
    csrrw   x5, mscratch, x0

    # store results
    sw      x0, 0(x2)
    sw      x5, 4(x2)


    RVTEST_IO_ASSERT_GPR_EQ(x2, x0, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x5, 0x00000000)

    RVTEST_IO_WRITE_STR(x31, "# Test part A4  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part E - testing csrrw with same dst and src registers\n");

    # Address for test results
    la      x2, test_E_res

    # Register initialization
    li      x7, 0x32165498
    li      x6, 0x14725836
    li      x5, 0x96385274

    # Test
    csrrw   x0, mscratch, x6
    csrrw   x5, mscratch, x5
    csrrw   x7, mscratch, x7
    csrrw   x8, mscratch, x0

    # Store results
    sw      x5, 0(x2)
    sw      x7, 4(x2)
    sw      x8, 8(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x5, 0x14725836)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x7, 0x96385274)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x8, 0x32165498)

    RVTEST_IO_WRITE_STR(x31, "# Test part A5  - Complete\n");

    RVTEST_IO_WRITE_STR(x31, "# Test End\n")

 # ---------------------------------------------------------------------------------------------
    # HALT
    RV_COMPLIANCE_HALT

RV_COMPLIANCE_CODE_END

# Input data section.
    .data
    .align 4


# Output data section.
RV_COMPLIANCE_DATA_BEGIN
    .align 4

test_A_res:
    .fill 6, 4, -1
test_B_res:
    .fill 4, 4, -1
test_C_res:
    .fill 1, 4, -1
test_D_res:
    .fill 2, 4, -1
test_E_res:
    .fill 3, 4, -1

RV_COMPLIANCE_DATA_END     # End of test output data region.
