# RISC-V Compliance Test I-CSRRS-01
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
# Description: Testing instruction CSRRS.

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
    RVTEST_IO_WRITE_STR(x31, "# Test part A1 - general test of CSRRS\n");

    # Address for test results
    la      x15, test_A1_res

    # Register initialization
    li      x1, 1
    li      x2, 0
    li      x3, 0x7FF0FFFF
    li      x4, 0x80000000
    li      x5, -1
    csrrw   x0, mscratch, x0

    # Test
    csrrs   x1, mscratch, x1
    csrrw   x1, mscratch, x0

    csrrs   x2, mscratch, x2
    csrrw   x2, mscratch, x0

    csrrs   x3, mscratch, x3
    csrrw   x3, mscratch, x0

    csrrs   x4, mscratch, x4
    csrrw   x4, mscratch, x0

    csrrs   x5, mscratch, x5
    csrrw   x5, mscratch, x0

    # Store results
    sw      x0, 0(x15)
    sw      x1, 4(x15)
    sw      x2, 8(x15)
    sw      x3, 12(x15)
    sw      x4, 16(x15)
    sw      x5, 20(x15)

    //
    // Assert
    //
    RVTEST_IO_CHECK()
    RVTEST_IO_ASSERT_GPR_EQ(x15, x0, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x15, x1, 0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x15, x2, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x15, x3, 0x7FF0FFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x15, x4, 0x80000000)
    RVTEST_IO_ASSERT_GPR_EQ(x15, x5, 0xFFFFFFFF)

    RVTEST_IO_WRITE_STR(x31, "# Test part A1  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A2 - general test of CSRRS\n");

    # Address for test results
    la      x5, test_A2_res

    # Register initialization
    li      x11, 1
    li      x12, 0
    li      x13, 0x7FF0FFFF
    li      x14, 0x80000000
    li      x15, -1
    csrrw   x0, mscratch, x0

    # Test
    csrrs   x11, mscratch, x11
    csrrs   x12, mscratch, x12
    csrrs   x13, mscratch, x13
    csrrs   x14, mscratch, x14
    csrrs   x15, mscratch, x15
    csrrs   x16, mscratch, x0


    # Store results
    sw      x11, 0(x5)
    sw      x12, 4(x5)
    sw      x13, 8(x5)
    sw      x14, 12(x5)
    sw      x15, 16(x5)
    sw      x16, 20(x5)

    RVTEST_IO_ASSERT_GPR_EQ(x5, x11, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x5, x12, 0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x5, x13, 0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x5, x14, 0x7FF0FFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x5, x15, 0xFFF0FFFF)
    RVTEST_IO_ASSERT_GPR_EQ(x5, x16, 0xFFFFFFFF)

    RVTEST_IO_WRITE_STR(x31, "# Test part A2  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part B - testing forwarding between instructions\n");

    # Address for test results
    la      x26, test_B_res

    # Register initialization
    li      x21, 0x12345678
    csrrw   x0, mscratch, x0

    # Test
    csrrs   x22, mscratch, x21
    csrrs   x23, mscratch, x22
    csrrw   x23, mscratch, x0
    csrrs   x24, mscratch, x23
    csrrs   x25, mscratch, x0

    # store results
    sw      x21, 0(x26)
    sw      x22, 4(x26)
    sw      x23, 8(x26)
    sw      x24, 12(x26)
    sw      x25, 16(x26)

    RVTEST_IO_ASSERT_GPR_EQ(x26, x21, 0x12345678)
    RVTEST_IO_ASSERT_GPR_EQ(x26, x22, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x26, x23, 0x12345678)
    RVTEST_IO_ASSERT_GPR_EQ(x26, x24, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x26, x25, 0x12345678)

    RVTEST_IO_WRITE_STR(x31, "# Test part A3  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part C - testing writing to x0 and reading from x0\n");

    # Address for test results
    la      x1, test_C_res

    # Register initialization
    li      x30, 0x42726E6F
    csrrw   x0, mscratch, x30

    # Test
    csrrs   x0, mscratch, x30

    # store results
    sw      x0, 0(x1)
    sw      x30, 4(x1)


    RVTEST_IO_ASSERT_GPR_EQ(x1, x0,  0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x1, x30, 0x42726E6F)

    RVTEST_IO_WRITE_STR(x31, "# Test part A4  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part D - testing forwarding throught x0\n");

    # Address for test results
    la      x2, test_D_res

    # Register initialization
    li      x31, 0xF7FF8818
    csrrw   x0, mscratch, x31

    # Test
    csrrs   x0, mscratch, x0
    csrrs   x0, mscratch, x0
    csrrs   x31, mscratch, x0

    # store results
    sw      x0, 0(x2)
    sw      x31, 4(x2)


    RVTEST_IO_ASSERT_GPR_EQ(x2, x0,  0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x31, 0xF7FF8818)

    RVTEST_IO_WRITE_STR(x31, "# Test part A5  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part E - testing csrrs with same dst and src registers\n");

    # Address for test results
    la      x2, test_E_res

    # Register initialization
    li      x7, 0x32165498
    li      x5, 0x96385274
    csrrw   x0, mscratch, x0

    # Test
    csrrs   x5, mscratch, x5
    csrrs   x7, mscratch, x7
    csrrs   x8, mscratch, x8

    # Store results
    sw      x5, 0(x2)
    sw      x7, 4(x2)
    sw      x8, 8(x2)

    RVTEST_IO_ASSERT_GPR_EQ(x2, x5, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x7, 0x96385274)
    RVTEST_IO_ASSERT_GPR_EQ(x2, x8, 0xB63E56FC)

    RVTEST_IO_WRITE_STR(x31, "# Test part B  - Complete\n");

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

test_A1_res:
    .fill 6, 4, -1
test_A2_res:
    .fill 6, 4, -1
test_B_res:
    .fill 5, 4, -1
test_C_res:
    .fill 2, 4, -1
test_D_res:
    .fill 2, 4, -1
test_E_res:
    .fill 3, 4, -1

RV_COMPLIANCE_DATA_END     # End of test output data region.
