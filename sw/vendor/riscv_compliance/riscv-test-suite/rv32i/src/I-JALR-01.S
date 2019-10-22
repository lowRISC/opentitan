# RISC-V Compliance Test I-JALR-01
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
# Description: Testing instruction JALR.

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
    RVTEST_IO_WRITE_STR(x31, "# Test part A1 - general test of JALR\n");

    # Address for test results
    la      x1, test_A1_res

    # Register initialization
    li      x2, 0x12345678

    # Test
    la      x3, 1f
    jalr    x0, x3, 0
    li      x2, 0

1:

    # Store results
    sw      x0, 0(x1)
    sw      x2, 4(x1)

    //
    // Assert
    //
    RVTEST_IO_CHECK()
    RVTEST_IO_ASSERT_GPR_EQ(x1, x0, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x1, x2, 0x12345678)

    RVTEST_IO_WRITE_STR(x31, "# Test part A1  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part A2 - test of JALR - jumps forward, backward\n");

    # Address for test results
    la      x1, test_A2_res

    # Register initialization
    li      x2, 0xFFFFFFFF
    li      x3, 0xFFFFFFFF
    li      x4, 0x0FEDCBA9

    # Test
    la      x31, 2f
    jalr    x0, x31, 0
    li      x2, 0
    li      x3, 0
    li      x4, 0

1:
    li      x3, 0x87654321
    la      x5, 3f
    jalr    x0, x5, 0
    li      x2, 0
    li      x3, 0
    li      x4, 0

2:
    li      x2, 0x9ABCDEF0
    la      x15, 1b
    jalr    x0, x15, 0
    li      x2, 0
    li      x3, 0
    li      x4, 0

3:

    # Store results
    sw      x0, 0(x1)
    sw      x2, 4(x1)
    sw      x3, 8(x1)
    sw      x4, 12(x1)

    RVTEST_IO_ASSERT_GPR_EQ(x1, x0, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x1, x2, 0x9ABCDEF0)
    RVTEST_IO_ASSERT_GPR_EQ(x1, x3, 0x87654321)
    RVTEST_IO_ASSERT_GPR_EQ(x1, x4, 0x0FEDCBA9)

    RVTEST_IO_WRITE_STR(x31, "# Test part A2  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part B1 - test of JALR - linking\n");

    # Addresses for test data and results
    la      x9, test_B1_data
    la      x10, test_B1_res

    # Register initialization
    li      x2, 0xFFFFFFFF
    li      x3, 0xFFFFFFFF
    li      x4, 0xFFFFFFFF
    li      x5, 0xFFFFFFFF
    li      x6, 0x55555555

    # Load testdata
    lw      x25, 0(x9)
    lw      x24, 4(x9)

    # Test
    la      x7, 1f
    jalr    x1, x7, 0

B1a_link:
    li      x3, 0x22222222
    la      x8, 2f
    jalr    x31, x8, 0

B1b_link:
    li      x5, 0x44444444
    la      x30, 3f
    jalr    x0, x30, 0

1:
    li      x2, 0x11111111
    jalr    x0, x1, 0
    li      x2, 0
    li      x3, 0
    li      x4, 0
    li      x5, 0
    li      x6, 0

2:
    li      x4, 0x33333333
    jalr    x0, x31, 0
    li      x2, 0
    li      x3, 0
    li      x4, 0
    li      x5, 0
    li      x6, 0

3:
    xor     x7, x1, x25
    xor     x8, x31, x24


    # Store results
    sw      x2, 0(x10)
    sw      x3, 4(x10)
    sw      x4, 8(x10)
    sw      x5, 12(x10)
    sw      x6, 16(x10)
    sw      x7, 20(x10)
    sw      x8, 24(x10)

    RVTEST_IO_ASSERT_GPR_EQ(x10, x2, 0x11111111)
    RVTEST_IO_ASSERT_GPR_EQ(x10, x3, 0x22222222)
    RVTEST_IO_ASSERT_GPR_EQ(x10, x4, 0x33333333)
    RVTEST_IO_ASSERT_GPR_EQ(x10, x5, 0x44444444)
    RVTEST_IO_ASSERT_GPR_EQ(x10, x6, 0x55555555)
    RVTEST_IO_ASSERT_GPR_EQ(x10, x7, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x10, x8, 0x00000000)

    RVTEST_IO_WRITE_STR(x31, "# Test part A3  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part B2 - test of JALR - linking, low bit of address is cleared\n");

    # Addresses for test data and results
    la      x9, test_B2_data
    la      x10, test_B2_res

    # Register initialization
    li      x2, 0xFFFFFFFF
    li      x3, 0xFFFFFFFF
    li      x4, 0xFFFFFFFF
    li      x5, 0xFFFFFFFF
    li      x6, 0xFFFFFFFF

    # Load testdata
    lw      x24, 0(x9)
    lw      x25, 4(x9)

    # Test
    la      x15, 2f
    jalr    x0, x15, 0

1:
    li      x3, 0x77777777
    jalr    x0, x31, 1
    li      x2, 0
    li      x3, 0
    li      x4, 0
    li      x5, 0
    li      x6, 0

2:
    li      x2, 0x66666666
    la      x31, 1b + 1
    jalr    x31, x31, 0

B2b_link:
    li      x4, 0x88888888
    la      x1, 3f + 1
    jalr    x1, x1, 0

B2c_link:
    li      x6, 0xAAAAAAAA
    la      x30, 4f
    jalr    x0, x30, 0

3:
    li      x5, 0x99999999
    jalr    x0, x1, 1
    li      x2, 0
    li      x3, 0
    li      x4, 0
    li      x5, 0
    li      x6, 0

4:
    xor     x7, x31, x24
    xor     x8, x1, x25

    # Store results
    sw      x2, 0(x10)
    sw      x3, 4(x10)
    sw      x4, 8(x10)
    sw      x5, 12(x10)
    sw      x6, 16(x10)
    sw      x7, 20(x10)
    sw      x8, 24(x10)

    RVTEST_IO_ASSERT_GPR_EQ(x10, x2, 0x66666666)
    RVTEST_IO_ASSERT_GPR_EQ(x10, x3, 0x77777777)
    RVTEST_IO_ASSERT_GPR_EQ(x10, x4, 0x88888888)
    RVTEST_IO_ASSERT_GPR_EQ(x10, x5, 0x99999999)
    RVTEST_IO_ASSERT_GPR_EQ(x10, x6, 0xAAAAAAAA)
    RVTEST_IO_ASSERT_GPR_EQ(x10, x7, 0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x10, x8, 0x00000000)

    RVTEST_IO_WRITE_STR(x31, "# Test part A4  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part C - JALR using immediate\n");

    # Address for test results
    la      x1, test_C_res

    # Test
    li      x4, 0x11111111
    la      x3, 1f - 1
    jalr    x0, x3, 1
    li      x4, 0

1:
    li      x5, 0x22222222
    la      x3, 1f + 1
    jalr    x0, x3, 0xFFFFFFFF
    li      x5, 0

1:
    li      x6, 0x33333333
    la      x3, 1f - 2047
    jalr    x0, x3, 0x000007FF
    li      x6, 0

1:
    li      x7, 0x44444444
    la      x3, 1f + 2048
    jalr    x0, x3, 0xFFFFF800
    li      x7, 0

1:
    # Store results
    sw      x4, 0(x1)
    sw      x5, 4(x1)
    sw      x6, 8(x1)
    sw      x7, 12(x1)

    RVTEST_IO_ASSERT_GPR_EQ(x1, x4, 0x11111111)
    RVTEST_IO_ASSERT_GPR_EQ(x1, x5, 0x22222222)
    RVTEST_IO_ASSERT_GPR_EQ(x1, x6, 0x33333333)
    RVTEST_IO_ASSERT_GPR_EQ(x1, x7, 0x44444444)

    RVTEST_IO_WRITE_STR(x31, "# Test part A5  - Complete\n");

    RVTEST_IO_WRITE_STR(x31, "# Test End\n")

 # ---------------------------------------------------------------------------------------------
    # HALT
    RV_COMPLIANCE_HALT



RV_COMPLIANCE_CODE_END

# Input data section.
    .data
    .align 4

test_B1_data:
    .word B1a_link
    .word B1b_link
test_B2_data:
    .word B2b_link
    .word B2c_link

# Output data section.
RV_COMPLIANCE_DATA_BEGIN
    .align 4

test_A1_res:
    .fill 2, 4, -1
test_A2_res:
    .fill 4, 4, -1
test_B1_res:
    .fill 7, 4, -1
test_B2_res:
    .fill 7, 4, -1
test_C_res:
    .fill 4, 4, -1

RV_COMPLIANCE_DATA_END     # End of test output data region.
