# RISC-V Compliance Test I-CSRRWI-01
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
# Description: Testing instruction CSRRWI.

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
    RVTEST_IO_WRITE_STR(x31, "# Test part A - general test of CSRRWI\n");

    # Address for test results
    la      x15, test_A_res

    # Register initialization
    csrrw   x0, mscratch, x0

    # Test
    csrrwi  x2, mscratch, 1
    csrrwi  x4, mscratch, 0
    csrrwi  x6, mscratch, 0x1F
    csrrwi  x28, mscratch, 0x0F
    csrrwi  x30, mscratch, 0x10
    csrrwi  x31, mscratch, 0

    # Store results
    sw      x0, 0(x15)
    sw      x2, 4(x15)
    sw      x4, 8(x15)
    sw      x6, 12(x15)
    sw      x28, 16(x15)
    sw      x30, 20(x15)
    sw      x31, 24(x15)

    //
    // Assert
    //
    RVTEST_IO_CHECK()
    RVTEST_IO_ASSERT_GPR_EQ(x15, x0,  0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x15, x2,  0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x15, x4,  0x00000001)
    RVTEST_IO_ASSERT_GPR_EQ(x15, x6,  0x00000000)
    RVTEST_IO_ASSERT_GPR_EQ(x15, x28, 0x0000001F)
    RVTEST_IO_ASSERT_GPR_EQ(x15, x30, 0x0000000F)
    RVTEST_IO_ASSERT_GPR_EQ(x15, x31, 0x00000010)

    RVTEST_IO_WRITE_STR(x31, "# Test part A1  - Complete\n");

    # ---------------------------------------------------------------------------------------------
    RVTEST_IO_WRITE_STR(x31, "# Test part B - testing writing to x0\n");

    # Address for test results
    la      x1, test_B_res

    # Test
    csrrwi  x0, mscratch, 0xF
    csrrwi  x0, mscratch, 0

    # store results
    sw      x0, 0(x1)

    RVTEST_IO_ASSERT_GPR_EQ(x1, x0, 0x00000000)

    RVTEST_IO_WRITE_STR(x31, "# Test part A2  - Complete\n");

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
    .fill 7, 4, -1
test_B_res:
    .fill 1, 4, -1

RV_COMPLIANCE_DATA_END     # End of test output data region.
