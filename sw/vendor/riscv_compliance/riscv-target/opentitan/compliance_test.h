// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// RISC-V Compliance Test Header File

#ifndef _COMPLIANCE_TEST_H
#define _COMPLIANCE_TEST_H

#include "riscv_test.h"

//-----------------------------------------------------------------------
// RV Compliance Macros
//-----------------------------------------------------------------------
#define RV_COMPLIANCE_HALT                                                    \
        la sp, _stack_start;                                                  \
        j dump_signature;                                                     \
      loop_forever:                                                           \
        wfi;                                                                  \
        j loop_forever;                                                       \

#define RV_COMPLIANCE_RV32M                                                   \
        RVTEST_RV32M                                                          \


#define RV_COMPLIANCE_CODE_BEGIN                                              \
        RVTEST_CODE_BEGIN                                                     \

#define RV_COMPLIANCE_CODE_END                                                \
        RVTEST_CODE_END                                                       \

#define RV_COMPLIANCE_DATA_BEGIN                                              \
        .section .test.output;                                                \
        RVTEST_DATA_BEGIN                                                     \

#define RV_COMPLIANCE_DATA_END                                                \
        RVTEST_DATA_END                                                       \

#endif
