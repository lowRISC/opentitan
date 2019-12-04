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
        .globl oled_clear;                                                    \
        .globl oled_write_str;                                                \
        .globl oled_write_disp;                                               \
        RVTEST_RV32M                                                          \


#define RV_COMPLIANCE_CODE_BEGIN                                              \
        RVTEST_CODE_BEGIN                                                     \
        la sp, _stack_start;                                                  \
        li a0, 1;                                                             \
        jal oled_clear;                                                       \
        la a0, _rv_compliance_str;                                            \
        la a1, 0;                                                             \
        la a2, 0;                                                             \
        jal oled_write_str;                                                   \
        la a0, _rv_test_name_str;                                             \
        la a1, 2;                                                             \
        la a2, 0;                                                             \
        jal oled_write_str;                                                   \
        jal oled_write_disp;                                                  \

#define RV_COMPLIANCE_CODE_END                                                \
        RVTEST_CODE_END                                                       \

#define Stringify(x) #x
#define Stringify2(x) Stringify(x)

#define RV_COMPLIANCE_DATA_BEGIN                                              \
      _rv_test_name_str:                                                      \
        .asciz Stringify2(RISCV_TEST_NAME);                                   \
      _rv_compliance_str:                                                     \
        .asciz "RISCV Compliance";                                            \
        .section .test.output;                                                \
        RVTEST_DATA_BEGIN                                                     \

#define RV_COMPLIANCE_DATA_END                                                \
        RVTEST_DATA_END                                                       \

#endif
