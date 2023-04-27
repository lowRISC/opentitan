// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Ibex specific macros
#define SIGNATURE_ADDR 0x8ffffff8

// signatue type - should be stored at sign_addr[7:0]
#define CORE_STATUS 0x0
#define TEST_RESULT 0x1
#define WRITE_GPR 0x2
#define WRITE_CSR 0x3

// core status - should be stored at sign_addr[12:8]
#define INITIALIZED 0x0
#define IN_DEBUG_MODE 0x1
#define IN_MACHINE_MODE 0x2
#define IN_HYPERVISOR_MODE 0x3
#define IN_SUPERVISOR_MODE 0x4
#define IN_USER_MODE 0x5
#define HANDLING_IRQ 0x6
#define FINISHED_IRQ 0x7
#define HANDLING_EXCEPTION 0x8
#define INSTR_FAULT_EXCEPTION 0x9
#define ILLEGAL_INSTR_EXCEPTION 0xa
#define LOAD_FAULT_EXCEPTION 0xb
#define STORE_FAULT_EXCEPTION 0xc
#define EBREAK_EXCEPTION 0xd

// test result - should be stored at sign_addr[8]
#define TEST_PASS 0x0
#define TEST_FAIL 0x1

#define CSR_MSECCFG 0x747
#define MSECCFG_MML 0x1
#define MSECCFG_MMWP 0x2
#define MSECCFG_RLB 0x4
