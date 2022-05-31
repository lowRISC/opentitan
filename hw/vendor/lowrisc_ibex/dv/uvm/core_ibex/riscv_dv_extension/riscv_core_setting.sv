/*
 * Copyright 2019 Google LLC
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

//-----------------------------------------------------------------------------
// Processor feature configuration
//-----------------------------------------------------------------------------
// XLEN
parameter int XLEN = 32;

// GPR setting
parameter int NUM_FLOAT_GPR = 0;
parameter int NUM_GPR = 32;
parameter int NUM_VEC_GPR = 0;

// Vector extension parameters - not used in Ibex
parameter int VECTOR_EXTENSION_ENABLE = 0;
parameter int VLEN = 512;
parameter int ELEN = 64;
parameter int SLEN = 64;
parameter int VELEN = 4;
parameter int SELEN = 8;
parameter int MAX_LMUL = 8;

// Number of harts
parameter int NUM_HARTS = 1;

// Parameter for SATP mode, set to BARE if address translation is not supported
parameter satp_mode_t SATP_MODE = BARE;

// Supported Privileged mode
privileged_mode_t supported_privileged_mode[] = {MACHINE_MODE, USER_MODE};

// Unsupported instructions
// Avoid generating these instructions in regular regression
// FENCE.I is intentionally treated as illegal instruction by ibex core
riscv_instr_name_t unsupported_instr[] = {FENCE_I};

// Specify whether processor supports unaligned loads and stores
bit support_unaligned_load_store = 1'b1;

// ISA supported by the processor
riscv_instr_group_t supported_isa[$] = {RV32I, RV32M, RV32C,
    RV32ZBA, RV32ZBB, RV32ZBC, RV32ZBS, RV32B};

// Interrupt mode support
mtvec_mode_t supported_interrupt_mode[$] = {VECTORED};

// The number of interrupt vectors to be generated, only used if VECTORED interrupt mode is
// supported
int max_interrupt_vector_num = 32;

// Physical memory protection support
bit support_pmp = 1;

// Debug mode support
bit support_debug_mode = 1;

// Support delegate trap to user mode
bit support_umode_trap = 0;

// Support sfence.vma instruction
bit support_sfence = 0;

//-----------------------------------------------------------------------------
// Kernel section setting, used by supervisor mode programs
//-----------------------------------------------------------------------------

// Number of kernel data pages
int num_of_kernel_data_pages = 0;

// Byte size of kernel data pages
int kernel_data_page_size = 4096;

// Kernel Stack section word length
int kernel_stack_len = 5000;

// Number of instructions for each kernel program
int kernel_program_instr_cnt = 400;

// ----------------------------------------------------------------------------
// Previleged CSR implementation
// ----------------------------------------------------------------------------

// Implemented previlieged CSR list
const privileged_reg_t implemented_csr[] = {
    // Machine mode mode CSR
    MVENDORID,        // Vendor ID
    MARCHID,          // Architecture ID
    MHARTID,          // Hardware thread ID
    MSTATUS,          // Machine status
    MISA,             // ISA and extensions
    MTVEC,            // Machine trap-handler base address
    MEPC,             // Machine exception program counter
    MCAUSE,           // Machine trap cause
    MTVAL,            // Machine bad address or instruction
    MIE,              // Machine interrupt enable
    MIP,              // Machine interrupt pending
    MCYCLE,           // Machine cycle counter (lower 32 bits)
    MCYCLEH,          // Machine cycle counter (upper 32 bits)
    MINSTRET,         // Machine instructions retired counter (lower 32 bits)
    MINSTRETH,        // Machine instructions retired counter (upper 32 bits)
    MCOUNTINHIBIT,    // Machine counter inhibit register
    MHPMEVENT3,       // Machine performance monitoring event selector
    MHPMEVENT4,       // Machine performance monitoring event selector
    MHPMEVENT5,       // Machine performance monitoring event selector
    MHPMEVENT6,       // Machine performance monitoring event selector
    MHPMEVENT7,       // Machine performance monitoring event selector
    MHPMEVENT8,       // Machine performance monitoring event selector
    MHPMEVENT9,       // Machine performance monitoring event selector
    MHPMEVENT10,      // Machine performance monitoring event selector
    MHPMCOUNTER3,     // Machine performance monitoring counter (lower 32 bits)
    MHPMCOUNTER4,     // Machine performance monitoring counter (lower 32 bits)
    MHPMCOUNTER5,     // Machine performance monitoring counter (lower 32 bits)
    MHPMCOUNTER6,     // Machine performance monitoring counter (lower 32 bits)
    MHPMCOUNTER7,     // Machine performance monitoring counter (lower 32 bits)
    MHPMCOUNTER8,     // Machine performance monitoring counter (lower 32 bits)
    MHPMCOUNTER9,     // Machine performance monitoring counter (lower 32 bits)
    MHPMCOUNTER10,    // Machine performance monitoring counter (lower 32 bits)
    MHPMCOUNTER3H,    // Machine performance monitoring counter (upper 32 bits)
    MHPMCOUNTER4H,    // Machine performance monitoring counter (upper 32 bits)
    MHPMCOUNTER5H,    // Machine performance monitoring counter (upper 32 bits)
    MHPMCOUNTER6H,    // Machine performance monitoring counter (upper 32 bits)
    MHPMCOUNTER7H,    // Machine performance monitoring counter (upper 32 bits)
    MHPMCOUNTER8H,    // Machine performance monitoring counter (upper 32 bits)
    MHPMCOUNTER9H,    // Machine performance monitoring counter (upper 32 bits)
    MHPMCOUNTER10H,   // Machine performance monitoring counter (upper 32 bits)
    PMPCFG0,          // PMP configuration register
    PMPCFG1,          // PMP configuration register
    PMPCFG2,          // PMP configuration register
    PMPCFG3,          // PMP configuration register
    PMPADDR0,         // PMP address register
    PMPADDR1,         // PMP address register
    PMPADDR2,         // PMP address register
    PMPADDR3,         // PMP address register
    PMPADDR4,         // PMP address register
    PMPADDR5,         // PMP address register
    PMPADDR6,         // PMP address register
    PMPADDR7,         // PMP address register
    PMPADDR8,         // PMP address register
    PMPADDR9,         // PMP address register
    PMPADDR10,        // PMP address register
    PMPADDR11,        // PMP address register
    PMPADDR12,        // PMP address register
    PMPADDR13,        // PMP address register
    PMPADDR14,        // PMP address register
    PMPADDR15,        // PMP address register
    DCSR,             // Debug control and status register
    DPC,              // Debug PC
    DSCRATCH0,        // Debug scratch register 0
    DSCRATCH1,        // Debug scratch register 1
    TSELECT,          // Trigger select register
    TDATA1,           // Trigger data register 1
    TDATA2,           // Trigger data register 2
    TDATA3,           // Trigger data register 3
    MCONTEXT,         // Machine context register
    SCONTEXT          // Supervisor context register
};

// Implementation-specific custom CSRs
const bit [11:0] custom_csr[] = {
  12'h7C0,    // cpuctrl    - CPU control register
  12'h7C1     // secureseed - Security feature random seed register
};

// --------------------------------------------------------------------------
// Supported interrupt/exception setting, used for functional coverage
// --------------------------------------------------------------------------
const interrupt_cause_t implemented_interrupt[] = {
  M_SOFTWARE_INTR,
  M_TIMER_INTR,
  M_EXTERNAL_INTR
};
const exception_cause_t implemented_exception[] = {
  INSTRUCTION_ACCESS_FAULT,
  ILLEGAL_INSTRUCTION,
  BREAKPOINT,
  LOAD_ACCESS_FAULT,
  STORE_AMO_ACCESS_FAULT,
  ECALL_MMODE
};
