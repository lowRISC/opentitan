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
parameter int XLEN = 64;

// Parameter for SATP mode, set to BARE if address translation is not supported
parameter satp_mode_t SATP_MODE = SV39;

// Supported Privileged mode
privileged_mode_t supported_privileged_mode[] = {USER_MODE, SUPERVISOR_MODE, MACHINE_MODE};

// Unsupported instructions
riscv_instr_name_t unsupported_instr[];

// ISA supported by the processor
riscv_instr_group_t supported_isa[$] = {RV32I, RV32M, RV64I, RV64M, RV32C, RV64C, RV32A, RV64A,
                                        RV32F, RV64F, RV32D, RV64D};

// Interrupt mode support
mtvec_mode_t supported_interrupt_mode[$] = {DIRECT, VECTORED};

// The number of interrupt vectors to be generated, only used if VECTORED interrupt mode is
// supported
int max_interrupt_vector_num = 16;

// Debug mode support
bit support_debug_mode = 0;

// Support delegate trap to user mode
bit support_umode_trap = 0;

// Support sfence.vma instruction
bit support_sfence = 1;

// ----------------------------------------------------------------------------
// Previleged CSR implementation
// ----------------------------------------------------------------------------

// Implemented previlieged CSR list
`ifdef DSIM
privileged_reg_t implemented_csr[] = {
`else
parameter privileged_reg_t implemented_csr[] = {
`endif
    // User mode CSR
    USTATUS,    // User status
    UIE,        // User interrupt-enable register
    UTVEC,      // User trap-handler base address
    USCRATCH,   // Scratch register for user trap handlers
    UEPC,       // User exception program counter
    UCAUSE,     // User trap cause
    UTVAL,      // User bad address or instruction
    UIP,        // User interrupt pending
    // Supervisor mode CSR
    SSTATUS,    // Supervisor status
    SEDELEG,    // Supervisor exception delegation register
    SIDELEG,    // Supervisor interrupt delegation register
    SIE,        // Supervisor interrupt-enable register
    STVEC,      // Supervisor trap-handler base address
    SCOUNTEREN, // Supervisor counter enable
    SSCRATCH,   // Scratch register for supervisor trap handlers
    SEPC,       // Supervisor exception program counter
    SCAUSE,     // Supervisor trap cause
    STVAL,      // Supervisor bad address or instruction
    SIP,        // Supervisor interrupt pending
    SATP,       // Supervisor address translation and protection
    // Machine mode mode CSR
    MVENDORID,  // Vendor ID
    MARCHID,    // Architecture ID
    MIMPID,     // Implementation ID
    MHARTID,    // Hardware thread ID
    MSTATUS,    // Machine status
    MISA,       // ISA and extensions
    MEDELEG,    // Machine exception delegation register
    MIDELEG,    // Machine interrupt delegation register
    MIE,        // Machine interrupt-enable register
    MTVEC,      // Machine trap-handler base address
    MCOUNTEREN, // Machine counter enable
    MSCRATCH,   // Scratch register for machine trap handlers
    MEPC,       // Machine exception program counter
    MCAUSE,     // Machine trap cause
    MTVAL,      // Machine bad address or instruction
    MIP,        // Machine interrupt pending
    // Floating point CSR
    FCSR        // Floating point control and status
};

// ----------------------------------------------------------------------------
// Supported interrupt/exception setting, used for functional coverage
// ----------------------------------------------------------------------------

`ifdef DSIM
interrupt_cause_t implemented_interrupt[] = {
`else
parameter interrupt_cause_t implemented_interrupt[] = {
`endif
    U_SOFTWARE_INTR,
    S_SOFTWARE_INTR,
    M_SOFTWARE_INTR,
    U_TIMER_INTR,
    S_TIMER_INTR,
    M_TIMER_INTR,
    U_EXTERNAL_INTR,
    S_EXTERNAL_INTR,
    M_EXTERNAL_INTR
};

`ifdef DSIM
exception_cause_t implemented_exception[] = {
`else
parameter exception_cause_t implemented_exception[] = {
`endif
    INSTRUCTION_ADDRESS_MISALIGNED,
    INSTRUCTION_ACCESS_FAULT,
    ILLEGAL_INSTRUCTION,
    BREAKPOINT,
    LOAD_ADDRESS_MISALIGNED,
    LOAD_ACCESS_FAULT,
    STORE_AMO_ADDRESS_MISALIGNED,
    STORE_AMO_ACCESS_FAULT,
    ECALL_UMODE,
    ECALL_SMODE,
    ECALL_MMODE,
    INSTRUCTION_PAGE_FAULT,
    LOAD_PAGE_FAULT,
    STORE_AMO_PAGE_FAULT
};
