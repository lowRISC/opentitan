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
riscv_instr_group_t supported_isa[$] = {RV32I, RV32M, RV64I, RV64M, RV32C, RV64C, RV32A, RV64A};

// Interrupt mode support
mtvec_mode_t supported_interrupt_mode[$] = {DIRECT, VECTORED};

// Debug mode support
bit support_debug_mode = 0;

// Support delegate trap to user mode
bit support_umode_trap = 0;

// Support sfence.vma instruction
bit support_sfence = 1;

// Cache line size (in bytes)
// If processor does not support caches, set to XLEN/8
int dcache_line_size_in_bytes = 128;

// Number of data section
// For processor that doesn't have data TLB, this can be set to 1
// For processor that supports data TLB, this should be set to be larger than the number
// of entries of dTLB to cover dTLB hit/miss scenario
int num_of_data_pages = 40;

// Data section byte size
// For processor with no dTLB and data cache, keep the value below 10K
// For processor with dTLB support, set it to the physical memory size that covers one entry
// of the dTLB
int data_page_size = 4096;
int data_page_alignment = $clog2(data_page_size);

// The maximum data section byte size actually used by load/store instruction
// Set to this value to be smaller than data_page_size. If there's data cache in the system,
// this value should be set large enough to be able to hit cache hit/miss scenario within a data
// section. Don't set this to too big as it will introduce a very large binary.
int max_used_data_page_size = 512;

// Stack section word length
int stack_len = 5000;

//-----------------------------------------------------------------------------
// Kernel section setting, used by supervisor mode programs
//-----------------------------------------------------------------------------

// Number of kernel data pages
int num_of_kernel_data_pages = 5;

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
privileged_reg_t implemented_csr[$] = {
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
    MIP         // Machine interrupt pending
};
