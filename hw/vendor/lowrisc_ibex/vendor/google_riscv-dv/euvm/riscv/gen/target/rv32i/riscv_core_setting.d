/*
 * Copyright 2019 Google LLC
 * Copyright 2022 Coverify Systems Technology
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

module riscv.gen.target.rv32i.riscv_core_setting;

import riscv.gen.riscv_instr_pkg: satp_mode_t, privileged_mode_t,
  riscv_instr_name_t, mtvec_mode_t, interrupt_cause_t,
  exception_cause_t, riscv_instr_group_t, privileged_reg_t;
import esdl: ubvec, flog2;

enum int XLEN = 32;

// Enum for SATP mode, set to BARE if address translation is not supported
enum satp_mode_t SATP_MODE = satp_mode_t.BARE;

// Supported Privileged mode
privileged_mode_t[] supported_privileged_mode = [privileged_mode_t.MACHINE_MODE];

// Unsupported instructions
riscv_instr_name_t[] unsupported_instr = [];

// ISA supported by the processor
riscv_instr_group_t[] supported_isa = [riscv_instr_group_t.RV32I];

// Interrupt mode support
mtvec_mode_t[] supported_interrupt_mode  = [mtvec_mode_t.DIRECT, mtvec_mode_t.VECTORED];

// The number of interrupt vectors to be generated, only used if VECTORED interrupt mode is
// supported
int max_interrupt_vector_num = 16;

// Physical memory protection support
enum bool support_pmp = false;

// Debug mode support
enum bool support_debug_mode = false;

// Support delegate trap to user mode
enum bool support_umode_trap = false;

// Support sfence.vma instruction
enum bool support_sfence = false;

// Support unaligned load/store
enum bool support_unaligned_load_store = true;

// GPR setting
enum int NUM_FLOAT_GPR = 32;
enum int NUM_GPR = 32;
enum int NUM_VEC_GPR = 32;

// ----------------------------------------------------------------------------
// Vector extension configuration
// ----------------------------------------------------------------------------

// Enum for vector extension
enum int VECTOR_EXTENSION_ENABLE = 0;

enum int VLEN = 512;

// Maximum size of a single vector element
enum int ELEN = 32;

// Minimum size of a sub-element, which must be at most 8-bits.
enum int SELEN = 8;

// Maximum size of a single vector element (encoded in vsew format)
enum int VELEN = flog2(ELEN) - 3;

// Maxium LMUL supported by the core
enum int MAX_LMUL = 8;

// ----------------------------------------------------------------------------
// Multi-harts configuration
// ----------------------------------------------------------------------------

// Number of harts
enum int NUM_HARTS = 1;

// ----------------------------------------------------------------------------
// Previleged CSR implementation
// ----------------------------------------------------------------------------

// Implemented previlieged CSR list
enum privileged_reg_t[] implemented_csr = [
					   // Machine mode mode CSR
					   privileged_reg_t.MVENDORID,  // Vendor ID
					   privileged_reg_t.MARCHID,    // Architecture ID
					   privileged_reg_t.MIMPID,     // Implementation ID
					   privileged_reg_t.MHARTID,    // Hardware thread ID
					   privileged_reg_t.MSTATUS,    // Machine status
					   privileged_reg_t.MISA,       // ISA and extensions
					   privileged_reg_t.MIE,        // Machine interrupt-enable register
					   privileged_reg_t.MTVEC,      // Machine trap-handler base address
					   privileged_reg_t.MCOUNTEREN, // Machine counter enable
					   privileged_reg_t.MSCRATCH,   // Scratch register for machine trap handlers
					   privileged_reg_t.MEPC,       // Machine exception program counter
					   privileged_reg_t.MCAUSE,     // Machine trap cause
					   privileged_reg_t.MTVAL,      // Machine bad address or instruction
					   privileged_reg_t.MIP         // Machine interrupt pending
					   ];

// Implementation-specific custom CSRs
ubvec!12[] custom_csr= [];

// ----------------------------------------------------------------------------
// Supported interrupt/exception setting, used for functional coverage
// ----------------------------------------------------------------------------

enum interrupt_cause_t[] implemented_interrupt = [ interrupt_cause_t.M_SOFTWARE_INTR,
						   interrupt_cause_t.M_TIMER_INTR,
						   interrupt_cause_t.M_EXTERNAL_INTR
						   ];

enum exception_cause_t[] implemented_exception = [

						  exception_cause_t.INSTRUCTION_ACCESS_FAULT,
						  exception_cause_t.ILLEGAL_INSTRUCTION,
						  exception_cause_t.BREAKPOINT,
						  exception_cause_t.LOAD_ADDRESS_MISALIGNED,
						  exception_cause_t.LOAD_ACCESS_FAULT,
						  exception_cause_t.ECALL_MMODE
						  ];
