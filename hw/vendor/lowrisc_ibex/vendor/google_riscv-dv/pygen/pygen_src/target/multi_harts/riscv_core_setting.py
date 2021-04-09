"""
Copyright 2020 Google LLC
Copyright 2020 PerfectVIPs Inc.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
"""
from pygen_src.riscv_instr_pkg import (privileged_reg_t, interrupt_cause_t,
                                       exception_cause_t, satp_mode_t,
                                       riscv_instr_group_t, privileged_mode_t,
                                       mtvec_mode_t)





XLEN = 32

implemented_csr = [privileged_reg_t.MVENDORID, privileged_reg_t.MARCHID,
                   privileged_reg_t.MIMPID, privileged_reg_t.MHARTID,
                   privileged_reg_t.MSTATUS, privileged_reg_t.MISA, privileged_reg_t.MIE,
                   privileged_reg_t.MTVEC, privileged_reg_t.MCOUNTEREN, privileged_reg_t.MSCRATCH,
                   privileged_reg_t.MEPC, privileged_reg_t.MCAUSE,
                   privileged_reg_t.MTVAL, privileged_reg_t.MIP]

SATP_MODE = satp_mode_t.BARE

supported_isa = [riscv_instr_group_t.RV32I, riscv_instr_group_t.RV32M,
                 riscv_instr_group_t.RV32C, riscv_instr_group_t.RV32A]

supported_privileged_mode = [privileged_mode_t.MACHINE_MODE]

supported_interrupt_mode = [mtvec_mode_t.DIRECT, mtvec_mode_t.VECTORED]

max_interrupt_vector_num = 16

support_debug_mode = 0

NUM_HARTS = 2

support_pmp = 0

unsupported_instr = []

support_umode_trap = 0

support_sfence = 0

support_unaligned_load_store = 1

NUM_FLOAT_GPR = 32

NUM_GPR = 32

NUM_VEC_GPR = 32

VECTOR_EXTENSION_ENABLE = 0

VLEN = 512

ELEN = 32

SELEN = 8

#VELEN = 

MAX_MUL = 8

implemented_interrupt = [interrupt_cause_t.M_SOFTWARE_INTR,
                         interrupt_cause_t.M_TIMER_INTR,
                         interrupt_cause_t.M_EXTERNAL_INTR]

implemented_exception = [exception_cause_t.INSTRUCTION_ACCESS_FAULT,
                         exception_cause_t.ILLEGAL_INSTRUCTION,
                         exception_cause_t.BREAKPOINT,
                         exception_cause_t.LOAD_ADDRESS_MISALIGNED,
                         exception_cause_t.LOAD_ACCESS_FAULT,
                         exception_cause_t.ECALL_MMODE]
