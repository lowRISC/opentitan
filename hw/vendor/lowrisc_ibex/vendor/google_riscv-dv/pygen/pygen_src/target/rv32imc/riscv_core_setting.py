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

XLEN = 32

implemented_csr = ['MVENDORID', 'MARCHID', 'MIMPID', 'MHARTID', 'MSTATUS', 'MISA', 'MIE',
                   'MTVEC', 'MCOUNTEREN', 'MSCRATCH', 'MEPC', 'MCAUSE', 'MTVAL', 'MIP']

SATP_MODE = 'BARE'

supported_isa = ['RV32I', 'RV32M', 'RV32C']

supported_privileged_mode = ['MACHINE_MODE']

supported_interrupt_mode = ['DIRECT', 'VECTORED']

max_interrupt_vector_num = 16

support_debug_mode = 0

NUM_HARTS = 1

support_pmp = 0

unsupported_instr = []

support_umode_trap = 0

support_sfence = 0

support_unaligned_load_store = 1

# GPR Setting
NUM_FLOAT_GPR = 32
NUM_GPR = 32
NUM_VEC_GPR = 32

VECTOR_EXTENSION_ENABLE = 0

VLEN = 512

ELEN = 32

SELEN = 0

MAX_MUL = 8

implemented_interrupt = ['M_SOFTWARE_INTR', 'M_TIMER_INTR', 'M_EXTERNAL_INTR']

implemented_exception = ['INSTRUCTION_ACCESS_FAULT', 'ILLEGAL_INSTRUCTION',
                         'BREAKPOINT', 'LOAD_ADDRESS_MISALIGNED', 'LOAD_ACCESS_FAULT',
                         'ECALL_MMODE']
