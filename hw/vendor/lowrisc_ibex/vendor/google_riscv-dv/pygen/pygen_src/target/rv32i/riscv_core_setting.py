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
from pygen_src.riscv_instr_pkg import (privileged_reg_t, satp_mode_t,
                                       riscv_instr_group_t, privileged_mode_t)


XLEN = 32

implemented_csr = [privileged_reg_t.MVENDORID, privileged_reg_t.MARCHID, privileged_reg_t.MIMPID,
                   privileged_reg_t.MHARTID, privileged_reg_t.MSTATUS,
                   privileged_reg_t.MISA, privileged_reg_t.MIE,
                   privileged_reg_t.MTVEC, privileged_reg_t.MCOUNTEREN, privileged_reg_t.MSCRATCH,
                   privileged_reg_t.MEPC, privileged_reg_t.MCAUSE,
                   privileged_reg_t.MTVAL, privileged_reg_t.MIP]

SATP_MODE = satp_mode_t.BARE

supported_isa = [riscv_instr_group_t.RV32I]

supported_privileged_mode = [privileged_mode_t.MACHINE_MODE]
NUM_HARTS = 1

support_pmp = 0

support_debug_mode = 0

unsupported_instr = []

support_umode_trap = 0

# GPR Setting
NUM_FLOAT_GPR = 32
NUM_GPR = 32
NUM_VEC_GPR = 32

max_interrupt_vector_num = 16
