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

supported_isa = ['RV32I']

supported_privileged_mode = ['MACHINE_MODE']

NUM_HARTS = 1

support_pmp = 0

unsupported_instr = []

support_umode_trap = 0

# GPR Setting
NUM_FLOAT_GPR = 32
NUM_GPR = 32
NUM_VEC_GPR = 32
