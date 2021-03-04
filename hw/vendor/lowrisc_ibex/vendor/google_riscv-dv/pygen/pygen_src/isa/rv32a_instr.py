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

from pygen_src.riscv_defines import DEFINE_AMO_INSTR
from pygen_src.riscv_instr_pkg import (riscv_instr_name_t, riscv_instr_format_t,
                                       riscv_instr_category_t, riscv_instr_group_t)


DEFINE_AMO_INSTR(riscv_instr_name_t.LR_W, riscv_instr_format_t.R_FORMAT,
                 riscv_instr_category_t.LOAD, riscv_instr_group_t.RV32A, g=globals())
DEFINE_AMO_INSTR(riscv_instr_name_t.SC_W, riscv_instr_format_t.R_FORMAT,
                 riscv_instr_category_t.STORE, riscv_instr_group_t.RV32A, g=globals())
DEFINE_AMO_INSTR(riscv_instr_name_t.AMOSWAP_W, riscv_instr_format_t.R_FORMAT,
                 riscv_instr_category_t.AMO, riscv_instr_group_t.RV32A, g=globals())
DEFINE_AMO_INSTR(riscv_instr_name_t.AMOADD_W, riscv_instr_format_t.R_FORMAT,
                 riscv_instr_category_t.AMO, riscv_instr_group_t.RV32A, g=globals())
DEFINE_AMO_INSTR(riscv_instr_name_t.AMOAND_W, riscv_instr_format_t.R_FORMAT,
                 riscv_instr_category_t.AMO, riscv_instr_group_t.RV32A, g=globals())
DEFINE_AMO_INSTR(riscv_instr_name_t.AMOOR_W, riscv_instr_format_t.R_FORMAT,
                 riscv_instr_category_t.AMO, riscv_instr_group_t.RV32A, g=globals())
DEFINE_AMO_INSTR(riscv_instr_name_t.AMOXOR_W, riscv_instr_format_t.R_FORMAT,
                 riscv_instr_category_t.AMO, riscv_instr_group_t.RV32A, g=globals())
DEFINE_AMO_INSTR(riscv_instr_name_t.AMOMIN_W, riscv_instr_format_t.R_FORMAT,
                 riscv_instr_category_t.AMO, riscv_instr_group_t.RV32A, g=globals())
DEFINE_AMO_INSTR(riscv_instr_name_t.AMOMAX_W, riscv_instr_format_t.R_FORMAT,
                 riscv_instr_category_t.AMO, riscv_instr_group_t.RV32A, g=globals())
DEFINE_AMO_INSTR(riscv_instr_name_t.AMOMINU_W, riscv_instr_format_t.R_FORMAT,
                 riscv_instr_category_t.AMO, riscv_instr_group_t.RV32A, g=globals())
DEFINE_AMO_INSTR(riscv_instr_name_t.AMOMAXU_W, riscv_instr_format_t.R_FORMAT,
                 riscv_instr_category_t.AMO, riscv_instr_group_t.RV32A, g=globals())
