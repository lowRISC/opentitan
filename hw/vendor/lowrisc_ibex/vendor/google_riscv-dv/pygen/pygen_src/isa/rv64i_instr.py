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

from pygen_src.riscv_defines import DEFINE_INSTR
from pygen_src.riscv_instr_pkg import (riscv_instr_name_t, riscv_instr_format_t,
                                       riscv_instr_category_t, riscv_instr_group_t)


DEFINE_INSTR(riscv_instr_name_t.LWU, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.LOAD, riscv_instr_group_t.RV64I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.LD, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.LOAD, riscv_instr_group_t.RV64I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.SD, riscv_instr_format_t.S_FORMAT,
             riscv_instr_category_t.STORE, riscv_instr_group_t.RV64I, g=globals())
# SHIFT intructions
DEFINE_INSTR(riscv_instr_name_t.SLLW, riscv_instr_format_t.R_FORMAT,
             riscv_instr_category_t.SHIFT, riscv_instr_group_t.RV64I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.SLLIW, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.SHIFT, riscv_instr_group_t.RV64I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.SRLW, riscv_instr_format_t.R_FORMAT,
             riscv_instr_category_t.SHIFT, riscv_instr_group_t.RV64I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.SRLIW, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.SHIFT, riscv_instr_group_t.RV64I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.SRAW, riscv_instr_format_t.R_FORMAT,
             riscv_instr_category_t.SHIFT, riscv_instr_group_t.RV64I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.SRAIW, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.SHIFT, riscv_instr_group_t.RV64I, g=globals())
# ARITHMETIC intructions
DEFINE_INSTR(riscv_instr_name_t.ADDW, riscv_instr_format_t.R_FORMAT,
             riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV64I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.ADDIW, riscv_instr_format_t.I_FORMAT,
             riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV64I, g=globals())
DEFINE_INSTR(riscv_instr_name_t.SUBW, riscv_instr_format_t.R_FORMAT,
             riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV64I, g=globals())
