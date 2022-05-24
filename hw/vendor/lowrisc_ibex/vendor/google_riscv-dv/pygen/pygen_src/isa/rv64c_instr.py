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

from pygen_src.riscv_defines import DEFINE_C_INSTR
from pygen_src.riscv_instr_pkg import (riscv_instr_name_t, riscv_instr_format_t,
                                       riscv_instr_category_t, riscv_instr_group_t)


DEFINE_C_INSTR(riscv_instr_name_t.C_ADDIW, riscv_instr_format_t.CI_FORMAT,
               riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV64C, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_SUBW, riscv_instr_format_t.CA_FORMAT,
               riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV64C, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_ADDW, riscv_instr_format_t.CA_FORMAT,
               riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV64C, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_LD, riscv_instr_format_t.CL_FORMAT,
               riscv_instr_category_t.LOAD, riscv_instr_group_t.RV64C, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_SD, riscv_instr_format_t.CS_FORMAT,
               riscv_instr_category_t.STORE, riscv_instr_group_t.RV64C, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_LDSP, riscv_instr_format_t.CI_FORMAT,
               riscv_instr_category_t.LOAD, riscv_instr_group_t.RV64C, g=globals())
DEFINE_C_INSTR(riscv_instr_name_t.C_SDSP, riscv_instr_format_t.CSS_FORMAT,
               riscv_instr_category_t.STORE, riscv_instr_group_t.RV64C, g=globals())
