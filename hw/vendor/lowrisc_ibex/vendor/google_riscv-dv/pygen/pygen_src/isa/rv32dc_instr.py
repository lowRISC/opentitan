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

from pygen_src.riscv_defines import DEFINE_FC_INSTR
from pygen_src.riscv_instr_pkg import (riscv_instr_name_t, riscv_instr_format_t,
                                       riscv_instr_category_t, riscv_instr_group_t, imm_t)


DEFINE_FC_INSTR(riscv_instr_name_t.C_FLD, riscv_instr_format_t.CL_FORMAT,
                riscv_instr_category_t.LOAD, riscv_instr_group_t.RV32DC, imm_t.UIMM, g=globals())
DEFINE_FC_INSTR(riscv_instr_name_t.C_FSD, riscv_instr_format_t.CS_FORMAT,
                riscv_instr_category_t.STORE, riscv_instr_group_t.RV32DC, imm_t.UIMM, g=globals())
DEFINE_FC_INSTR(riscv_instr_name_t.C_FLDSP, riscv_instr_format_t.CI_FORMAT,
                riscv_instr_category_t.LOAD, riscv_instr_group_t.RV32DC, imm_t.UIMM, g=globals())
DEFINE_FC_INSTR(riscv_instr_name_t.C_FSDSP, riscv_instr_format_t.CSS_FORMAT,
                riscv_instr_category_t.STORE, riscv_instr_group_t.RV32DC, imm_t.UIMM, g=globals())
