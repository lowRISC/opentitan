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

from pygen_src.riscv_defines import DEFINE_FP_INSTR
from pygen_src.riscv_instr_pkg import (riscv_instr_name_t, riscv_instr_format_t,
                                       riscv_instr_category_t, riscv_instr_group_t)


DEFINE_FP_INSTR(riscv_instr_name_t.FLW, riscv_instr_format_t.I_FORMAT,
                riscv_instr_category_t.LOAD, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FSW, riscv_instr_format_t.S_FORMAT,
                riscv_instr_category_t.STORE, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FMADD_S, riscv_instr_format_t.R4_FORMAT,
                riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FMSUB_S, riscv_instr_format_t.R4_FORMAT,
                riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FNMSUB_S, riscv_instr_format_t.R4_FORMAT,
                riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FNMADD_S, riscv_instr_format_t.R4_FORMAT,
                riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FADD_S, riscv_instr_format_t.R_FORMAT,
                riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FSUB_S, riscv_instr_format_t.R_FORMAT,
                riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FMUL_S, riscv_instr_format_t.R_FORMAT,
                riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FDIV_S, riscv_instr_format_t.R_FORMAT,
                riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FSQRT_S, riscv_instr_format_t.I_FORMAT,
                riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FSGNJ_S, riscv_instr_format_t.R_FORMAT,
                riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FSGNJN_S, riscv_instr_format_t.R_FORMAT,
                riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FSGNJX_S, riscv_instr_format_t.R_FORMAT,
                riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FMIN_S, riscv_instr_format_t.R_FORMAT,
                riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FMAX_S, riscv_instr_format_t.R_FORMAT,
                riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FCVT_W_S, riscv_instr_format_t.I_FORMAT,
                riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FCVT_WU_S, riscv_instr_format_t.I_FORMAT,
                riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FMV_X_W, riscv_instr_format_t.I_FORMAT,
                riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FEQ_S, riscv_instr_format_t.R_FORMAT,
                riscv_instr_category_t.COMPARE, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FLT_S, riscv_instr_format_t.R_FORMAT,
                riscv_instr_category_t.COMPARE, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FLE_S, riscv_instr_format_t.R_FORMAT,
                riscv_instr_category_t.COMPARE, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FCLASS_S, riscv_instr_format_t.R_FORMAT,
                riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FCVT_S_W, riscv_instr_format_t.I_FORMAT,
                riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FCVT_S_WU, riscv_instr_format_t.I_FORMAT,
                riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32F, g=globals())
DEFINE_FP_INSTR(riscv_instr_name_t.FMV_W_X, riscv_instr_format_t.I_FORMAT,
                riscv_instr_category_t.ARITHMETIC, riscv_instr_group_t.RV32F, g=globals())
