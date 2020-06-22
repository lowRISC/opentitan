/*
 * Copyright 2019 Google LLC
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

`ifndef COMPLIANCE_MODE
  `define DV(TEXT) TEXT
`else
  `define DV(TEXT)
`endif

`define SAMPLE(cg, val) \
  if (cg != null) cg.sample(val);

// sample with type cast
`define SAMPLE_W_TYPE(cg, val, typ = riscv_instr) \
  if (cg != null) begin \
    typ t; \
    `DV_CHECK_FATAL($cast(t, val), $sformatf("Cannot cast %0s to %0s", `"val`", `"typ`"), \
                    "riscv_instr_cover_group") \
    cg.sample(t); \
  end

`define SAMPLE_F(cg, val) `SAMPLE_W_TYPE(cg, val, riscv_floating_point_instr)
`define SAMPLE_B(cg, val) `SAMPLE_W_TYPE(cg, val, riscv_b_instr)

`define INSTR_CG_BEGIN(INSTR_NAME, INSTR_CLASS = riscv_instr) \
  covergroup ``INSTR_NAME``_cg with function sample(INSTR_CLASS instr);

`define R_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rs1         : coverpoint instr.rs1; \
    cp_rs2         : coverpoint instr.rs2; \
    cp_rd          : coverpoint instr.rd;  \
    cp_rs1_sign    : coverpoint instr.rs1_sign; \
    cp_rs2_sign    : coverpoint instr.rs2_sign; \
    cp_rd_sign     : coverpoint instr.rd_sign; \
    `DV(cp_gpr_hazard : coverpoint instr.gpr_hazard;) \

`define CMP_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rs1         : coverpoint instr.rs1; \
    cp_rd          : coverpoint instr.rd;  \
    cp_rs1_sign    : coverpoint instr.rs1_sign; \
    cp_result      : coverpoint instr.rd_value[0]; \
    `DV(cp_gpr_hazard : coverpoint instr.gpr_hazard;) \

`define SB_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rs1         : coverpoint instr.rs1; \
    cp_rs2         : coverpoint instr.rs2; \
    cp_rs1_sign    : coverpoint instr.rs1_sign; \
    cp_rs2_sign    : coverpoint instr.rs2_sign; \
    cp_imm_sign    : coverpoint instr.imm_sign; \
    cp_branch_hit  : coverpoint instr.branch_hit; \
    cp_sign_cross  : cross cp_rs1_sign, cp_rs2_sign; \
    `DV(cp_gpr_hazard : coverpoint instr.gpr_hazard { \
      bins valid_hazard[] = {NO_HAZARD, RAW_HAZARD}; \
    }) \

`define STORE_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rs1         : coverpoint instr.rs1 { \
        `DV(ignore_bins zero = {ZERO};) \
    } \
    cp_rs2         : coverpoint instr.rs2; \
    cp_imm_sign    : coverpoint instr.imm_sign; \
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard { \
      bins valid_hazard[] = {NO_HAZARD, RAW_HAZARD}; \
    }) \
    `DV(cp_lsu_hazard  : coverpoint instr.lsu_hazard { \
      bins valid_hazard[] = {NO_HAZARD, WAR_HAZARD, WAW_HAZARD}; \
    }) \

`define LOAD_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rs1         : coverpoint instr.rs1 { \
      `DV(ignore_bins zero = {ZERO};) \
    } \
    cp_rd          : coverpoint instr.rd; \
    cp_imm_sign    : coverpoint instr.imm_sign; \
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard;) \
    `DV(cp_lsu_hazard  : coverpoint instr.lsu_hazard { \
      bins valid_hazard[] = {NO_HAZARD, RAW_HAZARD}; \
    }) \

`define I_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rs1         : coverpoint instr.rs1; \
    cp_rd          : coverpoint instr.rd; \
    cp_rs1_sign    : coverpoint instr.rs1_sign; \
    cp_rd_sign     : coverpoint instr.rd_sign; \
    cp_imm_sign    : coverpoint instr.imm_sign; \
    `DV(cp_gpr_hazard : coverpoint instr.gpr_hazard;)

`define U_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rd          : coverpoint instr.rd; \
    cp_rd_sign     : coverpoint instr.rd_sign; \
    `DV(cp_gpr_hazard : coverpoint instr.gpr_hazard;)

`define J_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_imm_sign    : coverpoint instr.imm_sign; \
    cp_rd          : coverpoint instr.rd; \
    cp_rd_align    : coverpoint instr.rd_value[1];

`define CSR_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rd          : coverpoint instr.rd; \
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard;)

`define CR_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rs2         : coverpoint instr.rs2; \
    cp_rd          : coverpoint instr.rd; \
    cp_rs2_sign    : coverpoint instr.rs2_sign; \
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard;)

`define CI_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rd       : coverpoint instr.rd; \
    cp_imm_sign : coverpoint instr.imm_sign; \
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard { \
      bins valid_hazard[] = {NO_HAZARD, WAR_HAZARD, WAW_HAZARD}; \
    })

`define CI_INSTR_NON_ZERO_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rd       : coverpoint instr.rd { \
      ignore_bins non_zero = {ZERO}; \
    } \
    cp_imm_sign : coverpoint instr.imm_sign; \
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard { \
      bins valid_hazard[] = {NO_HAZARD, WAR_HAZARD, WAW_HAZARD}; \
    })

`define CSS_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rs2      : coverpoint instr.rs2; \
    cp_imm_sign : coverpoint instr.imm_sign; \
    cp_rs2_sign : coverpoint instr.rs2_sign; \
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard { \
      bins valid_hazard[] = {NO_HAZARD, RAW_HAZARD}; \
    })

`define CIW_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rd       : coverpoint instr.rd { \
      bins gpr[] = {S0, S1, A0, A1, A2, A3, A4, A5}; \
    } \
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard { \
      bins valid_hazard[] = {NO_HAZARD, WAR_HAZARD, WAW_HAZARD}; \
    })

`define CL_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rs1      : coverpoint instr.rs1 { \
      bins gpr[] = {S0, S1, A0, A1, A2, A3, A4, A5}; \
    } \
    cp_rd       : coverpoint instr.rd { \
      bins gpr[] = {S0, S1, A0, A1, A2, A3, A4, A5}; \
    } \
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard;) \
    `DV(cp_lsu_hazard  : coverpoint instr.lsu_hazard { \
      bins valid_hazard[] = {NO_HAZARD, RAW_HAZARD}; \
    })

`define CL_SP_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rd       : coverpoint instr.rd { \
      bins gpr[] = {S0, S1, A0, A1, A2, A3, A4, A5}; \
    }

`define CS_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rs1      : coverpoint instr.rs1 { \
      bins gpr[] = {S0, S1, A0, A1, A2, A3, A4, A5}; \
    } \
    cp_rs2      : coverpoint instr.rs2 { \
      bins gpr[] = {S0, S1, A0, A1, A2, A3, A4, A5}; \
    } \
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard { \
      bins valid_hazard[] = {NO_HAZARD, RAW_HAZARD}; \
    }) \
    `DV(cp_lsu_hazard  : coverpoint instr.lsu_hazard { \
      bins valid_hazard[] = {NO_HAZARD, WAR_HAZARD, WAW_HAZARD}; \
    })

`define CS_SP_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rs2      : coverpoint instr.rs2 { \
      bins gpr[] = {S0, S1, A0, A1, A2, A3, A4, A5}; \
    }

`define CA_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rd      : coverpoint instr.rd { \
      bins gpr[] = {S0, S1, A0, A1, A2, A3, A4, A5}; \
    } \
    cp_rs2      : coverpoint instr.rs2 { \
      bins gpr[] = {S0, S1, A0, A1, A2, A3, A4, A5}; \
    } \
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard;) \


`define CB_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rs1      : coverpoint instr.rs1 { \
      bins gpr[] = {S0, S1, A0, A1, A2, A3, A4, A5}; \
    } \
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard { \
      bins valid_hazard[] = {NO_HAZARD, RAW_HAZARD}; \
    })

`define CJ_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_imm_sign : coverpoint instr.imm_sign;

// single/double precision floating point special values coverpoint
`define FP_SPECIAL_VALUES_CP(VAR, NAME, PRECISION = S) \
    cp_sfp_special_values_on_``NAME`` : coverpoint VAR[31:0] { \
      option.weight = (`"PRECISION`" == "S"); \
      type_option.weight = (`"PRECISION`" == "S"); \
      bins infinity[] = {32'h7f80_0000, 32'hff80_0000}; \
      bins largest[]  = {32'h7f7f_ffff, 32'hff7f_ffff}; \
      bins zeros[]    = {32'h0000_0000, 32'h8000_0000}; \
      bins NaN[]      = {32'h7f80_0001, 32'h7fc0_0000}; \
    } \
    cp_sfp_subnormal_on_``NAME`` : coverpoint VAR[30:SINGLE_PRECISION_FRACTION_BITS] == 0 { \
      option.weight = (`"PRECISION`" == "S"); \
      type_option.weight = (`"PRECISION`" == "S"); \
    } \
    cp_dfp_special_values_on_``NAME`` : coverpoint VAR { \
      option.weight = (`"PRECISION`" == "D"); \
      type_option.weight = (`"PRECISION`" == "D"); \
      bins infinity[] = {64'h7ff0_0000_0000_0000, 64'hfff0_0000_0000_0000}; \
      bins largest[]  = {64'h7fef_ffff_ffff_ffff, 64'hffef_ffff_ffff_ffff}; \
      bins zeros[]    = {64'h0000_0000_0000_0000, 64'h8000_0000_0000_0000}; \
      bins NaN[]      = {64'h7ff0_0000_0000_0001, 64'h7ff8_0000_0000_0000}; \
    } \
    cp_dfp_subnormal_on_``NAME`` : coverpoint VAR[62:DOUBLE_PRECISION_FRACTION_BITS-1] == 0 { \
      option.weight = (`"PRECISION`" == "D"); \
      type_option.weight = (`"PRECISION`" == "D"); \
    }

`define FP_LOAD_INSTR_CG_BEGIN(INSTR_NAME, PRECISION = S) \
  `INSTR_CG_BEGIN(INSTR_NAME, riscv_floating_point_instr) \
    cp_rs1         : coverpoint instr.rs1 { \
      `DV(ignore_bins zero = {ZERO};) \
    } \
    cp_fd          : coverpoint instr.fd; \
    cp_imm_sign    : coverpoint instr.imm_sign; \
    `FP_SPECIAL_VALUES_CP(instr.fd_value, fd_value, PRECISION) \
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard;) \
    `DV(cp_lsu_hazard  : coverpoint instr.lsu_hazard { \
      bins valid_hazard[] = {NO_HAZARD, RAW_HAZARD}; \
    })

`define FP_STORE_INSTR_CG_BEGIN(INSTR_NAME, PRECISION = S) \
  `INSTR_CG_BEGIN(INSTR_NAME, riscv_floating_point_instr) \
    cp_rs1         : coverpoint instr.rs1 { \
        `DV(ignore_bins zero = {ZERO};) \
    } \
    cp_fs2         : coverpoint instr.fs2; \
    cp_imm_sign    : coverpoint instr.imm_sign; \
    `FP_SPECIAL_VALUES_CP(instr.fs2_value, fs2_value, PRECISION) \
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard { \
      bins valid_hazard[] = {NO_HAZARD, RAW_HAZARD}; \
    }) \
    `DV(cp_lsu_hazard  : coverpoint instr.lsu_hazard { \
      bins valid_hazard[] = {NO_HAZARD, WAR_HAZARD, WAW_HAZARD}; \
    })

`define FP_R_INSTR_CG_BEGIN(INSTR_NAME, PRECISION = S) \
  `INSTR_CG_BEGIN(INSTR_NAME, riscv_floating_point_instr) \
    cp_fs1         : coverpoint instr.fs1; \
    cp_fs2         : coverpoint instr.fs2; \
    cp_fd          : coverpoint instr.fd;  \
    cp_fs1_sign    : coverpoint instr.fs1_sign; \
    cp_fs2_sign    : coverpoint instr.fs2_sign; \
    cp_fd_sign     : coverpoint instr.fd_sign; \
    `FP_SPECIAL_VALUES_CP(instr.fs1_value, fs1_value, PRECISION) \
    `FP_SPECIAL_VALUES_CP(instr.fs2_value, fs2_value, PRECISION) \
    `FP_SPECIAL_VALUES_CP(instr.fd_value, fd_value, PRECISION) \
    `DV(cp_gpr_hazard : coverpoint instr.gpr_hazard;) \

`define FP_R4_INSTR_CG_BEGIN(INSTR_NAME, PRECISION = S) \
  `INSTR_CG_BEGIN(INSTR_NAME, riscv_floating_point_instr) \
    cp_fs1         : coverpoint instr.fs1; \
    cp_fs2         : coverpoint instr.fs2; \
    cp_fs3         : coverpoint instr.fs3; \
    cp_fd          : coverpoint instr.fd;  \
    cp_fs1_sign    : coverpoint instr.fs1_sign; \
    cp_fs2_sign    : coverpoint instr.fs2_sign; \
    cp_fs3_sign    : coverpoint instr.fs3_sign; \
    cp_fd_sign     : coverpoint instr.fd_sign; \
    cp_sign_cross: cross cp_fs1_sign, cp_fs2_sign, cp_fs3_sign, cp_fd_sign; \
    `FP_SPECIAL_VALUES_CP(instr.fs1_value, fs1_value, PRECISION) \
    `FP_SPECIAL_VALUES_CP(instr.fs2_value, fs2_value, PRECISION) \
    `FP_SPECIAL_VALUES_CP(instr.fs3_value, fs3_value, PRECISION) \
    `FP_SPECIAL_VALUES_CP(instr.fd_value, fd_value, PRECISION) \
    `DV(cp_gpr_hazard : coverpoint instr.gpr_hazard;) \

`define FSQRT_INSTR_CG_BEGIN(INSTR_NAME, PRECISION = S) \
  `INSTR_CG_BEGIN(INSTR_NAME, riscv_floating_point_instr) \
    cp_fs1         : coverpoint instr.fs1; \
    cp_fd          : coverpoint instr.fd;  \
    cp_fs1_sign    : coverpoint instr.fs1_sign; \
    cp_fd_sign     : coverpoint instr.fd_sign; \
    `FP_SPECIAL_VALUES_CP(instr.fs1_value, fs1_value, PRECISION) \
    `FP_SPECIAL_VALUES_CP(instr.fd_value, fd_value, PRECISION) \
    `DV(cp_gpr_hazard : coverpoint instr.gpr_hazard;) \

// FCVT integer to floating
`define FP_I2F_INSTR_CG_BEGIN(INSTR_NAME, PRECISION = S, SIGN_TYP = SIGN) \
  `INSTR_CG_BEGIN(INSTR_NAME, riscv_floating_point_instr) \
    cp_rs1         : coverpoint instr.rs1; \
    cp_fd          : coverpoint instr.fd; \
    cp_rs1_sign    : coverpoint instr.rs1_sign { \
      option.weight = (`"SIGN_TYP`" == "SIGN"); \
      type_option.weight = (`"SIGN_TYP`" == "SIGN"); \
    } \
    cp_fd_sign     : coverpoint instr.fd_sign { \
      option.weight = (`"SIGN_TYP`" == "SIGN"); \
      type_option.weight = (`"SIGN_TYP`" == "SIGN"); \
    } \
    `DV(cp_gpr_hazard : coverpoint instr.gpr_hazard;) \

// FCVT floating to integer
`define FP_F2I_INSTR_CG_BEGIN(INSTR_NAME, PRECISION = S, SIGN_TYP = SIGN) \
  `INSTR_CG_BEGIN(INSTR_NAME, riscv_floating_point_instr) \
    cp_fs1         : coverpoint instr.fs1; \
    cp_rd          : coverpoint instr.rd;  \
    cp_fs1_sign    : coverpoint instr.fs1_sign; \
    cp_rd_sign     : coverpoint instr.rd_sign { \
      option.weight = (`"SIGN_TYP`" == "SIGN"); \
      type_option.weight = (`"SIGN_TYP`" == "SIGN"); \
    } \
    `FP_SPECIAL_VALUES_CP(instr.fs1_value, fs1_value, PRECISION) \
    `DV(cp_gpr_hazard : coverpoint instr.gpr_hazard;) \

// floating compare instructions
`define FP_CMP_INSTR_CG_BEGIN(INSTR_NAME, PRECISION = S) \
  `INSTR_CG_BEGIN(INSTR_NAME, riscv_floating_point_instr) \
    cp_fs1         : coverpoint instr.fs1; \
    cp_fs2         : coverpoint instr.fs2; \
    cp_rd          : coverpoint instr.rd;  \
    cp_fs1_sign    : coverpoint instr.fs1_sign; \
    cp_fs2_sign    : coverpoint instr.fs2_sign; \
    `CP_VALUE_RANGE(compare_result, instr.rd_value, 0, 1) \
    `FP_SPECIAL_VALUES_CP(instr.fs1_value, fs1_value, PRECISION) \
    `FP_SPECIAL_VALUES_CP(instr.fs2_value, fs2_value, PRECISION) \
    `DV(cp_gpr_hazard : coverpoint instr.gpr_hazard;) \

`define FCLASS_INSTR_CG_BEGIN(INSTR_NAME, PRECISION = S) \
  `INSTR_CG_BEGIN(INSTR_NAME, riscv_floating_point_instr) \
    cp_fs1         : coverpoint instr.fs1; \
    cp_rd          : coverpoint instr.rd;  \
    cp_fs1_sign    : coverpoint instr.fs1_sign; \
    cp_rd_value    : coverpoint instr.rd_value { \
      bins values[] = {0, 'b1, 'b10, 'b100, 'b1000, 'b1_0000, 'b10_0000, \
                       'b100_0000, 'b1000_0000, 'b1_0000_0000, 'b10_0000_0000}; \
      illegal_bins others = default; \
    } \
    `FP_SPECIAL_VALUES_CP(instr.fs1_value, fs1_value, PRECISION) \
    `DV(cp_gpr_hazard : coverpoint instr.gpr_hazard;) \

`define B_I_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME, riscv_b_instr) \
    cp_rs1         : coverpoint instr.rs1; \
    cp_rd          : coverpoint instr.rd; \
    `DV(cp_gpr_hazard : coverpoint instr.gpr_hazard;)

`define B_R_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME, riscv_b_instr) \
    cp_rs1         : coverpoint instr.rs1; \
    cp_rs2         : coverpoint instr.rs2; \
    cp_rd          : coverpoint instr.rd;  \
    `DV(cp_gpr_hazard : coverpoint instr.gpr_hazard;) \

`define B_R_INSTR_NO_RS2_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME, riscv_b_instr) \
    cp_rs1         : coverpoint instr.rs1; \
    cp_rd          : coverpoint instr.rd;  \
    `DV(cp_gpr_hazard : coverpoint instr.gpr_hazard;) \

`define B_R4_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME, riscv_b_instr) \
    cp_rs1         : coverpoint instr.rs1; \
    cp_rs2         : coverpoint instr.rs2; \
    cp_rs3         : coverpoint instr.rs3; \
    cp_rd          : coverpoint instr.rd;  \
    `DV(cp_gpr_hazard : coverpoint instr.gpr_hazard;) \

// only enable the coverpoint for a particular XLEN (32, 64, 128)
`define ENABLE_CP_BY_XLEN(XLEN_VAL) \
  option.weight = (XLEN == XLEN_VAL); \
  type_option.weight = (XLEN == XLEN_VAL); \

`define CP_VALUE_RANGE(NAME, VAL, START, END) \
  cp_``NAME``: coverpoint VAL{ \
    bins values[] = {[START:END]}; \
  }

`define CG_END endgroup

`define CG_SELECTOR_BEGIN(CG_ISA) \
    if ((CG_ISA inside {supported_isa}) && (!select_isa || (cov_isa == CG_ISA))) begin

`define CG_SELECTOR_END \
    end

class riscv_instr_cover_group;

  riscv_instr_gen_config  cfg;
  riscv_instr             pre_instr;
  riscv_instr_name_t      instr_list[$];
  int unsigned            instr_cnt;
  int unsigned            branch_instr_cnt;
  bit [4:0]               branch_hit_history; // The last 5 branch result
  exception_cause_t       ignored_exceptions[];
  exception_cause_t       exception_list[$];

  // Mode of the coverage model

  // In complicance mode, all the micro-architecture related covergroups are removed. Only the ones
  // related to RISC-V specification compliance is sampled.
  bit                     compliance_mode;

  // By default the coverage model run with instruction trace from ISS simulation. When simulating
  // with ISS, certain covergroups like debug/interrupt could not be hit as these are not simulated
  // with ISS. You can turn off this mode by adding +iss_mode=0 if you use the instruction trace
  // from RTL simulation.
  bit                     iss_mode = 1'b1;

  // Select an ISA extension to cover
  bit                     select_isa;
  riscv_instr_group_t     cov_isa;

  `VECTOR_INCLUDE("riscv_instr_cover_group_inc_cpu_declare.sv")

  ///////////// RV32I instruction functional coverage //////////////

  // Arithmetic instructions
  `R_INSTR_CG_BEGIN(add)
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign, cp_rd_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(sub)
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign, cp_rd_sign;
  `CG_END

  `INSTR_CG_BEGIN(addi)
    cp_rs1         : coverpoint instr.rs1;
    cp_rd          : coverpoint instr.rd {
      ignore_bins non_zero = {ZERO}; // treated as nop
    }
    cp_rs1_sign    : coverpoint instr.rs1_sign;
    cp_rd_sign     : coverpoint instr.rd_sign;
    cp_imm_sign    : coverpoint instr.imm_sign;
    `DV(cp_gpr_hazard : coverpoint instr.gpr_hazard;)
    cp_sign_cross: cross cp_rs1_sign, cp_imm_sign, cp_rd_sign;
  `CG_END

  `U_INSTR_CG_BEGIN(lui)
  `CG_END

  `U_INSTR_CG_BEGIN(auipc)
  `CG_END

  // Shift instructions
  `R_INSTR_CG_BEGIN(sra)
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(sll)
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(srl)
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `INSTR_CG_BEGIN(srai)
    cp_rs1         : coverpoint instr.rs1;
    cp_rd          : coverpoint instr.rd;
    cp_rs1_sign    : coverpoint instr.rs1_sign;
    cp_rd_sign     : coverpoint instr.rd_sign;
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard;)
  `CG_END

  `INSTR_CG_BEGIN(slli)
    cp_rs1         : coverpoint instr.rs1;
    cp_rd          : coverpoint instr.rd;
    cp_rs1_sign    : coverpoint instr.rs1_sign;
    cp_rd_sign     : coverpoint instr.rd_sign;
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard;)
  `CG_END

  `INSTR_CG_BEGIN(srli)
    cp_rs1         : coverpoint instr.rs1;
    cp_rd          : coverpoint instr.rd;
    cp_rs1_sign    : coverpoint instr.rs1_sign;
    cp_rd_sign     : coverpoint instr.rd_sign;
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard;)
  `CG_END

  // Logical instructions
  `R_INSTR_CG_BEGIN(xor)
    cp_logical   : coverpoint instr.logical_similarity;
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(or)
    cp_logical   : coverpoint instr.logical_similarity;
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(and)
    cp_logical   : coverpoint instr.logical_similarity;
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `I_INSTR_CG_BEGIN(xori)
    cp_logical   : coverpoint instr.logical_similarity;
    cp_sign_cross: cross cp_rs1_sign, cp_imm_sign;
  `CG_END

  `I_INSTR_CG_BEGIN(ori)
    cp_logical   : coverpoint instr.logical_similarity;
    cp_sign_cross: cross cp_rs1_sign, cp_imm_sign;
  `CG_END

  `I_INSTR_CG_BEGIN(andi)
    cp_logical   : coverpoint instr.logical_similarity;
    cp_sign_cross: cross cp_rs1_sign, cp_imm_sign;
  `CG_END

  // Compare instructions
  `CMP_INSTR_CG_BEGIN(slt)
    cp_rs2        : coverpoint instr.rs2;
    cp_rs2_sign   : coverpoint instr.rs2_sign;
    cp_sign_cross : cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `CMP_INSTR_CG_BEGIN(sltu)
    cp_rs2        : coverpoint instr.rs2;
    cp_rs2_sign   : coverpoint instr.rs2_sign;
    cp_sign_cross : cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `CMP_INSTR_CG_BEGIN(slti)
    cp_imm_sign   : coverpoint instr.imm_sign;
    cp_sign_cross : cross cp_rs1_sign, cp_imm_sign;
  `CG_END

  `CMP_INSTR_CG_BEGIN(sltiu)
    cp_imm_sign   : coverpoint instr.imm_sign;
    cp_sign_cross : cross cp_rs1_sign, cp_imm_sign;
  `CG_END

  // Branch instruction
  `SB_INSTR_CG_BEGIN(beq)
  `CG_END

  `SB_INSTR_CG_BEGIN(bne)
  `CG_END

  `SB_INSTR_CG_BEGIN(blt)
  `CG_END

  `SB_INSTR_CG_BEGIN(bge)
  `CG_END

  `SB_INSTR_CG_BEGIN(bltu)
  `CG_END

  `SB_INSTR_CG_BEGIN(bgeu)
  `CG_END

  // Load instructions
  `LOAD_INSTR_CG_BEGIN(lb)
  `CG_END

  `LOAD_INSTR_CG_BEGIN(lh)
    cp_align: coverpoint instr.unaligned_mem_access;
  `CG_END

  `LOAD_INSTR_CG_BEGIN(lw)
    cp_align: coverpoint instr.unaligned_mem_access;
  `CG_END

  `LOAD_INSTR_CG_BEGIN(lbu)
  `CG_END

  `LOAD_INSTR_CG_BEGIN(lhu)
    cp_align: coverpoint instr.unaligned_mem_access;
  `CG_END

  // Store instruction
  `STORE_INSTR_CG_BEGIN(sb)
  `CG_END

  `STORE_INSTR_CG_BEGIN(sh)
    cp_misalign: coverpoint instr.unaligned_mem_access;
  `CG_END

  `STORE_INSTR_CG_BEGIN(sw)
    cp_misalign: coverpoint instr.unaligned_mem_access;
  `CG_END

  // JUMP instruction
  `J_INSTR_CG_BEGIN(jal)
    cp_imm_align : coverpoint instr.imm[1];
  `CG_END

  `J_INSTR_CG_BEGIN(jalr)
    cp_rs1_link : coverpoint instr.rs1 {
      bins ra = {RA};
      bins t1 = {T1};
      bins non_link = default;
    }
    cp_rd_link : coverpoint instr.rd {
      bins ra = {RA};
      bins t1 = {T1};
      bins non_link = default;
    }
    cp_imm_align : coverpoint instr.imm[1:0];
    cp_rs1_align : coverpoint instr.rs1_value[1:0];
    cp_align : cross cp_imm_align, cp_rs1_align;
    cp_ras : cross cp_rs1_link, cp_rd_link;
  `CG_END

  // floating instructions
  `FP_LOAD_INSTR_CG_BEGIN(flw)
  `CG_END

  `FP_LOAD_INSTR_CG_BEGIN(fld, D)
  `CG_END

  `FP_STORE_INSTR_CG_BEGIN(fsw)
  `CG_END

  `FP_STORE_INSTR_CG_BEGIN(fsd, D)
  `CG_END

  `FP_R_INSTR_CG_BEGIN(fadd_s)
    cp_sign_cross: cross cp_fs1_sign, cp_fs2_sign, cp_fd_sign;
  `CG_END

  `FP_R_INSTR_CG_BEGIN(fadd_d, D)
    cp_sign_cross: cross cp_fs1_sign, cp_fs2_sign, cp_fd_sign;
  `CG_END

  `FP_R_INSTR_CG_BEGIN(fsub_s)
    cp_sign_cross: cross cp_fs1_sign, cp_fs2_sign, cp_fd_sign;
  `CG_END

  `FP_R_INSTR_CG_BEGIN(fsub_d, D)
    cp_sign_cross: cross cp_fs1_sign, cp_fs2_sign, cp_fd_sign;
  `CG_END

  `FP_R_INSTR_CG_BEGIN(fmul_s)
    cp_sign_cross: cross cp_fs1_sign, cp_fs2_sign;
  `CG_END

  `FP_R_INSTR_CG_BEGIN(fmul_d, D)
    cp_sign_cross: cross cp_fs1_sign, cp_fs2_sign;
  `CG_END

  `FP_R_INSTR_CG_BEGIN(fdiv_s)
    cp_sign_cross: cross cp_fs1_sign, cp_fs2_sign;
  `CG_END

  `FP_R_INSTR_CG_BEGIN(fdiv_d, D)
    cp_sign_cross: cross cp_fs1_sign, cp_fs2_sign;
  `CG_END

  `FSQRT_INSTR_CG_BEGIN(fsqrt_s)
  `CG_END

  `FSQRT_INSTR_CG_BEGIN(fsqrt_d, D)
  `CG_END

  `FP_R_INSTR_CG_BEGIN(fmin_s)
    cp_sign_cross: cross cp_fs1_sign, cp_fs2_sign;
  `CG_END

  `FP_R_INSTR_CG_BEGIN(fmin_d, D)
    cp_sign_cross: cross cp_fs1_sign, cp_fs2_sign;
  `CG_END

  `FP_R_INSTR_CG_BEGIN(fmax_s)
    cp_sign_cross: cross cp_fs1_sign, cp_fs2_sign;
  `CG_END

  `FP_R_INSTR_CG_BEGIN(fmax_d, D)
    cp_sign_cross: cross cp_fs1_sign, cp_fs2_sign;
  `CG_END

  `FP_R4_INSTR_CG_BEGIN(fmadd_s)
  `CG_END

  `FP_R4_INSTR_CG_BEGIN(fmadd_d, D)
  `CG_END

  `FP_R4_INSTR_CG_BEGIN(fnmadd_s)
  `CG_END

  `FP_R4_INSTR_CG_BEGIN(fnmadd_d, D)
  `CG_END

  `FP_R4_INSTR_CG_BEGIN(fmsub_s)
  `CG_END

  `FP_R4_INSTR_CG_BEGIN(fmsub_d, D)
  `CG_END

  `FP_R4_INSTR_CG_BEGIN(fnmsub_s)
  `CG_END

  `FP_R4_INSTR_CG_BEGIN(fnmsub_d, D)
  `CG_END

  // FCVT floating to floating
  `INSTR_CG_BEGIN(fcvt_s_d, riscv_floating_point_instr)
    cp_fs1         : coverpoint instr.fs1;
    cp_fd          : coverpoint instr.fd;
    cp_fs1_sign    : coverpoint instr.fs1_sign;
    cp_fd_sign     : coverpoint instr.fd_sign;
    `FP_SPECIAL_VALUES_CP(instr.fs1_value, fs1_value, D)
    `FP_SPECIAL_VALUES_CP(instr.fd_value, fd_value, S)
    `DV(cp_gpr_hazard : coverpoint instr.gpr_hazard;)
  `CG_END

  `INSTR_CG_BEGIN(fcvt_d_s, riscv_floating_point_instr)
    cp_fs1         : coverpoint instr.fs1;
    cp_fd          : coverpoint instr.fd;
    cp_fs1_sign    : coverpoint instr.fs1_sign;
    cp_fd_sign     : coverpoint instr.fd_sign;
    `FP_SPECIAL_VALUES_CP(instr.fs1_value, fs1_value, S)
    `FP_SPECIAL_VALUES_CP(instr.fd_value, fd_value, D)
    `DV(cp_gpr_hazard : coverpoint instr.gpr_hazard;)
  `CG_END

  `FP_F2I_INSTR_CG_BEGIN(fcvt_w_s)
  `CG_END

  `FP_F2I_INSTR_CG_BEGIN(fcvt_wu_s, , UNSIGN)
  `CG_END

  `FP_F2I_INSTR_CG_BEGIN(fcvt_l_s)
  `CG_END

  `FP_F2I_INSTR_CG_BEGIN(fcvt_lu_s, UNSIGN)
  `CG_END

  `FP_F2I_INSTR_CG_BEGIN(fcvt_l_d, D)
  `CG_END

  `FP_F2I_INSTR_CG_BEGIN(fcvt_lu_d, D, UNSIGN)
  `CG_END

  `FP_F2I_INSTR_CG_BEGIN(fcvt_w_d, D)
  `CG_END

  `FP_F2I_INSTR_CG_BEGIN(fcvt_wu_d, D, UNSIGN)
  `CG_END

  `FP_I2F_INSTR_CG_BEGIN(fcvt_s_w)
  `CG_END

  `FP_I2F_INSTR_CG_BEGIN(fcvt_s_wu, , UNSIGN)
  `CG_END

  `FP_I2F_INSTR_CG_BEGIN(fcvt_s_l)
  `CG_END

  `FP_I2F_INSTR_CG_BEGIN(fcvt_d_l, D)
  `CG_END

  `FP_I2F_INSTR_CG_BEGIN(fcvt_s_lu, , UNSIGN)
  `CG_END

  `FP_I2F_INSTR_CG_BEGIN(fcvt_d_w, D)
  `CG_END

  `FP_I2F_INSTR_CG_BEGIN(fcvt_d_lu, D, UNSIGN)
  `CG_END

  `FP_I2F_INSTR_CG_BEGIN(fcvt_d_wu, D, UNSIGN)
  `CG_END

  `FP_R_INSTR_CG_BEGIN(fsgnj_s)
  `CG_END

  `FP_R_INSTR_CG_BEGIN(fsgnj_d, D)
  `CG_END

  `FP_R_INSTR_CG_BEGIN(fsgnjn_s)
  `CG_END

  `FP_R_INSTR_CG_BEGIN(fsgnjn_d, D)
  `CG_END

  `FP_R_INSTR_CG_BEGIN(fsgnjx_s)
  `CG_END

  `FP_R_INSTR_CG_BEGIN(fsgnjx_d, D)
  `CG_END

  `FP_F2I_INSTR_CG_BEGIN(fmv_x_w)
  `CG_END

  `FP_F2I_INSTR_CG_BEGIN(fmv_x_d, D)
  `CG_END

  `FP_I2F_INSTR_CG_BEGIN(fmv_w_x)
  `CG_END

  `FP_I2F_INSTR_CG_BEGIN(fmv_d_x, D)
  `CG_END

  `FP_CMP_INSTR_CG_BEGIN(feq_s)
  `CG_END

  `FP_CMP_INSTR_CG_BEGIN(feq_d, D)
  `CG_END

  `FP_CMP_INSTR_CG_BEGIN(flt_s)
  `CG_END

  `FP_CMP_INSTR_CG_BEGIN(flt_d, D)
  `CG_END

  `FP_CMP_INSTR_CG_BEGIN(fle_s)
  `CG_END

  `FP_CMP_INSTR_CG_BEGIN(fle_d, D)
  `CG_END

  `FCLASS_INSTR_CG_BEGIN(fclass_s)
  `CG_END

  `FCLASS_INSTR_CG_BEGIN(fclass_d, D)
  `CG_END

  // B extension
  // Count Leading/Trailing Zeros (clz, ctz)
  `B_R_INSTR_NO_RS2_CG_BEGIN(clz)
    `CP_VALUE_RANGE(num_leading_zeros, instr.rd_value, 0, XLEN-1)
  `CG_END

  `B_R_INSTR_NO_RS2_CG_BEGIN(ctz)
    `CP_VALUE_RANGE(num_trailing_zeros, instr.rd_value, 0, XLEN-1)
  `CG_END

  `B_R_INSTR_NO_RS2_CG_BEGIN(clzw)
    `CP_VALUE_RANGE(num_leading_zeros, instr.rd_value, 0, XLEN/2-1)
  `CG_END

  `B_R_INSTR_NO_RS2_CG_BEGIN(ctzw)
    `CP_VALUE_RANGE(num_trailing_zeros, instr.rd_value, 0, XLEN/2-1)
  `CG_END

  // Count Bits Set (pcnt)
  `B_R_INSTR_NO_RS2_CG_BEGIN(pcnt)
    `CP_VALUE_RANGE(num_set_bits, instr.rd_value, 0, XLEN-1)
  `CG_END

  `B_R_INSTR_NO_RS2_CG_BEGIN(pcntw)
    `CP_VALUE_RANGE(num_set_bits, instr.rd_value, 0, XLEN/2-1)
  `CG_END

  // Logic-with-negate (andn, orn, xnor)
  `B_R_INSTR_CG_BEGIN(andn)
  `CG_END

  `B_R_INSTR_CG_BEGIN(orn)
  `CG_END

  `B_R_INSTR_CG_BEGIN(xnor)
  `CG_END

  // Pack two words in one register (pack, packu, packh)
  `B_R_INSTR_CG_BEGIN(pack)
  `CG_END

  `B_R_INSTR_CG_BEGIN(packu)
  `CG_END

  `B_R_INSTR_CG_BEGIN(packh)
  `CG_END

  `B_R_INSTR_CG_BEGIN(packw)
  `CG_END

  `B_R_INSTR_CG_BEGIN(packuw)
  `CG_END

  // Min/max instructions (min, max, minu, maxu)
  `B_R_INSTR_CG_BEGIN(min)
    cp_rs1_gt_rs2  : coverpoint (longint'(instr.rs1_value) > longint'(instr.rs2_value));
    cp_rs1_eq_rs2  : coverpoint (instr.rs1_value == instr.rs2_value) {
      bins equal = {1};
    }
  `CG_END

  `B_R_INSTR_CG_BEGIN(max)
    cp_rs1_gt_rs2  : coverpoint (longint'(instr.rs1_value) > longint'(instr.rs2_value));
    cp_rs1_eq_rs2  : coverpoint (instr.rs1_value == instr.rs2_value) {
      bins equal = {1};
    }
  `CG_END

  `B_R_INSTR_CG_BEGIN(minu)
    cp_rs1_gt_rs2  : coverpoint (instr.rs1_value > instr.rs2_value);
    cp_rs1_eq_rs2  : coverpoint (instr.rs1_value == instr.rs2_value) {
      bins equal = {1};
    }
  `CG_END

  `B_R_INSTR_CG_BEGIN(maxu)
    cp_rs1_gt_rs2  : coverpoint (instr.rs1_value > instr.rs2_value);
    cp_rs1_eq_rs2  : coverpoint (instr.rs1_value == instr.rs2_value) {
      bins equal = {1};
    }
  `CG_END

  // Sign-extend instructions (sext.b, sext.h)
  `B_R_INSTR_NO_RS2_CG_BEGIN(sext_b)
  `CG_END

  `B_R_INSTR_NO_RS2_CG_BEGIN(sext_h)
  `CG_END

  // Single-bit instructions (sbset, sbclr, sbinv, sbext)
  `B_R_INSTR_CG_BEGIN(sbset)
    `CP_VALUE_RANGE(bit_location, instr.rs2_value, 0, XLEN-1)
  `CG_END

  `B_R_INSTR_CG_BEGIN(sbclr)
    `CP_VALUE_RANGE(bit_location, instr.rs2_value, 0, XLEN-1)
  `CG_END

  `B_R_INSTR_CG_BEGIN(sbinv)
    `CP_VALUE_RANGE(bit_location, instr.rs2_value, 0, XLEN-1)
  `CG_END

  `B_R_INSTR_CG_BEGIN(sbext)
    `CP_VALUE_RANGE(bit_location, instr.rs2_value, 0, XLEN-1)
  `CG_END

  `B_I_INSTR_CG_BEGIN(sbseti)
    `CP_VALUE_RANGE(bit_location, instr.imm, 0, XLEN-1)
  `CG_END

  `B_I_INSTR_CG_BEGIN(sbclri)
    `CP_VALUE_RANGE(bit_location, instr.imm, 0, XLEN-1)
  `CG_END

  `B_I_INSTR_CG_BEGIN(sbinvi)
    `CP_VALUE_RANGE(bit_location, instr.imm, 0, XLEN-1)
  `CG_END

  `B_I_INSTR_CG_BEGIN(sbexti)
    `CP_VALUE_RANGE(bit_location, instr.imm, 0, XLEN-1)
  `CG_END

  // Shift Ones (Left/Right) (slo, sloi, sro, sroi)
  `B_R_INSTR_CG_BEGIN(slo)
    `CP_VALUE_RANGE(num_ones_shift, instr.rs2_value, 0, XLEN-1)
  `CG_END

  `B_R_INSTR_CG_BEGIN(sro)
    `CP_VALUE_RANGE(num_ones_shift, instr.rs2_value, 0, XLEN-1)
  `CG_END

  `B_I_INSTR_CG_BEGIN(sloi)
    `CP_VALUE_RANGE(num_ones_shift, instr.imm, 0, XLEN-1)
  `CG_END

  `B_I_INSTR_CG_BEGIN(sroi)
    `CP_VALUE_RANGE(num_ones_shift, instr.imm, 0, XLEN-1)
  `CG_END

  `B_R_INSTR_CG_BEGIN(slow)
    `CP_VALUE_RANGE(num_ones_shift, instr.rs2_value, 0, XLEN/2-1)
  `CG_END

  `B_R_INSTR_CG_BEGIN(srow)
    `CP_VALUE_RANGE(num_ones_shift, instr.rs2_value, 0, XLEN/2-1)
  `CG_END

  `B_I_INSTR_CG_BEGIN(sloiw)
    `CP_VALUE_RANGE(num_ones_shift, instr.imm, 0, XLEN/2-1)
  `CG_END

  `B_I_INSTR_CG_BEGIN(sroiw)
    `CP_VALUE_RANGE(num_ones_shift, instr.imm, 0, XLEN/2-1)
  `CG_END

  // Rotate (Left/Right) (rol, ror, rori)
  `B_R_INSTR_CG_BEGIN(ror)
    `CP_VALUE_RANGE(num_bit_rotate, instr.rs2_value, 0, XLEN-1)
  `CG_END

  `B_R_INSTR_CG_BEGIN(rol)
    `CP_VALUE_RANGE(num_bit_rotate, instr.rs2_value, 0, XLEN-1)
  `CG_END

  `B_I_INSTR_CG_BEGIN(rori)
    `CP_VALUE_RANGE(num_bit_rotate, instr.imm, 0, XLEN-1)
  `CG_END

  `B_R_INSTR_CG_BEGIN(rorw)
    `CP_VALUE_RANGE(num_bit_rotate, instr.rs2_value, 0, XLEN/2-1)
  `CG_END

  `B_R_INSTR_CG_BEGIN(rolw)
    `CP_VALUE_RANGE(num_bit_rotate, instr.rs2_value, 0, XLEN/2-1)
  `CG_END

  `B_I_INSTR_CG_BEGIN(roriw)
    `CP_VALUE_RANGE(num_bit_rotate, instr.imm, 0, XLEN/2-1)
  `CG_END

  // Generalized Reverse (grev, grevi, rev)
  `B_R_INSTR_CG_BEGIN(grev)
    `CP_VALUE_RANGE(reverse_mode, instr.rs2_value, 0, XLEN-1)
  `CG_END

  `B_I_INSTR_CG_BEGIN(grevi)
    `CP_VALUE_RANGE(reverse_mode, instr.imm, 0, XLEN-1)
  `CG_END

  `B_R_INSTR_CG_BEGIN(grevw)
    `CP_VALUE_RANGE(reverse_mode, instr.rs2_value, 0, XLEN/2-1)
  `CG_END

  `B_I_INSTR_CG_BEGIN(greviw)
    `CP_VALUE_RANGE(reverse_mode, instr.imm, 0, XLEN/2-1)
  `CG_END

  // Generalized Shuffle (shfl, unshfl, shfli, unshfli, zip, unzip)
  `B_R_INSTR_CG_BEGIN(shfl)
    `CP_VALUE_RANGE(shuffle_mode, instr.rs2_value, 0, XLEN/2-1)
  `CG_END

  `B_R_INSTR_CG_BEGIN(unshfl)
    `CP_VALUE_RANGE(shuffle_mode, instr.rs2_value, 0, XLEN/2-1)
  `CG_END

  `B_I_INSTR_CG_BEGIN(shfli)
    `CP_VALUE_RANGE(shuffle_mode, instr.imm, 0, XLEN/2-1)
  `CG_END

  `B_I_INSTR_CG_BEGIN(unshfli)
    `CP_VALUE_RANGE(shuffle_mode, instr.imm, 0, XLEN/2-1)
  `CG_END

  `B_R_INSTR_CG_BEGIN(shflw)
    `CP_VALUE_RANGE(shuffle_mode, instr.rs2_value, 0, XLEN/2-1)
  `CG_END

  `B_R_INSTR_CG_BEGIN(unshflw)
    `CP_VALUE_RANGE(shuffle_mode, instr.rs2_value, 0, XLEN/2-1)
  `CG_END

  // Generalized OR-Combine (gorc, gorci)
  `B_R_INSTR_CG_BEGIN(gorc)
    `CP_VALUE_RANGE(or_combine_mode, instr.rs2_value, 0, XLEN-1)
  `CG_END

  `B_I_INSTR_CG_BEGIN(gorci)
    `CP_VALUE_RANGE(or_combine_mode, instr.imm, 0, XLEN-1)
  `CG_END

  `B_R_INSTR_CG_BEGIN(gorcw)
    `CP_VALUE_RANGE(or_combine_mode, instr.rs2_value, 0, XLEN/2-1)
  `CG_END

  `B_I_INSTR_CG_BEGIN(gorciw)
    `CP_VALUE_RANGE(or_combine_mode, instr.imm, 0, XLEN/2-1)
  `CG_END

  // Bit-Field Place (bfp)
  `B_R_INSTR_CG_BEGIN(bfp)
    // cover all values of length and offset
    cp_len: coverpoint instr.rs2_value[27:24] iff (XLEN == 32) {
      `ENABLE_CP_BY_XLEN(32)
      bins values[] = {[0:XLEN/2-1]};
    }
    cp_offset: coverpoint instr.rs2_value[20:16] iff (XLEN == 32) {
      `ENABLE_CP_BY_XLEN(32)
      bins values[] = {[0:XLEN-1]};
    }
    cp_len_64bit_sel01: coverpoint instr.rs2_value[60:56] iff (XLEN == 64 &&
          instr.rs2_value[XLEN-1:XLEN-2] == 2'b10) {
      `ENABLE_CP_BY_XLEN(64)
      bins values[] = {[0:XLEN/2-1]};
    }
    cp_offset_64bit_sel01: coverpoint instr.rs2_value[53:48] iff (XLEN == 64 &&
          instr.rs2_value[XLEN-1:XLEN-2] == 2'b10) {
      `ENABLE_CP_BY_XLEN(64)
      bins values = {[0:XLEN-1]};
    }
    cp_len_64bit_not_sel01: coverpoint instr.rs2_value[60:56] iff (XLEN == 64 &&
          instr.rs2_value[XLEN-1:XLEN-2] != 2'b10) {
      `ENABLE_CP_BY_XLEN(64)
      bins values[] = {[0:XLEN/2-1]};
    }
    cp_offset_64bit_not_sel01: coverpoint instr.rs2_value[53:48] iff (XLEN == 64 &&
          instr.rs2_value[XLEN-1:XLEN-2] != 2'b10) {
      `ENABLE_CP_BY_XLEN(64)
      bins values[] = {[0:XLEN-1]};
    }
  `CG_END

  `B_R_INSTR_CG_BEGIN(bfpw)
    // cover all values of length and offset
    `CP_VALUE_RANGE(length, instr.rs2_value[27:24], 0, XLEN/2-1)
    `CP_VALUE_RANGE(offset, instr.rs2_value[20:16], 0, XLEN/2-1)
  `CG_END

  `B_R_INSTR_CG_BEGIN(bext)
  `CG_END

  `B_R_INSTR_CG_BEGIN(bextw)
  `CG_END

  `B_R_INSTR_CG_BEGIN(bdep)
  `CG_END

  `B_R_INSTR_CG_BEGIN(bdepw)
  `CG_END

  `B_R_INSTR_CG_BEGIN(clmul)
  `CG_END

  `B_R_INSTR_CG_BEGIN(clmulh)
  `CG_END

  `B_R_INSTR_CG_BEGIN(clmulr)
  `CG_END

  `B_R_INSTR_CG_BEGIN(clmulw)
  `CG_END

  `B_R_INSTR_CG_BEGIN(clmulhw)
  `CG_END

  `B_R_INSTR_CG_BEGIN(clmulrw)
  `CG_END

  `B_R_INSTR_NO_RS2_CG_BEGIN(crc32_b)
  `CG_END

  `B_R_INSTR_NO_RS2_CG_BEGIN(crc32_h)
  `CG_END

  `B_R_INSTR_NO_RS2_CG_BEGIN(crc32_w)
  `CG_END

  `B_R_INSTR_NO_RS2_CG_BEGIN(crc32c_b)
  `CG_END

  `B_R_INSTR_NO_RS2_CG_BEGIN(crc32c_h)
  `CG_END

  `B_R_INSTR_NO_RS2_CG_BEGIN(crc32c_w)
  `CG_END

  `B_R_INSTR_NO_RS2_CG_BEGIN(crc32_d)
  `CG_END

  `B_R_INSTR_NO_RS2_CG_BEGIN(crc32c_d)
  `CG_END

  `B_R_INSTR_CG_BEGIN(bmator)
  `CG_END

  `B_R_INSTR_CG_BEGIN(bmatxor)
  `CG_END

  `B_R_INSTR_NO_RS2_CG_BEGIN(bmatflip)
  `CG_END

  `B_R4_INSTR_CG_BEGIN(cmix)
  `CG_END

  `B_R4_INSTR_CG_BEGIN(cmov)
  `CG_END

  `B_R4_INSTR_CG_BEGIN(fsl)
    `CP_VALUE_RANGE(num_shift, instr.rs2_value, 0, 2*XLEN-1)
  `CG_END

  `B_R4_INSTR_CG_BEGIN(fsr)
    `CP_VALUE_RANGE(num_shift, instr.rs2_value, 0, 2*XLEN-1)
  `CG_END

  `B_I_INSTR_CG_BEGIN(fsri)
    cp_rs3 : coverpoint instr.rs3;
    `CP_VALUE_RANGE(num_shift, instr.imm, 0, XLEN-1)
  `CG_END

  `B_R4_INSTR_CG_BEGIN(fslw)
    `CP_VALUE_RANGE(num_shift, instr.rs2_value, 0, 2*XLEN-1)
  `CG_END

  `B_R4_INSTR_CG_BEGIN(fsrw)
    `CP_VALUE_RANGE(num_shift, instr.rs2_value, 0, 2*XLEN-1)
  `CG_END

  `B_I_INSTR_CG_BEGIN(fsriw)
    cp_rs3 : coverpoint instr.rs3;
    `CP_VALUE_RANGE(num_shift, instr.imm, 0, XLEN/2-1)
  `CG_END

  `B_R_INSTR_CG_BEGIN(addwu)
  `CG_END

  `B_R_INSTR_CG_BEGIN(subwu)
  `CG_END

  `B_I_INSTR_CG_BEGIN(addiwu)
  `CG_END

  `B_R_INSTR_CG_BEGIN(addu_w)
  `CG_END

  `B_R_INSTR_CG_BEGIN(subu_w)
  `CG_END

  `B_I_INSTR_CG_BEGIN(slliu_w)
    `CP_VALUE_RANGE(num_shift, instr.imm, 0, XLEN-1)
  `CG_END

  // CSR instructions
  `CSR_INSTR_CG_BEGIN(csrrw)
    cp_rs1 : coverpoint instr.rs1;
  `CG_END

  `CSR_INSTR_CG_BEGIN(csrrs)
    cp_rs1 : coverpoint instr.rs1;
  `CG_END

  `CSR_INSTR_CG_BEGIN(csrrc)
    cp_rs1 : coverpoint instr.rs1;
  `CG_END

  `CSR_INSTR_CG_BEGIN(csrrwi)
  `CG_END

  `CSR_INSTR_CG_BEGIN(csrrsi)
  `CG_END

  `CSR_INSTR_CG_BEGIN(csrrci)
  `CG_END

  covergroup rv32i_misc_cg with function sample(riscv_instr instr);
    cp_misc : coverpoint instr.instr_name {
      bins instr[] = {FENCE, FENCE_I, EBREAK, ECALL, MRET};
    }
  endgroup

  covergroup wfi_cg with function sample(riscv_instr instr);
    cp_misc : coverpoint instr.instr_name {
      bins wfi = {WFI};
    }
  endgroup

  // RV32M
  `R_INSTR_CG_BEGIN(mul)
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(mulh)
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(mulhsu)
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(mulhu)
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(div)
    cp_div_result: coverpoint instr.div_result;
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(divu)
    cp_div_result: coverpoint instr.div_result {
      ignore_bins no_overflow = {riscv_instr::DIV_OVERFLOW};
    }
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(rem)
    cp_div_result: coverpoint instr.div_result;
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(remu)
    cp_div_result: coverpoint instr.div_result {
      ignore_bins no_overflow = {riscv_instr::DIV_OVERFLOW};
    }
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  // RV64M
  // Below instructions only do calculation based on lower 32 bits, and extend the result to 64
  // bits. Add special covergroup for corner cases

  `R_INSTR_CG_BEGIN(mulw)
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(divw)
    cp_div_result: coverpoint instr.div_result;
    cp_div_zero  : coverpoint instr.rs2_value iff (instr.rs2_value[31:0] == 0) {
      bins zero     = {0};
      bins non_zero = default;
    }
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(divuw)
    cp_div_result: coverpoint instr.div_result {
      ignore_bins no_overflow = {riscv_instr::DIV_OVERFLOW};
    }
    cp_div_zero  : coverpoint instr.rs2_value iff (instr.rs2_value[31:0] == 0) {
      bins zero     = {0};
      bins non_zero = default;
    }
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(remw)
    cp_div_result: coverpoint instr.div_result;
    cp_div_zero  : coverpoint instr.rs2_value iff (instr.rs2_value[31:0] == 0) {
      bins zero     = {0};
      bins non_zero = default;
    }
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(remuw)
    cp_div_result: coverpoint instr.div_result {
      ignore_bins no_overflow = {riscv_instr::DIV_OVERFLOW};
    }
    cp_div_zero  : coverpoint instr.rs2_value iff (instr.rs2_value[31:0] == 0) {
      bins zero     = {0};
      bins non_zero = default;
    }
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  // RV64I
  `LOAD_INSTR_CG_BEGIN(lwu)
    cp_align: coverpoint instr.unaligned_mem_access;
  `CG_END

  `LOAD_INSTR_CG_BEGIN(ld)
    cp_align: coverpoint instr.unaligned_mem_access;
  `CG_END

  `STORE_INSTR_CG_BEGIN(sd)
    cp_misalign: coverpoint instr.unaligned_mem_access;
  `CG_END

  `R_INSTR_CG_BEGIN(sraw)
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(sllw)
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(srlw)
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  // imm[5] could be 1 for RV64I SLLI/SRAI/SRLI
  `INSTR_CG_BEGIN(srai64)
    cp_imm: coverpoint instr.imm[5];
  `CG_END

  `INSTR_CG_BEGIN(slli64)
    cp_imm: coverpoint instr.imm[5];
  `CG_END

  `INSTR_CG_BEGIN(srli64)
    cp_imm: coverpoint instr.imm[5];
  `CG_END

  `INSTR_CG_BEGIN(sraiw)
    cp_rs1         : coverpoint instr.rs1;
    cp_rd          : coverpoint instr.rd;
    cp_rs1_sign    : coverpoint instr.rs1_sign;
    cp_rd_sign     : coverpoint instr.rd_sign;
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard;)
  `CG_END

  `INSTR_CG_BEGIN(slliw)
    cp_rs1         : coverpoint instr.rs1;
    cp_rd          : coverpoint instr.rd;
    cp_rs1_sign    : coverpoint instr.rs1_sign;
    cp_rd_sign     : coverpoint instr.rd_sign;
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard;)
  `CG_END

  `INSTR_CG_BEGIN(srliw)
    cp_rs1         : coverpoint instr.rs1;
    cp_rd          : coverpoint instr.rd;
    cp_rs1_sign    : coverpoint instr.rs1_sign;
    cp_rd_sign     : coverpoint instr.rd_sign;
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard;)
  `CG_END

  `R_INSTR_CG_BEGIN(addw)
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign, cp_rd_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(subw)
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign, cp_rd_sign;
  `CG_END

  `I_INSTR_CG_BEGIN(addiw)
    cp_sign_cross: cross cp_rs1_sign, cp_imm_sign, cp_rd_sign;
  `CG_END

  // RV32C

  `CL_INSTR_CG_BEGIN(c_lw)
  `CG_END

  `CL_SP_INSTR_CG_BEGIN(c_lwsp)
  `CG_END

  `CS_INSTR_CG_BEGIN(c_sw)
  `CG_END

  `CS_SP_INSTR_CG_BEGIN(c_swsp)
  `CG_END

  `CIW_INSTR_CG_BEGIN(c_addi4spn)
  `CG_END

  `CI_INSTR_NON_ZERO_CG_BEGIN(c_addi)
  `CG_END

  `INSTR_CG_BEGIN(c_addi16sp)
    cp_imm_sign : coverpoint instr.imm_sign;
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard {
      bins valid_hazard[] = {NO_HAZARD, WAR_HAZARD, WAW_HAZARD};
    })
  `CG_END

  `CI_INSTR_NON_ZERO_CG_BEGIN(c_li)
  `CG_END

  `INSTR_CG_BEGIN(c_lui)
    cp_rd : coverpoint instr.rd {
     `DV(ignore_bins bin = {ZERO, SP};)
    }
  `CG_END

  `CA_INSTR_CG_BEGIN(c_sub)
  `CG_END

  `INSTR_CG_BEGIN(c_add)
    cp_rs2         : coverpoint instr.rs2 {
      ignore_bins non_zero = {ZERO};
    }
    cp_rd          : coverpoint instr.rd {
      ignore_bins non_zero = {ZERO};
    }
    cp_rs2_sign    : coverpoint instr.rs2_sign;
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard;)
  `CG_END

  `INSTR_CG_BEGIN(c_mv)
    cp_rs2         : coverpoint instr.rs2 {
      ignore_bins non_zero = {ZERO};
    }
    cp_rd          : coverpoint instr.rd {
      ignore_bins non_zero = {ZERO};
    }
    cp_rs2_sign    : coverpoint instr.rs2_sign;
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard;)
  `CG_END

  `CB_INSTR_CG_BEGIN(c_andi)
    cp_imm_sign : coverpoint instr.imm_sign;
  `CG_END

  `CA_INSTR_CG_BEGIN(c_xor)
  `CG_END

  `CA_INSTR_CG_BEGIN(c_or)
  `CG_END

  `CA_INSTR_CG_BEGIN(c_and)
  `CG_END

  `CB_INSTR_CG_BEGIN(c_beqz)
    cp_imm_sign : coverpoint instr.imm_sign;
  `CG_END

  `CB_INSTR_CG_BEGIN(c_bnez)
    cp_imm_sign : coverpoint instr.imm_sign;
  `CG_END

  `CB_INSTR_CG_BEGIN(c_srli)
  `CG_END

  `CB_INSTR_CG_BEGIN(c_srai)
  `CG_END

  `INSTR_CG_BEGIN(c_slli)
    cp_rd : coverpoint instr.rd {
      ignore_bins non_zero = {ZERO};
    }
    `DV(cp_gpr_hazard  : coverpoint instr.gpr_hazard {
      bins valid_hazard[] = {NO_HAZARD, RAW_HAZARD};
    })
  `CG_END

  `CJ_INSTR_CG_BEGIN(c_j)
  `CG_END

  `CJ_INSTR_CG_BEGIN(c_jal)
  `CG_END

  `INSTR_CG_BEGIN(c_jr)
    cp_rs1 : coverpoint instr.rs1 {
      `DV(ignore_bins zero = {ZERO};)
    }
    cp_rs1_align : coverpoint instr.rs1_value[1:0];
  `CG_END

  `INSTR_CG_BEGIN(c_jalr)
    cp_rs1 : coverpoint instr.rs1 {
      `DV(ignore_bins zero = {ZERO};)
    }
    cp_rs1_align : coverpoint instr.rs1_value[1:0];
    cp_rd_align : coverpoint instr.rs1_value[1];
  `CG_END

  // RV64C

  `CL_INSTR_CG_BEGIN(c_ld)
  `CG_END

  `CL_SP_INSTR_CG_BEGIN(c_ldsp)
  `CG_END

  `CS_INSTR_CG_BEGIN(c_sd)
  `CG_END

  `CS_SP_INSTR_CG_BEGIN(c_sdsp)
  `CG_END

  `CI_INSTR_NON_ZERO_CG_BEGIN(c_addiw)
  `CG_END

  `CA_INSTR_CG_BEGIN(c_subw)
  `CG_END

  `CA_INSTR_CG_BEGIN(c_addw)
  `CG_END

  `INSTR_CG_BEGIN(hint)
    cp_hint : coverpoint instr.binary[15:0] {
      wildcard bins addi    = {16'b0000_1xxx_x000_0001,
                               16'b0000_x1xx_x000_0001,
                               16'b0000_xx1x_x000_0001,
                               16'b0000_xxx1_x000_0001,
                               16'b0000_xxxx_1000_0001};
      wildcard bins li      = {16'b010x_0000_0xxx_xx01};
      wildcard bins lui     = {16'b011x_0000_0xxx_xx01};
      wildcard bins srli64  = {16'b1000_00xx_x000_0001};
      wildcard bins srai64  = {16'b1000_01xx_x000_0001};
      wildcard bins slli    = {16'b000x_0000_0xxx_xx10};
      wildcard bins slli64  = {16'b0000_xxxx_x000_0010};
      wildcard bins mv      = {16'b1000_0000_01xx_xx10,
                               16'b1000_0000_0x1x_xx10,
                               16'b1000_0000_0xx1_xx10,
                               16'b1000_0000_0xxx_1x10,
                               16'b1000_0000_0xxx_x110};
      wildcard bins add     = {16'b1001_0000_01xx_xx10,
                               16'b1001_0000_0x1x_xx10,
                               16'b1001_0000_0xx1_xx10,
                               16'b1001_0000_0xxx_1x10,
                               16'b1001_0000_0xxx_x110};
    }
  `CG_END

  // Cover all illegal compressed instruction
  covergroup illegal_compressed_instr_cg with function sample(bit [31:0] binary);
    cp_point : coverpoint binary[15:0] {
      wildcard bins c_illegal  = {16'b0};
      wildcard bins c_addi4spn = {16'b0000_0000_000x_x100,
                                  16'b0000_0000_000x_1x00,
                                  16'b0000_0000_0001_xx00};
      wildcard bins c_addiw    = {16'b001x_0000_0xxx_xx01};
      wildcard bins c_addi16sp = {16'b0110_0001_0000_0001};
      wildcard bins c_lui      = {16'b0110_xxxx_1000_0001,
                                  16'b0110_xx1x_x000_0001,
                                  16'b0110_x1xx_x000_0001,
                                  16'b0110_1xxx_x000_0001};
      wildcard bins c_reserv_0 = {16'b1001_11xx_x10x_xx01};
      wildcard bins c_reserv_1 = {16'b1001_11xx_x11x_xx01};
      wildcard bins c_jr       = {16'b1000_0000_0000_0010};
      wildcard bins c_lwsp     = {16'b010x_0000_0xxx_xx10};
      wildcard bins c_lqsp     = {16'b001x_0000_0xxx_xx10};
      wildcard bins c_ldsp     = {16'b011x_0000_0xxx_xx10};
    }
  endgroup

  // Cover all non-compressed opcode
  covergroup opcode_cg with function sample(bit [4:0] opcode);
    cp_opcode: coverpoint opcode;
  endgroup

  // Cover all compressed instruction opcode
  covergroup compressed_opcode_cg with function sample(bit [15:0] binary);
    cp_00 : coverpoint binary[15:13] iff (binary[1:0] == 2'b00);
    cp_01 : coverpoint binary[15:13] iff (binary[1:0] == 2'b01);
    cp_10 : coverpoint binary[15:13] iff (binary[1:0] == 2'b10);
  endgroup

  // Branch hit history
  covergroup branch_hit_history_cg;
    cp_branch_history: coverpoint branch_hit_history;
  endgroup

  // Instruction transition for all supported instructions
  /* TODO: Refine the transition functional coverage, not all combinations are interesting
  covergroup instr_trans_cg with function sample();
    cp_instr: coverpoint instr_name {
      bins instr[] = cp_instr with (is_supported_instr(riscv_instr_name_t'(item)));
    }
    cp_pre_instr: coverpoint pre_instr_name {
      // This is a helper coverpoint for cross coverpoint below, it should not be counted when
      // calculate the coverage score
      type_option.weight = 0;
      bins instr[] = cp_pre_instr with (is_supported_instr(riscv_instr_name_t'(item)));
    }
    cp_trans: cross cp_pre_instr, cp_instr {
      // Cover all instruction transitions, except for below system instructions
      ignore_bins ignore = binsof(cp_instr) intersect {ECALL, URET, SRET, SRET, DRET} ||
                           binsof(cp_pre_instr) intersect {ECALL, URET, SRET, SRET, DRET};
    }
  endgroup
  */

  covergroup privileged_csr_cg with function sample(bit [11:0] csr);
    cp_csr : coverpoint csr {
      bins pcsr[] = cp_csr with (item inside {implemented_csr});
    }
  endgroup

  // Privileged CSR covergroup
  covergroup mcause_exception_cg with function sample(exception_cause_t exception);
    cp_exception: coverpoint exception {
        bins exception[] = cp_exception with ((item inside {implemented_exception}));
       // bins exception[] = cp_exception with ((item inside {exception_list}));
    }
  endgroup

  covergroup mcause_interrupt_cg with function sample(interrupt_cause_t interrupt);
    cp_interrupt: coverpoint interrupt {
       bins interrupt[] = cp_interrupt with (item inside {implemented_interrupt});
    }
  endgroup

  covergroup mepc_alignment_cg with function sample(bit [XLEN-1:0] val);
    cp_align: coverpoint val[1:0] {
      bins alignment[] = {2'b00, 2'b10};
    }
  endgroup

  covergroup mstatus_m_cg with function sample(bit [XLEN-1:0] val);
    cp_mie  : coverpoint val[3];
    cp_mpie : coverpoint val[7];
    cp_mpp  : coverpoint val[12:11];
  endgroup

  covergroup fcsr_cg with function sample(bit [XLEN-1:0] val);
    cp_fflags : coverpoint val[4:0];
    cp_frm    : coverpoint val[7:5] {
      ignore_bins invalid = {3'b101, 3'b110};
    }
  endgroup

  `VECTOR_INCLUDE("riscv_instr_cover_group_inc_cg_add.sv")

  function new(riscv_instr_gen_config cfg);
    string opts;
    this.cfg = cfg;
    build_instr_list();
    `ifdef COMPLIANCE_MODE
      compliance_mode = 1;
    `endif
    // process coverage options
    void'($value$plusargs("iss_mode=%0d", iss_mode));

    if ($value$plusargs("cov_isa=%0s", opts)) begin
      if (!uvm_enum_wrapper#(riscv_instr_group_t)::from_name(opts, cov_isa)) begin
        `uvm_fatal("riscv_instr_covergroup",
                   $sformatf("Cannot find enum for specifed cov_isa=%0s", opts))
      end
      select_isa = 1'b1;
    end
    // TODO if we want to selectively enable/disable coverage based on categories...
    // e.g. +cov_category=OPV_CONFIG
    if ($test$plusargs("cov_category=")) begin
      string cov_category_str;
      void'($value$plusargs("cov_category=%0s", cov_category_str));
      $display("coverage option: +cov_category=%0s", cov_category_str);
      // used to further subset coverage (used by vectors)
    end

    if ($test$plusargs("stop_on_first_error")) begin
      $display("coverage option: +stop_on_first_error");
    end

   `VECTOR_INCLUDE("riscv_instr_cover_group_inc_cg_instantiation.sv")

    // RV32I instruction functional coverage instantiation
    `CG_SELECTOR_BEGIN(RV32I)
        add_cg = new();
        sub_cg = new();
        addi_cg = new();
        lui_cg = new();
        auipc_cg = new();
        sll_cg = new();
        srl_cg = new();
        sra_cg = new();
        slli_cg = new();
        srli_cg = new();
        srai_cg = new();
        and_cg = new();
        or_cg = new();
        xor_cg = new();
        andi_cg = new();
        ori_cg = new();
        xori_cg = new();
        slt_cg = new();
        sltu_cg = new();
        slti_cg = new();
        sltiu_cg = new();
        jal_cg = new();
        jalr_cg = new();
        beq_cg = new();
        bne_cg = new();
        blt_cg = new();
        bge_cg = new();
        bgeu_cg = new();
        bltu_cg = new();
        lb_cg = new();
        lh_cg = new();
        lw_cg = new();
        lbu_cg = new();
        lhu_cg = new();
        sb_cg = new();
        sh_cg = new();
        sw_cg = new();
    `CG_SELECTOR_END

    // TODO sort when there is a RV32ZICSR isa enum
    if (RV32I inside {supported_isa}) begin
      if (!compliance_mode) begin
        csrrw_cg = new();
        csrrs_cg = new();
        csrrc_cg = new();
        csrrwi_cg = new();
        csrrsi_cg = new();
        csrrci_cg = new();
      end
    end

    if (!compliance_mode) begin
      // instr_trans_cg = new();
      branch_hit_history_cg = new();
      rv32i_misc_cg = new();
      opcode_cg = new();
      // TODO: Enable WFI covergroup. It's currently disabled because OVPSIM will stop program
      // execution upon decoding WFI instruction
      if (!iss_mode) begin
        wfi_cg = new();
      end
    end

    if (RV32C inside {supported_isa} || RV64C inside {supported_isa}) begin
      if (!compliance_mode) begin
        compressed_opcode_cg = new();
        hint_cg = new();
        if (!cfg.disable_compressed_instr) begin
          illegal_compressed_instr_cg = new();
        end
      end
    end

    `CG_SELECTOR_BEGIN(RV32M)
      mul_cg = new();
      mulh_cg = new();
      mulhsu_cg = new();
      mulhu_cg = new();
      div_cg = new();
      divu_cg = new();
      rem_cg = new();
      remu_cg = new();
    `CG_SELECTOR_END

    `CG_SELECTOR_BEGIN(RV64M)
      mulw_cg = new();
      divw_cg = new();
      divuw_cg = new();
      remw_cg = new();
      remuw_cg = new();
    `CG_SELECTOR_END

    `CG_SELECTOR_BEGIN(RV64I)
      lwu_cg = new();
      ld_cg = new();
      sd_cg = new();
      slli64_cg = new();
      srli64_cg = new();
      srai64_cg = new();
      sllw_cg = new();
      slliw_cg = new();
      srlw_cg = new();
      srliw_cg = new();
      sraw_cg = new();
      sraiw_cg = new();
      addw_cg = new();
      addiw_cg = new();
      subw_cg = new();
    `CG_SELECTOR_END

    `CG_SELECTOR_BEGIN(RV32C)
      c_lw_cg = new();
      c_sw_cg = new();
      c_lwsp_cg = new();
      c_swsp_cg = new();
      c_addi4spn_cg = new();
      c_addi_cg = new();
      c_addi16sp_cg = new();
      c_li_cg = new();
      c_lui_cg = new();
      c_sub_cg = new();
      c_add_cg = new();
      c_mv_cg = new();
      c_andi_cg = new();
      c_xor_cg = new();
      c_or_cg = new();
      c_and_cg = new();
      c_beqz_cg = new();
      c_bnez_cg = new();
      c_srli_cg = new();
      c_srai_cg = new();
      c_slli_cg = new();
      c_j_cg = new();
      if (XLEN == 32) begin
        c_jal_cg = new();
      end
      c_jr_cg = new();
      c_jalr_cg = new();
    `CG_SELECTOR_END

    `CG_SELECTOR_BEGIN(RV64C)
      c_ld_cg = new();
      c_sd_cg = new();
      c_ldsp_cg = new();
      c_sdsp_cg = new();
      c_addiw_cg = new();
      c_subw_cg = new();
      c_addw_cg = new();
    `CG_SELECTOR_END

    `CG_SELECTOR_BEGIN(RV32F)
      flw_cg      = new();
      fsw_cg      = new();
      fadd_s_cg   = new();
      fsub_s_cg   = new();
      fmul_s_cg   = new();
      fdiv_s_cg   = new();
      fsqrt_s_cg  = new();
      fmin_s_cg   = new();
      fmax_s_cg   = new();
      fmadd_s_cg  = new();
      fnmadd_s_cg = new();
      fmsub_s_cg  = new();
      fnmsub_s_cg = new();
      fcvt_w_s_cg  = new();
      fcvt_wu_s_cg = new();
      fcvt_s_w_cg  = new();
      fcvt_s_wu_cg = new();
      fsgnj_s_cg   = new();
      fsgnjn_s_cg  = new();
      fsgnjx_s_cg  = new();
      fmv_x_w_cg   = new();
      fmv_w_x_cg   = new();
      feq_s_cg     = new();
      flt_s_cg     = new();
      fle_s_cg     = new();
      fclass_s_cg  = new();
    `CG_SELECTOR_END

    `CG_SELECTOR_BEGIN(RV32D)
      fld_cg      = new();
      fsd_cg      = new();
      fadd_d_cg   = new();
      fsub_d_cg   = new();
      fdiv_d_cg   = new();
      fmul_d_cg   = new();
      fmadd_d_cg  = new();
      fnmadd_d_cg = new();
      fmsub_d_cg  = new();
      fnmsub_d_cg = new();
      fsqrt_d_cg  = new();
      fmin_d_cg   = new();
      fmax_d_cg   = new();
      fsgnj_d_cg   = new();
      fsgnjn_d_cg  = new();
      fsgnjx_d_cg  = new();
      feq_d_cg     = new();
      flt_d_cg     = new();
      fle_d_cg     = new();
      fcvt_w_d_cg  = new();
      fcvt_wu_d_cg = new();
      fcvt_d_w_cg  = new();
      fcvt_d_wu_cg = new();
      fclass_d_cg  = new();
    `CG_SELECTOR_END

    `CG_SELECTOR_BEGIN(RV64F)
      fcvt_l_s_cg  = new();
      fcvt_lu_s_cg = new();
      fcvt_s_l_cg  = new();
      fcvt_s_lu_cg = new();
    `CG_SELECTOR_END

    `CG_SELECTOR_BEGIN(RV64D)
      fmv_x_d_cg   = new();
      fmv_d_x_cg   = new();
      fcvt_d_s_cg  = new();
      fcvt_s_d_cg  = new();
      fcvt_l_d_cg  = new();
      fcvt_lu_d_cg = new();
      fcvt_d_l_cg  = new();
      fcvt_d_lu_cg = new();
    `CG_SELECTOR_END

    `CG_SELECTOR_BEGIN(RV32B)
      clz_cg      = new();
      ctz_cg      = new();
      pcnt_cg     = new();
      andn_cg     = new();
      orn_cg      = new();
      xnor_cg     = new();
      pack_cg     = new();
      packh_cg    = new();
      min_cg      = new();
      max_cg      = new();
      minu_cg     = new();
      maxu_cg     = new();
      sext_b_cg   = new();
      sext_h_cg   = new();
      sbset_cg    = new();
      sbclr_cg    = new();
      sbinv_cg    = new();
      sbext_cg    = new();
      sbseti_cg   = new();
      sbclri_cg   = new();
      sbinvi_cg   = new();
      sbexti_cg   = new();
      slo_cg      = new();
      sro_cg      = new();
      sloi_cg     = new();
      sroi_cg     = new();
      ror_cg      = new();
      rol_cg      = new();
      rori_cg     = new();
      grev_cg     = new();
      grevi_cg    = new();
      shfli_cg    = new();
      unshfli_cg  = new();
      shfl_cg     = new();
      unshfl_cg   = new();
      gorc_cg     = new();
      gorci_cg    = new();
      bfp_cg      = new();
      bext_cg     = new();
      bdep_cg     = new();
      clmul_cg    = new();
      clmulh_cg   = new();
      clmulr_cg   = new();
      crc32_b_cg  = new();
      crc32_h_cg  = new();
      crc32_w_cg  = new();
      crc32c_b_cg = new();
      crc32c_h_cg = new();
      crc32c_w_cg = new();
      cmix_cg     = new();
      cmov_cg     = new();
      fsl_cg      = new();
      fsr_cg      = new();
      fsri_cg     = new();
    `CG_SELECTOR_END

    `CG_SELECTOR_BEGIN(RV64B)
      clzw_cg     = new();
      ctzw_cg     = new();
      pcntw_cg    = new();
      packw_cg    = new();
      packuw_cg   = new();
      slow_cg     = new();
      srow_cg     = new();
      sloiw_cg    = new();
      sroiw_cg    = new();
      rorw_cg     = new();
      rolw_cg     = new();
      roriw_cg    = new();
      grevw_cg    = new();
      greviw_cg   = new();
      shflw_cg    = new();
      unshflw_cg  = new();
      gorcw_cg    = new();
      gorciw_cg   = new();
      bfpw_cg     = new();
      bextw_cg    = new();
      bdepw_cg    = new();
      clmulw_cg   = new();
      clmulhw_cg  = new();
      clmulrw_cg  = new();
      crc32_d_cg  = new();
      crc32c_d_cg = new();
      bmator_cg   = new();
      bmatxor_cg  = new();
      bmatflip_cg = new();
      fslw_cg     = new();
      fsrw_cg     = new();
      fsriw_cg    = new();
      addwu_cg    = new();
      subwu_cg    = new();
      addiwu_cg   = new();
      addu_w_cg   = new();
      subu_w_cg   = new();
      slliu_w_cg  = new();
    `CG_SELECTOR_END
    // Ignore the exception which cannot be covered when running with ISS
    if (iss_mode) begin
      int i;
      ignored_exceptions = {INSTRUCTION_ACCESS_FAULT, LOAD_ACCESS_FAULT};
      if (support_unaligned_load_store) begin
        ignored_exceptions = {ignored_exceptions, LOAD_ADDRESS_MISALIGNED};
      end
    end

    foreach (riscv_instr_pkg::implemented_exception[i]) begin
      if (!(riscv_instr_pkg::implemented_exception[i] inside {ignored_exceptions})) begin
        exception_list.push_back(riscv_instr_pkg::implemented_exception[i]);
      end
    end

    if (!compliance_mode) begin
      if (!iss_mode) begin
        // Expect to cover below coverpoint in RTL sim mode only
        privileged_csr_cg = new();
        mcause_exception_cg = new();
        mcause_interrupt_cg = new();
        mstatus_m_cg = new();
        fcsr_cg = new();
      end
      if (!cfg.disable_compressed_instr) begin
        mepc_alignment_cg = new();
      end
    end
  endfunction

  function void sample(riscv_instr instr);
    instr_cnt += 1;
    if (instr_cnt > 1) begin
      instr.check_hazard_condition(pre_instr);
    end
    if ((instr.binary[1:0] != 2'b11) && (RV32C inside {supported_isa})) begin
      `SAMPLE(hint_cg, instr);
      `SAMPLE(compressed_opcode_cg, instr.binary[15:0]);
      `SAMPLE(illegal_compressed_instr_cg, instr.binary);
    end
    if (instr.binary[1:0] == 2'b11) begin
      `SAMPLE(opcode_cg, instr.binary[6:2]);
    end
    case (instr.instr_name)
      ADD        : `SAMPLE(add_cg, instr)
      SUB        : `SAMPLE(sub_cg, instr)
      ADDI       : `SAMPLE(addi_cg, instr)
      LUI        : `SAMPLE(lui_cg, instr)
      AUIPC      : `SAMPLE(auipc_cg, instr)
      SLL        : `SAMPLE(sll_cg, instr)
      SRL        : `SAMPLE(srl_cg, instr)
      SRA        : `SAMPLE(sra_cg, instr)
      SLLI       : begin
                     `SAMPLE(slli_cg, instr)
                     `SAMPLE(slli64_cg, instr)
                   end
      SRLI       : begin
                     `SAMPLE(srli_cg, instr)
                     `SAMPLE(srli64_cg, instr)
                   end
      SRAI       : begin
                     `SAMPLE(srai_cg, instr)
                     `SAMPLE(srai64_cg, instr)
                   end
      AND        : `SAMPLE(and_cg, instr)
      OR         : `SAMPLE(or_cg, instr)
      XOR        : `SAMPLE(xor_cg, instr)
      ANDI       : `SAMPLE(andi_cg, instr)
      ORI        : `SAMPLE(ori_cg, instr)
      XORI       : `SAMPLE(xori_cg, instr)
      SLT        : `SAMPLE(slt_cg, instr)
      SLTU       : `SAMPLE(sltu_cg, instr)
      SLTI       : `SAMPLE(slti_cg, instr)
      SLTIU      : `SAMPLE(sltiu_cg, instr)
      JAL        : `SAMPLE(jal_cg, instr)
      JALR       : `SAMPLE(jalr_cg, instr)
      BEQ        : `SAMPLE(beq_cg, instr)
      BNE        : `SAMPLE(bne_cg, instr)
      BLT        : `SAMPLE(blt_cg, instr)
      BGE        : `SAMPLE(bge_cg, instr)
      BLTU       : `SAMPLE(bltu_cg, instr)
      BGEU       : `SAMPLE(bgeu_cg, instr)
      LW         : `SAMPLE(lw_cg, instr)
      LH         : `SAMPLE(lh_cg, instr)
      LB         : `SAMPLE(lb_cg, instr)
      LBU        : `SAMPLE(lbu_cg, instr)
      LHU        : `SAMPLE(lhu_cg, instr)
      SW         : `SAMPLE(sw_cg, instr)
      SH         : `SAMPLE(sh_cg, instr)
      SB         : `SAMPLE(sb_cg, instr)
      CSRRW      : `SAMPLE(csrrw_cg, instr)
      CSRRS      : `SAMPLE(csrrs_cg, instr)
      CSRRC      : `SAMPLE(csrrc_cg, instr)
      CSRRWI     : `SAMPLE(csrrwi_cg, instr)
      CSRRSI     : `SAMPLE(csrrsi_cg, instr)
      CSRRCI     : `SAMPLE(csrrci_cg, instr)
      WFI        : `SAMPLE(wfi_cg, instr)
      MUL        : `SAMPLE(mul_cg, instr)
      MULH       : `SAMPLE(mulh_cg, instr)
      MULHSU     : `SAMPLE(mulhsu_cg, instr)
      MULHU      : `SAMPLE(mulhu_cg, instr)
      DIV        : `SAMPLE(div_cg, instr)
      DIVU       : `SAMPLE(divu_cg, instr)
      REM        : `SAMPLE(rem_cg, instr)
      REMU       : `SAMPLE(remu_cg, instr)
      MULW       : `SAMPLE(mulw_cg, instr)
      DIVW       : `SAMPLE(divw_cg, instr)
      DIVUW      : `SAMPLE(divuw_cg, instr)
      REMW       : `SAMPLE(remw_cg, instr)
      REMUW      : `SAMPLE(remuw_cg, instr)
      LWU        : `SAMPLE(lwu_cg, instr)
      LD         : `SAMPLE(ld_cg, instr)
      SD         : `SAMPLE(sd_cg, instr)
      SLLW       : `SAMPLE(sllw_cg, instr)
      SLLIW      : `SAMPLE(slliw_cg, instr)
      SRLW       : `SAMPLE(srlw_cg, instr)
      SRLIW      : `SAMPLE(srliw_cg, instr)
      SRAW       : `SAMPLE(sraw_cg, instr)
      SRAIW      : `SAMPLE(sraiw_cg, instr)
      ADDW       : `SAMPLE(addw_cg, instr)
      ADDIW      : `SAMPLE(addiw_cg, instr)
      SUBW       : `SAMPLE(subw_cg, instr)
      C_LW       : `SAMPLE(c_lw_cg, instr)
      C_SW       : `SAMPLE(c_sw_cg, instr)
      C_LWSP     : `SAMPLE(c_lwsp_cg, instr)
      C_SWSP     : `SAMPLE(c_swsp_cg, instr)
      C_ADDI4SPN : `SAMPLE(c_addi4spn_cg, instr)
      C_ADDI     : `SAMPLE(c_addi_cg, instr)
      C_ADDI16SP : `SAMPLE(c_addi16sp_cg, instr)
      C_LI       : `SAMPLE(c_li_cg, instr)
      C_LUI      : `SAMPLE(c_lui_cg, instr)
      C_SUB      : `SAMPLE(c_sub_cg, instr)
      C_ADD      : `SAMPLE(c_add_cg, instr)
      C_MV       : `SAMPLE(c_mv_cg, instr)
      C_ANDI     : `SAMPLE(c_andi_cg, instr)
      C_XOR      : `SAMPLE(c_xor_cg, instr)
      C_OR       : `SAMPLE(c_or_cg, instr)
      C_AND      : `SAMPLE(c_and_cg, instr)
      C_BEQZ     : `SAMPLE(c_beqz_cg, instr)
      C_BNEZ     : `SAMPLE(c_bnez_cg, instr)
      C_SRLI     : `SAMPLE(c_srli_cg, instr)
      C_SRAI     : `SAMPLE(c_srai_cg, instr)
      C_SLLI     : `SAMPLE(c_slli_cg, instr)
      C_J        : `SAMPLE(c_j_cg, instr)
      C_JAL      : `SAMPLE(c_jal_cg, instr)
      C_JR       : `SAMPLE(c_jr_cg, instr)
      C_JALR     : `SAMPLE(c_jalr_cg, instr)
      C_LD       : `SAMPLE(c_ld_cg, instr)
      C_SD       : `SAMPLE(c_sd_cg, instr)
      C_LDSP     : `SAMPLE(c_ldsp_cg, instr)
      C_SDSP     : `SAMPLE(c_sdsp_cg, instr)
      C_SUBW     : `SAMPLE(c_subw_cg, instr)
      C_ADDW     : `SAMPLE(c_addw_cg, instr)
      C_ADDIW    : `SAMPLE(c_addiw_cg, instr)
      FLW        : `SAMPLE_F(flw_cg, instr)
      FLD        : `SAMPLE_F(fld_cg, instr)
      FSW        : `SAMPLE_F(fsw_cg, instr)
      FSD        : `SAMPLE_F(fsd_cg, instr)
      FADD_S     : `SAMPLE_F(fadd_s_cg, instr)
      FADD_D     : `SAMPLE_F(fadd_d_cg, instr)
      FSUB_S     : `SAMPLE_F(fsub_s_cg, instr)
      FSUB_D     : `SAMPLE_F(fsub_d_cg, instr)
      FMUL_S     : `SAMPLE_F(fmul_s_cg, instr)
      FMUL_D     : `SAMPLE_F(fmul_d_cg, instr)
      FDIV_S     : `SAMPLE_F(fdiv_s_cg, instr)
      FDIV_D     : `SAMPLE_F(fdiv_d_cg, instr)
      FSQRT_S    : `SAMPLE_F(fsqrt_s_cg, instr)
      FSQRT_D    : `SAMPLE_F(fsqrt_d_cg, instr)
      FMIN_S     : `SAMPLE_F(fmin_s_cg, instr)
      FMIN_D     : `SAMPLE_F(fmin_d_cg, instr)
      FMAX_S     : `SAMPLE_F(fmax_s_cg, instr)
      FMAX_D     : `SAMPLE_F(fmax_d_cg, instr)
      FMADD_S    : `SAMPLE_F(fmadd_s_cg, instr)
      FMADD_D    : `SAMPLE_F(fmadd_d_cg, instr)
      FNMADD_S   : `SAMPLE_F(fnmadd_s_cg, instr)
      FNMADD_D   : `SAMPLE_F(fnmadd_d_cg, instr)
      FMSUB_S    : `SAMPLE_F(fmsub_s_cg, instr)
      FMSUB_D    : `SAMPLE_F(fmsub_d_cg, instr)
      FNMSUB_S   : `SAMPLE_F(fnmsub_s_cg, instr)
      FNMSUB_D   : `SAMPLE_F(fnmsub_d_cg, instr)
      FCVT_W_S   : `SAMPLE_F(fcvt_w_s_cg, instr)
      FCVT_WU_S  : `SAMPLE_F(fcvt_wu_s_cg, instr)
      FCVT_L_S   : `SAMPLE_F(fcvt_l_s_cg, instr)
      FCVT_LU_S  : `SAMPLE_F(fcvt_lu_s_cg, instr)
      FCVT_L_D   : `SAMPLE_F(fcvt_l_d_cg, instr)
      FCVT_LU_D  : `SAMPLE_F(fcvt_lu_d_cg, instr)
      FCVT_S_D   : `SAMPLE_F(fcvt_s_d_cg, instr)
      FCVT_D_S   : `SAMPLE_F(fcvt_d_s_cg, instr)
      FCVT_W_D   : `SAMPLE_F(fcvt_w_d_cg, instr)
      FCVT_WU_D  : `SAMPLE_F(fcvt_wu_d_cg, instr)
      FCVT_S_W   : `SAMPLE_F(fcvt_s_w_cg, instr)
      FCVT_S_WU  : `SAMPLE_F(fcvt_s_wu_cg, instr)
      FCVT_S_L   : `SAMPLE_F(fcvt_s_l_cg, instr)
      FCVT_D_L   : `SAMPLE_F(fcvt_d_l_cg, instr)
      FCVT_S_LU  : `SAMPLE_F(fcvt_s_lu_cg, instr)
      FCVT_D_W   : `SAMPLE_F(fcvt_d_w_cg, instr)
      FCVT_D_LU  : `SAMPLE_F(fcvt_d_lu_cg, instr)
      FCVT_D_WU  : `SAMPLE_F(fcvt_d_wu_cg, instr)
      FSGNJ_S    : `SAMPLE_F(fsgnj_s_cg, instr)
      FSGNJ_D    : `SAMPLE_F(fsgnj_d_cg, instr)
      FSGNJN_S   : `SAMPLE_F(fsgnjn_s_cg, instr)
      FSGNJN_D   : `SAMPLE_F(fsgnjn_d_cg, instr)
      FSGNJX_S   : `SAMPLE_F(fsgnjx_s_cg, instr)
      FSGNJX_D   : `SAMPLE_F(fsgnjx_d_cg, instr)
      FMV_X_W    : `SAMPLE_F(fmv_x_w_cg, instr)
      FMV_X_D    : `SAMPLE_F(fmv_x_d_cg, instr)
      FMV_W_X    : `SAMPLE_F(fmv_w_x_cg, instr)
      FMV_D_X    : `SAMPLE_F(fmv_d_x_cg, instr)
      FEQ_S      : `SAMPLE_F(feq_s_cg, instr)
      FEQ_D      : `SAMPLE_F(feq_d_cg, instr)
      FLT_S      : `SAMPLE_F(flt_s_cg, instr)
      FLT_D      : `SAMPLE_F(flt_d_cg, instr)
      FLE_S      : `SAMPLE_F(fle_s_cg, instr)
      FLE_D      : `SAMPLE_F(fle_d_cg, instr)
      FCLASS_S   : `SAMPLE_F(fclass_s_cg, instr)
      FCLASS_D   : `SAMPLE_F(fclass_d_cg, instr)
      // RV32B
      CLZ        : `SAMPLE_B(clz_cg, instr)
      CTZ        : `SAMPLE_B(ctz_cg, instr)
      PCNT       : `SAMPLE_B(pcnt_cg, instr)
      ANDN       : `SAMPLE_B(andn_cg, instr)
      ORN        : `SAMPLE_B(orn_cg, instr)
      XNOR       : `SAMPLE_B(xnor_cg, instr)
      PACK       : `SAMPLE_B(pack_cg, instr)
      PACKH      : `SAMPLE_B(packh_cg, instr)
      MIN        : `SAMPLE_B(min_cg, instr)
      MAX        : `SAMPLE_B(max_cg, instr)
      MINU       : `SAMPLE_B(minu_cg, instr)
      MAXU       : `SAMPLE_B(maxu_cg, instr)
      SEXT_B     : `SAMPLE_B(sext_b_cg, instr)
      SEXT_H     : `SAMPLE_B(sext_h_cg, instr)
      SBSET      : `SAMPLE_B(sbset_cg, instr)
      SBCLR      : `SAMPLE_B(sbclr_cg, instr)
      SBINV      : `SAMPLE_B(sbinv_cg, instr)
      SBEXT      : `SAMPLE_B(sbext_cg, instr)
      SBSETI     : `SAMPLE_B(sbseti_cg, instr)
      SBCLRI     : `SAMPLE_B(sbclri_cg, instr)
      SBINVI     : `SAMPLE_B(sbinvi_cg, instr)
      SBEXTI     : `SAMPLE_B(sbexti_cg, instr)
      SLO        : `SAMPLE_B(slo_cg, instr)
      SRO        : `SAMPLE_B(sro_cg, instr)
      SLOI       : `SAMPLE_B(sloi_cg, instr)
      SROI       : `SAMPLE_B(sroi_cg, instr)
      ROR        : `SAMPLE_B(ror_cg, instr)
      ROL        : `SAMPLE_B(rol_cg, instr)
      RORI       : `SAMPLE_B(rori_cg, instr)
      GREV       : `SAMPLE_B(grev_cg, instr)
      GREVI      : `SAMPLE_B(grevi_cg, instr)
      SHFLI      : `SAMPLE_B(shfli_cg, instr)
      UNSHFLI    : `SAMPLE_B(unshfli_cg, instr)
      SHFL       : `SAMPLE_B(shfl_cg, instr)
      UNSHFL     : `SAMPLE_B(unshfl_cg, instr)
      GORC       : `SAMPLE_B(gorc_cg, instr)
      GORCI      : `SAMPLE_B(gorci_cg, instr)
      BFP        : `SAMPLE_B(bfp_cg, instr)
      BEXT       : `SAMPLE_B(bext_cg, instr)
      BDEP       : `SAMPLE_B(bdep_cg, instr)
      CLMUL      : `SAMPLE_B(clmul_cg, instr)
      CLMULH     : `SAMPLE_B(clmulh_cg, instr)
      CLMULR     : `SAMPLE_B(clmulr_cg, instr)
      CRC32_B    : `SAMPLE_B(crc32_b_cg, instr)
      CRC32_H    : `SAMPLE_B(crc32_h_cg, instr)
      CRC32_W    : `SAMPLE_B(crc32_w_cg, instr)
      CRC32C_B   : `SAMPLE_B(crc32c_b_cg, instr)
      CRC32C_H   : `SAMPLE_B(crc32c_h_cg, instr)
      CRC32C_W   : `SAMPLE_B(crc32c_w_cg, instr)
      CMIX       : `SAMPLE_B(cmix_cg, instr)
      CMOV       : `SAMPLE_B(cmov_cg, instr)
      FSL        : `SAMPLE_B(fsl_cg, instr)
      FSR        : `SAMPLE_B(fsr_cg, instr)
      FSRI       : `SAMPLE_B(fsri_cg, instr)
      // RV64B
      CLZW       : `SAMPLE_B(clzw_cg, instr)
      CTZW       : `SAMPLE_B(ctzw_cg, instr)
      PCNTW      : `SAMPLE_B(pcntw_cg, instr)
      PACKW      : `SAMPLE_B(packw_cg, instr)
      PACKUW     : `SAMPLE_B(packuw_cg, instr)
      SLOW       : `SAMPLE_B(slow_cg, instr)
      SROW       : `SAMPLE_B(srow_cg, instr)
      SLOIW      : `SAMPLE_B(sloiw_cg, instr)
      SROIW      : `SAMPLE_B(sroiw_cg, instr)
      RORW       : `SAMPLE_B(rorw_cg, instr)
      ROLW       : `SAMPLE_B(rolw_cg, instr)
      RORIW      : `SAMPLE_B(roriw_cg, instr)
      GREVW      : `SAMPLE_B(grevw_cg, instr)
      GREVIW     : `SAMPLE_B(greviw_cg, instr)
      SHFLW      : `SAMPLE_B(shflw_cg, instr)
      UNSHFLW    : `SAMPLE_B(unshflw_cg, instr)
      GORCW      : `SAMPLE_B(gorcw_cg, instr)
      GORCIW     : `SAMPLE_B(gorciw_cg, instr)
      BFPW       : `SAMPLE_B(bfpw_cg, instr)
      BEXTW      : `SAMPLE_B(bextw_cg, instr)
      BDEPW      : `SAMPLE_B(bdepw_cg, instr)
      CLMULW     : `SAMPLE_B(clmulw_cg, instr)
      CLMULHW    : `SAMPLE_B(clmulhw_cg, instr)
      CLMULRW    : `SAMPLE_B(clmulrw_cg, instr)
      CRC32_D    : `SAMPLE_B(crc32_d_cg, instr)
      CRC32C_D   : `SAMPLE_B(crc32c_d_cg, instr)
      BMATOR     : `SAMPLE_B(bmator_cg, instr)
      BMATXOR    : `SAMPLE_B(bmatxor_cg, instr)
      BMATFLIP   : `SAMPLE_B(bmatflip_cg, instr)
      FSLW       : `SAMPLE_B(fslw_cg, instr)
      FSRW       : `SAMPLE_B(fsrw_cg, instr)
      FSRIW      : `SAMPLE_B(fsriw_cg, instr)
      ADDWU      : `SAMPLE_B(addwu_cg, instr)
      SUBWU      : `SAMPLE_B(subwu_cg, instr)
      ADDIWU     : `SAMPLE_B(addiwu_cg, instr)
      ADDU_W     : `SAMPLE_B(addu_w_cg, instr)
      SUBU_W     : `SAMPLE_B(subu_w_cg, instr)
      SLLIU_W    : `SAMPLE_B(slliu_w_cg, instr)
      `VECTOR_INCLUDE("riscv_instr_cover_group_inc_cg_sample.sv")
      default: begin
        if (instr.group == RV32I) begin
          `SAMPLE(rv32i_misc_cg, instr);
        end
      end
    endcase
    if (instr.category == BRANCH) begin
      branch_hit_history = (branch_hit_history << 1) | instr.branch_hit;
      branch_instr_cnt += 1;
      if (branch_instr_cnt >= $bits(branch_hit_history)) begin
        if (!compliance_mode) begin
          branch_hit_history_cg.sample();
        end
      end
    end
    if (instr.category == CSR) begin
      `SAMPLE(privileged_csr_cg, instr.csr);
      case (instr.csr)
        MCAUSE: begin
          if (instr.rd_value[XLEN-1]) begin
            interrupt_cause_t interrupt;
            if ($cast(interrupt, instr.rd_value[3:0])) begin
              `SAMPLE(mcause_interrupt_cg, interrupt);
            end
          end else begin
            exception_cause_t exception;
            if ($cast(exception, instr.rd_value[3:0])) begin
              `SAMPLE(mcause_exception_cg, exception);
            end
          end
        end
        MEPC: begin
          `SAMPLE(mepc_alignment_cg, instr.rd_value);
        end
        MSTATUS: begin
          `SAMPLE(mstatus_m_cg, instr.rd_value);
        end
        FCSR: begin
          `SAMPLE(fcsr_cg, instr.rd_value);
        end
      endcase
    end
    if (instr_cnt > 1) begin
      if (!compliance_mode) begin
        //instr_trans_cg.sample();
      end
    end
   `VECTOR_INCLUDE("riscv_instr_cover_group_inc_sample.sv")
    pre_instr = instr;
  endfunction

  // Check if the instruction is supported
  virtual function bit is_supported_instr(riscv_instr_name_t name);
    if (name inside {instr_list}) begin
      return 1'b1;
    end else begin
      return 1'b0;
    end
  endfunction

  // Check if the instruction is supported
  virtual function bit is_compressed_gpr(riscv_reg_t gpr);
    if (gpr inside {[S0:A5]}) begin
      return 1'b1;
    end else begin
      return 1'b0;
    end
  endfunction

  // Build the supported instruction list based on the core setting
  virtual function void build_instr_list();
    riscv_instr_name_t instr_name;
    instr_name = instr_name.first;
    do begin
      riscv_instr instr;
      if (!(instr_name inside {unsupported_instr}) && (instr_name != INVALID_INSTR) &&
          riscv_instr::instr_registry.exists(instr_name)) begin
        instr = riscv_instr::create_instr(instr_name);
        if ((instr.group inside {supported_isa}) &&
            (instr.group inside {RV32I, RV32M, RV64M, RV64I, RV32C, RV64C,
                                 RVV, RV64B, RV32B})) begin
          if (((instr_name inside {URET}) && !support_umode_trap) ||
              ((instr_name inside {SRET, SFENCE_VMA}) &&
              !(SUPERVISOR_MODE inside {supported_privileged_mode})) ||
              ((instr_name inside {DRET}) && !support_debug_mode)) begin
            instr_name = instr_name.next;
            continue;
          end
          `uvm_info("riscv_instr_cover_group", $sformatf("Adding [%s] %s to the list",
                    instr.group.name(), instr.instr_name.name()), UVM_HIGH)
          instr_list.push_back(instr_name);
        end
      end
      instr_name = instr_name.next;
    end
    while (instr_name != instr_name.first);
  endfunction

  function void reset();
    instr_cnt = 0;
    branch_instr_cnt = 0;
    branch_hit_history = '0;
    `VECTOR_INCLUDE("riscv_instr_cover_group_inc_cpu_reset.sv")
  endfunction

  function void fatal(string str);
    if ($test$plusargs("stop_on_first_error")) begin
      `uvm_fatal("riscv_instr_cover_group", $sformatf("FATAL Error: %0s", str))
    end
  endfunction

endclass
