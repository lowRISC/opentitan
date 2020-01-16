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

`define INSTR_CG_BEGIN(INSTR_NAME) \
  covergroup ``INSTR_NAME``_cg with function sample(riscv_instr_cov_item instr);

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

`define CG_END endgroup

`define CG_SELECTOR_BEGIN(CG_ISA) \
    if ((CG_ISA inside {supported_isa}) && (!select_isa || (cov_isa == CG_ISA))) begin

`define CG_SELECTOR_END \
    end

class riscv_instr_cover_group;

  riscv_instr_gen_config  cfg;
  riscv_instr_cov_item    cur_instr;
  riscv_instr_cov_item    pre_instr;
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

  covergroup rv32i_misc_cg with function sample(riscv_instr_cov_item instr);
    cp_misc : coverpoint instr.instr_name {
      bins instr[] = {FENCE, FENCE_I, EBREAK, ECALL, MRET};
    }
  endgroup

  covergroup wfi_cg with function sample(riscv_instr_cov_item instr);
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
      ignore_bins no_overflow = {riscv_instr_cov_item::DIV_OVERFLOW};
    }
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(rem)
    cp_div_result: coverpoint instr.div_result;
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(remu)
    cp_div_result: coverpoint instr.div_result {
      ignore_bins no_overflow = {riscv_instr_cov_item::DIV_OVERFLOW};
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
      ignore_bins no_overflow = {riscv_instr_cov_item::DIV_OVERFLOW};
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
      ignore_bins no_overflow = {riscv_instr_cov_item::DIV_OVERFLOW};
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

  `VECTOR_INCLUDE("riscv_instr_cover_group_inc_cg_add.sv")

  function new(riscv_instr_gen_config cfg);
    string opts;
    this.cfg = cfg;
    cur_instr = riscv_instr_cov_item::type_id::create("cur_instr");
    pre_instr = riscv_instr_cov_item::type_id::create("pre_instr");
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
      end
      if (!cfg.disable_compressed_instr) begin
        mepc_alignment_cg = new();
      end
    end
  endfunction

  function void sample(riscv_instr_cov_item instr);
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
      endcase
    end
    if (instr_cnt > 1) begin
      if (!compliance_mode) begin
        //instr_trans_cg.sample();
      end
    end
   `VECTOR_INCLUDE("riscv_instr_cover_group_inc_sample.sv")
    pre_instr.copy(instr);
    pre_instr.mem_addr = instr.mem_addr;
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
      `INSTR instr;
      if (!(instr_name inside {unsupported_instr}) && (instr_name != INVALID_INSTR)) begin
        `ifdef DEPRECATED
          instr = riscv_instr_base::type_id::create("instr");
          if (!instr.randomize() with {instr_name == local::instr_name;}) begin
            `uvm_fatal("riscv_instr_cover_group",
                       $sformatf("Instruction %0s randomization failure", instr_name.name()))
          end
        `else
          instr = riscv_instr::create_instr(instr_name);
        `endif
        if ((instr.group inside {supported_isa}) &&
            (instr.group inside {RV32I, RV32M, RV64M, RV64I, RV32C, RV64C,
                                 RV32V, RV64V, RV64B, RV32B})) begin
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
