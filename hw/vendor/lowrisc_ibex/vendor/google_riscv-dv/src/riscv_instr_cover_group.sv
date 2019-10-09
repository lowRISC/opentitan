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
    cp_gpr_harzard : coverpoint instr.gpr_hazard; \

`define CMP_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rs1         : coverpoint instr.rs1; \
    cp_rd          : coverpoint instr.rd;  \
    cp_rs1_sign    : coverpoint instr.rs1_sign; \
    cp_result      : coverpoint instr.rd_value[0]; \
    cp_gpr_harzard : coverpoint instr.gpr_hazard; \

`define SB_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rs1         : coverpoint instr.rs1; \
    cp_rs2         : coverpoint instr.rs2; \
    cp_rs1_sign    : coverpoint instr.rs1_sign; \
    cp_rs2_sign    : coverpoint instr.rs2_sign; \
    cp_imm_sign    : coverpoint instr.imm_sign; \
    cp_branch_hit  : coverpoint instr.branch_hit; \
    cp_sign_cross  : cross cp_rs1_sign, cp_rs2_sign, cp_imm_sign; \
    cp_gpr_harzard : coverpoint instr.gpr_hazard { \
      bins valid_hazard[] = {NO_HAZARD, RAW_HAZARD}; \
    }

`define STORE_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rs1         : coverpoint instr.rs1; \
    cp_rs2         : coverpoint instr.rs2; \
    cp_imm_sign    : coverpoint instr.imm_sign; \
    cp_gpr_harzard : coverpoint instr.gpr_hazard { \
      bins valid_hazard[] = {NO_HAZARD, RAW_HAZARD}; \
    } \
    cp_lsu_harzard : coverpoint instr.lsu_hazard { \
      bins valid_hazard[] = {NO_HAZARD, WAR_HAZARD, WAW_HAZARD}; \
    }

`define LOAD_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rs1         : coverpoint instr.rs1; \
    cp_rd          : coverpoint instr.rd; \
    cp_imm_sign    : coverpoint instr.imm_sign; \
    cp_gpr_harzard : coverpoint instr.gpr_hazard; \
    cp_lsu_harzard : coverpoint instr.lsu_hazard { \
      bins valid_hazard[] = {NO_HAZARD, RAW_HAZARD}; \
    }

`define I_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rs1         : coverpoint instr.rs1; \
    cp_rd          : coverpoint instr.rd; \
    cp_rs1_sign    : coverpoint instr.rs1_sign; \
    cp_rd_sign     : coverpoint instr.rd_sign; \
    cp_imm_sign    : coverpoint instr.imm_sign; \
    cp_gpr_harzard : coverpoint instr.gpr_hazard;

`define U_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rd          : coverpoint instr.rd; \
    cp_rd_sign     : coverpoint instr.rd_sign; \
    cp_imm_sign    : coverpoint instr.imm_sign; \
    cp_gpr_harzard : coverpoint instr.gpr_hazard;


`define J_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_imm_sign    : coverpoint instr.imm_sign; \
    cp_imm_lsb     : coverpoint instr.imm[1:0]; \
    cp_rd          : coverpoint instr.rd; \


`define CSR_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rs1         : coverpoint instr.rs1; \
    cp_rd          : coverpoint instr.rd; \
    cp_gpr_harzard : coverpoint instr.gpr_hazard;

`define CR_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rs2         : coverpoint instr.rs2; \
    cp_rd          : coverpoint instr.rd; \
    cp_rs2_sign    : coverpoint instr.rs2_sign; \
    cp_gpr_harzard : coverpoint instr.gpr_hazard;

`define CI_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rd       : coverpoint instr.rd; \
    cp_imm_sign : coverpoint instr.imm_sign; \
    cp_gpr_harzard : coverpoint instr.gpr_hazard { \
      bins valid_hazard[] = {NO_HAZARD, WAR_HAZARD, WAW_HAZARD}; \
    }

`define CSS_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_rs2      : coverpoint instr.rs2; \
    cp_imm_sign : coverpoint instr.imm_sign; \
    cp_rs2_sign : coverpoint instr.rs2_sign; \
    cp_gpr_harzard : coverpoint instr.gpr_hazard { \
      bins valid_hazard[] = {NO_HAZARD, RAW_HAZARD}; \
    }

`define CIW_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_imm_sign : coverpoint instr.imm_sign; \
    cp_rd       : coverpoint instr.rd { \
      bins gpr[] = cp_rd with (is_compressed_gpr(riscv_reg_t'(item))); \
    } \
    cp_gpr_harzard : coverpoint instr.gpr_hazard { \
      bins valid_hazard[] = {NO_HAZARD, WAR_HAZARD, WAW_HAZARD}; \
    }

`define CL_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_imm_sign : coverpoint instr.imm_sign; \
    cp_rs1      : coverpoint instr.rs1 { \
      bins gpr[] = cp_rs1 with (is_compressed_gpr(riscv_reg_t'(item))); \
    } \
    cp_rd       : coverpoint instr.rd { \
      bins gpr[] = cp_rd with (is_compressed_gpr(riscv_reg_t'(item))); \
    } \
    cp_gpr_harzard : coverpoint instr.gpr_hazard; \
    cp_lsu_harzard : coverpoint instr.lsu_hazard { \
      bins valid_hazard[] = {NO_HAZARD, RAW_HAZARD}; \
    }

`define CS_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_imm_sign : coverpoint instr.imm_sign; \
    cp_rs1      : coverpoint instr.rs1 { \
      bins gpr[] = cp_rs1 with (is_compressed_gpr(riscv_reg_t'(item))); \
    } \
    cp_rs2      : coverpoint instr.rs2 { \
      bins gpr[] = cp_rs2 with (is_compressed_gpr(riscv_reg_t'(item))); \
    } \
    cp_gpr_harzard : coverpoint instr.gpr_hazard { \
      bins valid_hazard[] = {NO_HAZARD, RAW_HAZARD}; \
    } \
    cp_lsu_harzard : coverpoint instr.lsu_hazard { \
      bins valid_hazard[] = {NO_HAZARD, WAR_HAZARD, WAW_HAZARD}; \
    }


`define CB_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_imm_sign : coverpoint instr.imm_sign; \
    cp_rs1      : coverpoint instr.rs1 { \
      bins gpr[] = cp_rs1 with (is_compressed_gpr(riscv_reg_t'(item))); \
    } \
    cp_gpr_harzard : coverpoint instr.gpr_hazard { \
      bins valid_hazard[] = {NO_HAZARD, RAW_HAZARD}; \
    }

`define CJ_INSTR_CG_BEGIN(INSTR_NAME) \
  `INSTR_CG_BEGIN(INSTR_NAME) \
    cp_imm_sign : coverpoint instr.imm_sign;

`define CG_END endgroup

class riscv_instr_cover_group;

  riscv_instr_gen_config  cfg;
  riscv_instr_cov_item    cur_instr;
  riscv_instr_cov_item    pre_instr;
  riscv_instr_name_t      instr_list[$];
  int unsigned            instr_cnt;
  int unsigned            branch_instr_cnt;
  bit [4:0]               branch_hit_history; // The last 5 branch result

  ///////////// RV32I instruction functional coverage //////////////

  // Arithmetic instructions
  `R_INSTR_CG_BEGIN(add)
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign, cp_rd_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(sub)
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign, cp_rd_sign;
  `CG_END

  `I_INSTR_CG_BEGIN(addi)
    cp_sign_cross: cross cp_rs1_sign, cp_imm_sign, cp_rd_sign;
  `CG_END

  `U_INSTR_CG_BEGIN(lui)
    cp_sign_cross: cross cp_imm_sign, cp_rd_sign;
  `CG_END

  `U_INSTR_CG_BEGIN(auipc)
    cp_sign_cross: cross cp_imm_sign, cp_rd_sign;
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
    cp_gpr_harzard : coverpoint instr.gpr_hazard;
  `CG_END

  `INSTR_CG_BEGIN(slli)
    cp_rs1         : coverpoint instr.rs1;
    cp_rd          : coverpoint instr.rd;
    cp_rs1_sign    : coverpoint instr.rs1_sign;
    cp_rd_sign     : coverpoint instr.rd_sign;
    cp_gpr_harzard : coverpoint instr.gpr_hazard;
  `CG_END

  `INSTR_CG_BEGIN(srli)
    cp_rs1         : coverpoint instr.rs1;
    cp_rd          : coverpoint instr.rd;
    cp_rs1_sign    : coverpoint instr.rs1_sign;
    cp_rd_sign     : coverpoint instr.rd_sign;
    cp_gpr_harzard : coverpoint instr.gpr_hazard;
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
  `CG_END

  `J_INSTR_CG_BEGIN(jalr)
    cp_rs1_eq_rd : coverpoint instr.rs1 iff (instr.rs1 == instr.rd);
    cp_rs1_ne_rd : coverpoint instr.rs1 iff (instr.rs1 != instr.rd);
  `CG_END

  // CSR instructions
  `CSR_INSTR_CG_BEGIN(csrrw)
    cp_rs2 : coverpoint instr.rs1;
  `CG_END

  `CSR_INSTR_CG_BEGIN(csrrs)
    cp_rs2 : coverpoint instr.rs1;
  `CG_END

  `CSR_INSTR_CG_BEGIN(csrrc)
    cp_rs2 : coverpoint instr.rs1;
  `CG_END

  `CSR_INSTR_CG_BEGIN(csrrwi)
    cp_imm_sign : coverpoint instr.imm_sign;
  `CG_END

  `CSR_INSTR_CG_BEGIN(csrrsi)
    cp_imm_sign : coverpoint instr.imm_sign;
  `CG_END

  `CSR_INSTR_CG_BEGIN(csrrci)
    cp_imm_sign : coverpoint instr.imm_sign;
  `CG_END

  covergroup rv32i_misc_cg with function sample(riscv_instr_cov_item instr);
    cp_misc : coverpoint instr.instr_name {
      bins instr[] = {FENCE, FENCE_I, EBREAK, ECALL, MRET, WFI};
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
    cp_div_result: coverpoint instr.div_result;
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(rem)
    cp_div_result: coverpoint instr.div_result;
    cp_sign_cross: cross cp_rs1_sign, cp_rs2_sign;
  `CG_END

  `R_INSTR_CG_BEGIN(remu)
    cp_div_result: coverpoint instr.div_result;
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
    cp_div_result: coverpoint instr.div_result;
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
    cp_div_result: coverpoint instr.div_result;
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
    cp_gpr_harzard : coverpoint instr.gpr_hazard;
  `CG_END

  `INSTR_CG_BEGIN(slliw)
    cp_rs1         : coverpoint instr.rs1;
    cp_rd          : coverpoint instr.rd;
    cp_rs1_sign    : coverpoint instr.rs1_sign;
    cp_rd_sign     : coverpoint instr.rd_sign;
    cp_gpr_harzard : coverpoint instr.gpr_hazard;
  `CG_END

  `INSTR_CG_BEGIN(srliw)
    cp_rs1         : coverpoint instr.rs1;
    cp_rd          : coverpoint instr.rd;
    cp_rs1_sign    : coverpoint instr.rs1_sign;
    cp_rd_sign     : coverpoint instr.rd_sign;
    cp_gpr_harzard : coverpoint instr.gpr_hazard;
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

  `CL_INSTR_CG_BEGIN(c_lwsp)
  `CG_END

  `CS_INSTR_CG_BEGIN(c_sw)
  `CG_END

  `CS_INSTR_CG_BEGIN(c_swsp)
  `CG_END

  `CIW_INSTR_CG_BEGIN(c_addi4spn)
  `CG_END

  `CI_INSTR_CG_BEGIN(c_addi)
  `CG_END

  `CI_INSTR_CG_BEGIN(c_addi16sp)
  `CG_END

  `CI_INSTR_CG_BEGIN(c_li)
  `CG_END

  `CI_INSTR_CG_BEGIN(c_lui)
  `CG_END

  `CS_INSTR_CG_BEGIN(c_sub)
  `CG_END

  `CR_INSTR_CG_BEGIN(c_add)
  `CG_END

  `CR_INSTR_CG_BEGIN(c_mv)
  `CG_END

  `CB_INSTR_CG_BEGIN(c_andi)
  `CG_END

  `CS_INSTR_CG_BEGIN(c_xor)
  `CG_END

  `CS_INSTR_CG_BEGIN(c_or)
  `CG_END

  `CS_INSTR_CG_BEGIN(c_and)
  `CG_END

  `CB_INSTR_CG_BEGIN(c_beqz)
  `CG_END

  `CB_INSTR_CG_BEGIN(c_bnez)
  `CG_END

  `INSTR_CG_BEGIN(c_srli)
    cp_rs1      : coverpoint instr.rs1 {
      bins gpr[] = cp_rs1 with (is_compressed_gpr(riscv_reg_t'(item)));
    }
    cp_gpr_harzard : coverpoint instr.gpr_hazard {
      bins valid_hazard[] = {NO_HAZARD, RAW_HAZARD};
    }
  `CG_END

  `INSTR_CG_BEGIN(c_srai)
    cp_rs1      : coverpoint instr.rs1 {
      bins gpr[] = cp_rs1 with (is_compressed_gpr(riscv_reg_t'(item)));
    }
    cp_gpr_harzard : coverpoint instr.gpr_hazard {
      bins valid_hazard[] = {NO_HAZARD, RAW_HAZARD};
    }
  `CG_END

  `INSTR_CG_BEGIN(c_slli)
    cp_rs1      : coverpoint instr.rs1 {
      bins gpr[] = cp_rs1 with (is_compressed_gpr(riscv_reg_t'(item)));
    }
    cp_gpr_harzard : coverpoint instr.gpr_hazard {
      bins valid_hazard[] = {NO_HAZARD, RAW_HAZARD};
    }
  `CG_END

  `CJ_INSTR_CG_BEGIN(c_j)
  `CG_END

  `CJ_INSTR_CG_BEGIN(c_jal)
  `CG_END

  `CR_INSTR_CG_BEGIN(c_jr)
  `CG_END

  `CR_INSTR_CG_BEGIN(c_jalr)
  `CG_END

  // RV64C

  `CL_INSTR_CG_BEGIN(c_ld)
  `CG_END

  `CL_INSTR_CG_BEGIN(c_ldsp)
  `CG_END

  `CS_INSTR_CG_BEGIN(c_sd)
  `CG_END

  `CS_INSTR_CG_BEGIN(c_sdsp)
  `CG_END

  `CI_INSTR_CG_BEGIN(c_addiw)
  `CG_END

  `CS_INSTR_CG_BEGIN(c_subw)
  `CG_END

  `CR_INSTR_CG_BEGIN(c_addw)
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

  // Cover all illegal instruction
  covergroup illegal_cg with function sample(bit [31:0] binary);
    cp_point : coverpoint binary {
      wildcard bins c_addi4spn = {32'bxxxx_xxxxx_0000_0000_000x_xx00};
      wildcard bins c_addiw    = {32'bxxxx_xxxxx_001x_0000_0xxx_xx01};
      wildcard bins c_addi16sp = {32'bxxxx_xxxxx_0110_0001_0000_0001};
      wildcard bins c_lui      = {32'bxxxx_xxxxx_0110_xxxx_1000_0001,
                                  32'bxxxx_xxxxx_0110_xx1x_x000_0001,
                                  32'bxxxx_xxxxx_0110_x1xx_x000_0001,
                                  32'bxxxx_xxxxx_0110_1xxx_x000_0001};
      wildcard bins c_jr       = {32'bxxxx_xxxxx_1000_0000_0000_0001};
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
       bins exception[] = cp_exception with (item inside {implemented_exception});
    }
  endgroup

  covergroup mcause_interrupt_cg with function sample(interrupt_cause_t interrupt);
    cp_interrupt: coverpoint interrupt {
       bins interrupt[] = cp_interrupt with (item inside {implemented_interrupt});
    }
  endgroup

  covergroup mepc_cg with function sample(bit [XLEN-1:0] val);
    cp_align: coverpoint val[1:0] {
      bins alignment[] = {2'b00, 2'b10};
    }
  endgroup

  covergroup mstatus_m_cg with function sample(bit [XLEN-1:0] val);
    cp_mie  : coverpoint val[3];
    cp_mpie : coverpoint val[7];
    cp_mpp  : coverpoint val[12:11];
  endgroup

  function new(riscv_instr_gen_config cfg);
    this.cfg = cfg;
    cur_instr = riscv_instr_cov_item::type_id::create("cur_instr");
    pre_instr = riscv_instr_cov_item::type_id::create("pre_instr");
    build_instr_list();
    hint_cg = new();
    // RV32I instruction functional coverage instantiation
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
    csrrw_cg = new();
    csrrs_cg = new();
    csrrc_cg = new();
    csrrwi_cg = new();
    csrrsi_cg = new();
    csrrci_cg = new();
    // instr_trans_cg = new();
    branch_hit_history_cg = new();
    rv32i_misc_cg = new();
    illegal_cg = new();
    opcode_cg = new();
    compressed_opcode_cg = new();
    if (RV32M inside {supported_isa}) begin
      mul_cg = new();
      mulh_cg = new();
      mulhsu_cg = new();
      mulhu_cg = new();
      div_cg = new();
      divu_cg = new();
      rem_cg = new();
    end
    if (RV64M inside {supported_isa}) begin
      mulw_cg = new();
      divw_cg = new();
      divuw_cg = new();
      remw_cg = new();
      remuw_cg = new();
    end
    if (RV64I inside {supported_isa}) begin
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
    end
    if (RV32C inside {supported_isa}) begin
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
      c_jal_cg = new();
      c_jr_cg = new();
      c_jalr_cg = new();
    end
    if (RV64C inside {supported_isa}) begin
      c_ld_cg = new();
      c_sd_cg = new();
      c_ldsp_cg = new();
      c_sdsp_cg = new();
      c_addiw_cg = new();
      c_subw_cg = new();
      c_addw_cg = new();
    end
    privileged_csr_cg = new();
    mcause_exception_cg = new();
    mcause_interrupt_cg = new();
    mepc_cg = new();
    mstatus_m_cg = new();
  endfunction

  function void sample(riscv_instr_cov_item instr);
    instr_cnt += 1;
    if (instr_cnt > 1) begin
      instr.check_hazard_condition(pre_instr);
    end
    if (instr.binary[1:0] != 2'b11) begin
      hint_cg.sample(instr);
      compressed_opcode_cg.sample(instr.binary[15:0]);
    end else begin
      opcode_cg.sample(instr.binary[6:2]);
    end
    case (instr.instr_name)
      ADD        : add_cg.sample(instr);
      SUB        : sub_cg.sample(instr);
      ADDI       : addi_cg.sample(instr);
      LUI        : lui_cg.sample(instr);
      AUIPC      : auipc_cg.sample(instr);
      SLL        : sll_cg.sample(instr);
      SRL        : srl_cg.sample(instr);
      SRA        : sra_cg.sample(instr);
      SLLI       : begin
                     slli_cg.sample(instr);
                     if (RV64I inside {supported_isa}) begin
                       slli64_cg.sample(instr);
                     end
                   end
      SRLI       : begin
                     srli_cg.sample(instr);
                     if (RV64I inside {supported_isa}) begin
                       srli64_cg.sample(instr);
                     end
                   end
      SRAI       : begin
                     slli_cg.sample(instr);
                     if (RV64I inside {supported_isa}) begin
                       slli64_cg.sample(instr);
                     end
                   end
      SRLI       : srli_cg.sample(instr);
      SRAI       : srai_cg.sample(instr);
      AND        : and_cg.sample(instr);
      OR         : or_cg.sample(instr);
      XOR        : xor_cg.sample(instr);
      ANDI       : andi_cg.sample(instr);
      ORI        : ori_cg.sample(instr);
      XORI       : xori_cg.sample(instr);
      SLT        : slt_cg.sample(instr);
      SLTU       : sltu_cg.sample(instr);
      SLTI       : slti_cg.sample(instr);
      SLTIU      : sltiu_cg.sample(instr);
      JAL        : jal_cg.sample(instr);
      JALR       : jalr_cg.sample(instr);
      BEQ        : beq_cg.sample(instr);
      BNE        : bne_cg.sample(instr);
      BLT        : blt_cg.sample(instr);
      BGE        : bge_cg.sample(instr);
      BLTU       : bltu_cg.sample(instr);
      BGEU       : bgeu_cg.sample(instr);
      LW         : lw_cg.sample(instr);
      LH         : lh_cg.sample(instr);
      LB         : lb_cg.sample(instr);
      LBU        : lbu_cg.sample(instr);
      LHU        : lhu_cg.sample(instr);
      SW         : sw_cg.sample(instr);
      SH         : sh_cg.sample(instr);
      SB         : sb_cg.sample(instr);
      CSRRW      : csrrw_cg.sample(instr);
      CSRRS      : csrrs_cg.sample(instr);
      CSRRC      : csrrc_cg.sample(instr);
      CSRRWI     : csrrwi_cg.sample(instr);
      CSRRSI     : csrrsi_cg.sample(instr);
      CSRRCI     : csrrci_cg.sample(instr);
      MUL        : mul_cg.sample(instr);
      MULH       : mulh_cg.sample(instr);
      MULHSU     : mulhsu_cg.sample(instr);
      MULHU      : mulhu_cg.sample(instr);
      DIV        : div_cg.sample(instr);
      DIVU       : divu_cg.sample(instr);
      REM        : rem_cg.sample(instr);
      MULW       : mulw_cg.sample(instr);
      DIVW       : divw_cg.sample(instr);
      DIVUW      : divuw_cg.sample(instr);
      REMW       : remw_cg.sample(instr);
      REMUW      : remuw_cg.sample(instr);
      LWU        : lwu_cg.sample(instr);
      LD         : ld_cg.sample(instr);
      SD         : sd_cg.sample(instr);
      SLLW       : sllw_cg.sample(instr);
      SLLIW      : slliw_cg.sample(instr);
      SRLW       : srlw_cg.sample(instr);
      SRLIW      : srliw_cg.sample(instr);
      SRAW       : sraw_cg.sample(instr);
      SRAIW      : sraiw_cg.sample(instr);
      ADDW       : addw_cg.sample(instr);
      ADDIW      : addiw_cg.sample(instr);
      SUBW       : subw_cg.sample(instr);
      C_LW       : c_lw_cg.sample(instr);
      C_SW       : c_sw_cg.sample(instr);
      C_LWSP     : c_lwsp_cg.sample(instr);
      C_SWSP     : c_swsp_cg.sample(instr);
      C_ADDI4SPN : c_addi4spn_cg.sample(instr);
      C_ADDI     : c_addi_cg.sample(instr);
      C_ADDI16SP : c_addi16sp_cg.sample(instr);
      C_LI       : c_li_cg.sample(instr);
      C_LUI      : c_lui_cg.sample(instr);
      C_SUB      : c_sub_cg.sample(instr);
      C_ADD      : c_add_cg.sample(instr);
      C_MV       : c_mv_cg.sample(instr);
      C_ANDI     : c_andi_cg.sample(instr);
      C_XOR      : c_xor_cg.sample(instr);
      C_OR       : c_or_cg.sample(instr);
      C_AND      : c_and_cg.sample(instr);
      C_BEQZ     : c_beqz_cg.sample(instr);
      C_BNEZ     : c_bnez_cg.sample(instr);
      C_SRLI     : c_srli_cg.sample(instr);
      C_SRAI     : c_srai_cg.sample(instr);
      C_SLLI     : c_slli_cg.sample(instr);
      C_J        : c_j_cg.sample(instr);
      C_JAL      : c_jal_cg.sample(instr);
      C_JR       : c_jr_cg.sample(instr);
      C_JALR     : c_jalr_cg.sample(instr);
      C_LD       : c_ld_cg.sample(instr);
      C_SD       : c_sd_cg.sample(instr);
      C_LDSP     : c_ldsp_cg.sample(instr);
      C_SDSP     : c_sdsp_cg.sample(instr);
      C_SUBW     : c_subw_cg.sample(instr);
      C_ADDW     : c_addw_cg.sample(instr);
      C_ADDIW    : c_addiw_cg.sample(instr);
      default: begin
        illegal_cg.sample(instr.binary);
        if (instr.group == RV32I) begin
          rv32i_misc_cg.sample(instr);
        end
      end
    endcase
    if (instr.category == BRANCH) begin
      branch_hit_history = (branch_hit_history << 1) | instr.branch_hit;
      branch_instr_cnt += 1;
      if (branch_instr_cnt >= $bits(branch_hit_history)) begin
        branch_hit_history_cg.sample();
      end
    end
    if (instr.category == CSR) begin
      privileged_csr_cg.sample(instr.csr);
      case (instr.csr)
        MCAUSE: begin
          if (instr.rd_value[XLEN-1]) begin
            interrupt_cause_t interrupt;
            if ($cast(interrupt, instr.rd_value[3:0])) begin
              mcause_interrupt_cg.sample(interrupt);
            end
          end else begin
            exception_cause_t exception;
            if ($cast(exception, instr.rd_value[3:0])) begin
              mcause_exception_cg.sample(exception);
            end
          end
        end
        MEPC: mepc_cg.sample(instr.rd_value);
        MSTATUS: begin
          mstatus_m_cg.sample(instr.rd_value);
        end
      endcase
    end
    if (instr_cnt > 1) begin
      // instr_trans_cg.sample();
    end
    pre_instr.copy_base_instr(instr);
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
      riscv_instr_base instr;
      if (!(instr_name inside {unsupported_instr}) && (instr_name != INVALID_INSTR)) begin
        instr = riscv_instr_base::type_id::create("instr");
        if (!instr.randomize() with {instr_name == local::instr_name;}) begin
          `uvm_fatal("riscv_instr_cover_group",
                     $sformatf("Instruction %0s randomization failure", instr_name.name()))
        end
        if ((instr.group inside {supported_isa}) &&
            (instr.group inside {RV32I, RV32M, RV64M, RV64I, RV32C, RV64C})) begin
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
  endfunction

endclass
