/*
 * Copyright 2018 Google LLC
 * Copyright 2020 Andes Technology Co., Ltd.
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


package riscv_instr_pkg;

  `include "dv_defines.svh"
  `include "riscv_defines.svh"
  `include "uvm_macros.svh"

  import uvm_pkg::*;
  import riscv_signature_pkg::*;

  `define include_file(f) `include `"f`"

  uvm_cmdline_processor  inst;

  // Data section setting
  typedef struct {
    string         name;
    int unsigned   size_in_bytes;
    bit [2:0]      xwr; // Excutable,Writable,Readale
  } mem_region_t;

  // Initialization of the vregs
  typedef enum {
    SAME_VALUES_ALL_ELEMS,
    RANDOM_VALUES_VMV,
    RANDOM_VALUES_LOAD
  } vreg_init_method_t;

  typedef enum bit [3:0] {
    BARE = 4'b0000,
    SV32 = 4'b0001,
    SV39 = 4'b1000,
    SV48 = 4'b1001,
    SV57 = 4'b1010,
    SV64 = 4'b1011
  } satp_mode_t;

  typedef enum bit [2:0] {
    RNE = 3'b000,
    RTZ = 3'b001,
    RDN = 3'b010,
    RUP = 3'b011,
    RMM = 3'b100
  } f_rounding_mode_t;

  typedef enum bit [1:0] {
    DIRECT   = 2'b00,
    VECTORED = 2'b01
  } mtvec_mode_t;

  typedef enum bit [2:0] {
    IMM,    // Signed immediate
    UIMM,   // Unsigned immediate
    NZUIMM, // Non-zero unsigned immediate
    NZIMM   // Non-zero signed immediate
  } imm_t;

  // Privileged mode
  typedef enum bit [1:0] {
    USER_MODE       = 2'b00,
    SUPERVISOR_MODE = 2'b01,
    RESERVED_MODE   = 2'b10,
    MACHINE_MODE    = 2'b11
  } privileged_mode_t;

  typedef enum bit [4:0] {
    RV32I,
    RV64I,
    RV32M,
    RV64M,
    RV32A,
    RV64A,
    RV32F,
    RV32FC,
    RV64F,
    RV32D,
    RV32DC,
    RV64D,
    RV32C,
    RV64C,
    RV128I,
    RV128C,
    RVV,
    RV32B,
    RV64B,
    RV32X,
    RV64X
  } riscv_instr_group_t;

  typedef enum {
    // RV32I instructions
    LUI,
    AUIPC,
    JAL,
    JALR,
    BEQ,
    BNE,
    BLT,
    BGE,
    BLTU,
    BGEU,
    LB,
    LH,
    LW,
    LBU,
    LHU,
    SB,
    SH,
    SW,
    ADDI,
    SLTI,
    SLTIU,
    XORI,
    ORI,
    ANDI,
    SLLI,
    SRLI,
    SRAI,
    ADD,
    SUB,
    SLL,
    SLT,
    SLTU,
    XOR,
    SRL,
    SRA,
    OR,
    AND,
    NOP,
    FENCE,
    FENCE_I,
    ECALL,
    EBREAK,
    CSRRW,
    CSRRS,
    CSRRC,
    CSRRWI,
    CSRRSI,
    CSRRCI,
    // RV32B instructions
    ANDN,
    ORN,
    XNOR,
    GORC,
    SLO,
    SRO,
    ROL,
    ROR,
    SBCLR,
    SBSET,
    SBINV,
    SBEXT,
    GREV,
    SLOI,
    SROI,
    RORI,
    SBCLRI,
    SBSETI,
    SBINVI,
    SBEXTI,
    GORCI,
    GREVI,
    CMIX,
    CMOV,
    FSL,
    FSR,
    FSRI,
    CLZ,
    CTZ,
    PCNT,
    SEXT_B,
    SEXT_H,
    CRC32_B,
    CRC32_H,
    CRC32_W,
    CRC32C_B,
    CRC32C_H,
    CRC32C_W,
    CLMUL,
    CLMULR,
    CLMULH,
    MIN,
    MAX,
    MINU,
    MAXU,
    SHFL,
    UNSHFL,
    BDEP,
    BEXT,
    PACK,
    PACKU,
    BMATOR,
    BMATXOR,
    PACKH,
    BFP,
    SHFLI,
    UNSHFLI,
    //RV64B instructions
    ADDIWU,
    SLLIU_W,
    ADDWU,
    SUBWU,
    BMATFLIP,
    CRC32_D,
    CRC32C_D,
    ADDU_W,
    SUBU_W,
    SLOW,
    SROW,
    ROLW,
    RORW,
    SBCLRW,
    SBSETW,
    SBINVW,
    SBEXTW,
    GORCW,
    GREVW,
    SLOIW,
    SROIW,
    RORIW,
    SBCLRIW,
    SBSETIW,
    SBINVIW,
    GORCIW,
    GREVIW,
    FSLW,
    FSRW,
    FSRIW,
    CLZW,
    CTZW,
    PCNTW,
    CLMULW,
    CLMULRW,
    CLMULHW,
    SHFLW,
    UNSHFLW,
    BDEPW,
    BEXTW,
    PACKW,
    PACKUW,
    BFPW,
    // RV32M instructions
    MUL,
    MULH,
    MULHSU,
    MULHU,
    DIV,
    DIVU,
    REM,
    REMU,
    // RV64M instructions
    MULW,
    DIVW,
    DIVUW,
    REMW,
    REMUW,
    // RV32F instructions
    FLW,
    FSW,
    FMADD_S,
    FMSUB_S,
    FNMSUB_S,
    FNMADD_S,
    FADD_S,
    FSUB_S,
    FMUL_S,
    FDIV_S,
    FSQRT_S,
    FSGNJ_S,
    FSGNJN_S,
    FSGNJX_S,
    FMIN_S,
    FMAX_S,
    FCVT_W_S,
    FCVT_WU_S,
    FMV_X_W,
    FEQ_S,
    FLT_S,
    FLE_S,
    FCLASS_S,
    FCVT_S_W,
    FCVT_S_WU,
    FMV_W_X,
    // RV64F instruction
    FCVT_L_S,
    FCVT_LU_S,
    FCVT_S_L,
    FCVT_S_LU,
    // RV32D instructions
    FLD,
    FSD,
    FMADD_D,
    FMSUB_D,
    FNMSUB_D,
    FNMADD_D,
    FADD_D,
    FSUB_D,
    FMUL_D,
    FDIV_D,
    FSQRT_D,
    FSGNJ_D,
    FSGNJN_D,
    FSGNJX_D,
    FMIN_D,
    FMAX_D,
    FCVT_S_D,
    FCVT_D_S,
    FEQ_D,
    FLT_D,
    FLE_D,
    FCLASS_D,
    FCVT_W_D,
    FCVT_WU_D,
    FCVT_D_W,
    FCVT_D_WU,
    // RV64D
    FCVT_L_D,
    FCVT_LU_D,
    FMV_X_D,
    FCVT_D_L,
    FCVT_D_LU,
    FMV_D_X,
    // RV64I
    LWU,
    LD,
    SD,
    ADDIW,
    SLLIW,
    SRLIW,
    SRAIW,
    ADDW,
    SUBW,
    SLLW,
    SRLW,
    SRAW,
    // RV32C
    C_LW,
    C_SW,
    C_LWSP,
    C_SWSP,
    C_ADDI4SPN,
    C_ADDI,
    C_LI,
    C_ADDI16SP,
    C_LUI,
    C_SRLI,
    C_SRAI,
    C_ANDI,
    C_SUB,
    C_XOR,
    C_OR,
    C_AND,
    C_BEQZ,
    C_BNEZ,
    C_SLLI,
    C_MV,
    C_EBREAK,
    C_ADD,
    C_NOP,
    C_J,
    C_JAL,
    C_JR,
    C_JALR,
    // RV64C
    C_ADDIW,
    C_SUBW,
    C_ADDW,
    C_LD,
    C_SD,
    C_LDSP,
    C_SDSP,
    // RV128C
    C_SRLI64,
    C_SRAI64,
    C_SLLI64,
    C_LQ,
    C_SQ,
    C_LQSP,
    C_SQSP,
    // RV32FC
    C_FLW,
    C_FSW,
    C_FLWSP,
    C_FSWSP,
    // RV32DC
    C_FLD,
    C_FSD,
    C_FLDSP,
    C_FSDSP,
    // RV32A
    LR_W,
    SC_W,
    AMOSWAP_W,
    AMOADD_W,
    AMOAND_W,
    AMOOR_W,
    AMOXOR_W,
    AMOMIN_W,
    AMOMAX_W,
    AMOMINU_W,
    AMOMAXU_W,
    // RV64A
    LR_D,
    SC_D,
    AMOSWAP_D,
    AMOADD_D,
    AMOAND_D,
    AMOOR_D,
    AMOXOR_D,
    AMOMIN_D,
    AMOMAX_D,
    AMOMINU_D,
    AMOMAXU_D,
    // Vector instructions
    VSETVL,
    VSETVLI,
    VADD,
    VSUB,
    VRSUB,
    VWADDU,
    VWSUBU,
    VWADD,
    VWSUB,
    VADC,
    VMADC,
    VSBC,
    VMSBC,
    VAND,
    VOR,
    VXOR,
    VSLL,
    VSRL,
    VSRA,
    VNSRL,
    VNSRA,
    VMSEQ,
    VMSNE,
    VMSLTU,
    VMSLT,
    VMSLEU,
    VMSLE,
    VMSGTU,
    VMSGT,
    VMINU,
    VMIN,
    VMAXU,
    VMAX,
    VMUL,
    VMULH,
    VMULHU,
    VMULHSU,
    VDIVU,
    VDIV,
    VREMU,
    VREM,
    VWMUL,
    VWMULU,
    VWMULSU,
    VMACC,
    VNMSAC,
    VMADD,
    VNMSUB,
    VWMACCU,
    VWMACC,
    VWMACCSU,
    VWMACCUS,
    //VQMACCU,
    //VQMACC,
    //VQMACCSU,
    //VQMACCUS,
    VMERGE,
    VMV,
    VSADDU,
    VSADD,
    VSSUBU,
    VSSUB,
    VAADDU,
    VAADD,
    VASUBU,
    VASUB,
    VSSRL,
    VSSRA,
    VNCLIPU,
    VNCLIP,
    // 14. Vector Floating-Point Instructions
    VFADD,
    VFSUB,
    VFRSUB,
    VFMUL,
    VFDIV,
    VFRDIV,
    VFWMUL,
    VFMACC,
    VFNMACC,
    VFMSAC,
    VFNMSAC,
    VFMADD,
    VFNMADD,
    VFMSUB,
    VFNMSUB,
    VFWMACC,
    VFWNMACC,
    VFWMSAC,
    VFWNMSAC,
    VFSQRT_V,
    VFMIN,
    VFMAX,
    VFSGNJ,
    VFSGNJN,
    VFSGNJX,
    VMFEQ,
    VMFNE,
    VMFLT,
    VMFLE,
    VMFGT,
    VMFGE,
    VFCLASS_V,
    VFMERGE,
    VFMV,
    VFCVT_XU_F_V,
    VFCVT_X_F_V,
    VFCVT_F_XU_V,
    VFCVT_F_X_V,
    VFWCVT_XU_F_V,
    VFWCVT_X_F_V,
    VFWCVT_F_XU_V,
    VFWCVT_F_X_V,
    VFWCVT_F_F_V,
    VFNCVT_XU_F_W,
    VFNCVT_X_F_W,
    VFNCVT_F_XU_W,
    VFNCVT_F_X_W,
    VFNCVT_F_F_W,
    VFNCVT_ROD_F_F_W,
    // 15. Vector reduction instruction
    VREDSUM_VS,
    VREDMAXU_VS,
    VREDMAX_VS,
    VREDMINU_VS,
    VREDMIN_VS,
    VREDAND_VS,
    VREDOR_VS,
    VREDXOR_VS,
    VWREDSUMU_VS,
    VWREDSUM_VS,
    VFREDOSUM_VS,
    VFREDSUM_VS,
    VFREDMAX_VS,
    VFWREDOSUM_VS,
    VFWREDSUM_VS,
    // Vector mask instruction
    VMAND_MM,
    VMNAND_MM,
    VMANDNOT_MM,
    VMXOR_MM,
    VMOR_MM,
    VMNOR_MM,
    VMORNOT_MM,
    VMXNOR_MM,
    VPOPC_M,
    VFIRST_M,
    VMSBF_M,
    VMSIF_M,
    VMSOF_M,
    VIOTA_M,
    VID_V,
    // Vector permutation instruction
    VMV_X_S,
    VMV_S_X,
    VFMV_F_S,
    VFMV_S_F,
    VSLIDEUP,
    VSLIDEDOWN,
    VSLIDE1UP,
    VSLIDE1DOWN,
    VRGATHER,
    VCOMPRESS,
    VMV1R_V,
    VMV2R_V,
    VMV4R_V,
    VMV8R_V,
    // Vector load/store instruction
    VLE_V,
    VSE_V,
    VLSE_V,
    VSSE_V,
    VLXEI_V,
    VSXEI_V,
    VSUXEI_V,
    VLEFF_V,
    // Segmented load/store instruction
    VLSEGE_V,
    VSSEGE_V,
    VLSEGEFF_V,
    VLSSEGE_V,
    VSSSEGE_V,
    VLXSEGEI_V,
    VSXSEGEI_V,
    VSUXSEGEI_V,
    // Vector AMO instruction
    // EEW vector AMOs
    VAMOSWAPE_V,
    VAMOADDE_V,
    VAMOXORE_V,
    VAMOANDE_V,
    VAMOORE_V,
    VAMOMINE_V,
    VAMOMAXE_V,
    VAMOMINUE_V,
    VAMOMAXUE_V,
    // Supervisor instruction
    DRET,
    MRET,
    URET,
    SRET,
    WFI,
    SFENCE_VMA,
    // Custom instructions
    `include "isa/custom/riscv_custom_instr_enum.sv"
    // You can add other instructions here
    INVALID_INSTR
  } riscv_instr_name_t;

  // Maximum virtual address bits used by the program
  parameter int MAX_USED_VADDR_BITS = 30;

  parameter int SINGLE_PRECISION_FRACTION_BITS = 23;
  parameter int DOUBLE_PRECISION_FRACTION_BITS = 52;

  typedef enum bit [4:0] {
    ZERO = 5'b00000,
    RA, SP, GP, TP, T0, T1, T2, S0, S1, A0, A1, A2, A3, A4, A5, A6, A7,
    S2, S3, S4, S5, S6, S7, S8, S9, S10, S11, T3, T4, T5, T6
  } riscv_reg_t;

  typedef enum bit [4:0] {
    FT0, FT1, FT2, FT3, FT4, FT5, FT6, FT7, FS0, FS1, FA0, FA1, FA2, FA3, FA4, FA5,
    FA6, FA7, FS2, FS3, FS4, FS5, FS6, FS7, FS8, FS9, FS10, FS11, FT8, FT9, FT10, FT11
  } riscv_fpr_t;

  typedef enum bit [4:0] {
    V0, V1, V2, V3, V4, V5, V6, V7, V8, V9, V10, V11, V12, V13, V14, V15,
    V16, V17, V18, V19, V20, V21, V22, V23, V24, V25, V26, V27, V28, V29, V30, V31
  } riscv_vreg_t;

  typedef enum bit [5:0] {
    J_FORMAT = 0,
    U_FORMAT,
    I_FORMAT,
    B_FORMAT,
    R_FORMAT,
    S_FORMAT,
    R4_FORMAT,
    // Compressed instruction format
    CI_FORMAT,
    CB_FORMAT,
    CJ_FORMAT,
    CR_FORMAT,
    CA_FORMAT,
    CL_FORMAT,
    CS_FORMAT,
    CSS_FORMAT,
    CIW_FORMAT,
    // Vector instruction format
    VSET_FORMAT,
    VA_FORMAT,
    VS2_FORMAT, // op vd,vs2
    VL_FORMAT,
    VS_FORMAT,
    VLX_FORMAT,
    VSX_FORMAT,
    VLS_FORMAT,
    VSS_FORMAT,
    VAMO_FORMAT
  } riscv_instr_format_t;


  // Vector arithmetic instruction variant
  typedef enum bit [3:0] {
    VV,
    VI,
    VX,
    VF,
    WV,
    WI,
    WX,
    VVM,
    VIM,
    VXM,
    VFM,
    VS,
    VM
  } va_variant_t;

  typedef enum bit [5:0] {
    LOAD = 0,
    STORE,
    SHIFT,
    ARITHMETIC,
    LOGICAL,
    COMPARE,
    BRANCH,
    JUMP,
    SYNCH,
    SYSTEM,
    COUNTER,
    CSR,
    CHANGELEVEL,
    TRAP,
    INTERRUPT,
    `VECTOR_INCLUDE("riscv_instr_pkg_inc_riscv_instr_category_t.sv")
    AMO // (last one)
  } riscv_instr_category_t;

  typedef bit [11:0] riscv_csr_t;

  typedef enum bit [11:0] {
    // User mode register
    USTATUS         = 'h000,  // User status
    UIE             = 'h004,  // User interrupt-enable register
    UTVEC           = 'h005,  // User trap-handler base address
    USCRATCH        = 'h040,  // Scratch register for user trap handlers
    UEPC            = 'h041,  // User exception program counter
    UCAUSE          = 'h042,  // User trap cause
    UTVAL           = 'h043,  // User bad address or instruction
    UIP             = 'h044,  // User interrupt pending
    FFLAGS          = 'h001,  // Floating-Point Accrued Exceptions
    FRM             = 'h002,  // Floating-Point Dynamic Rounding Mode
    FCSR            = 'h003,  // Floating-Point Control/Status Register (FRM + FFLAGS)
    CYCLE           = 'hC00,  // Cycle counter for RDCYCLE instruction
    TIME            = 'hC01,  // Timer for RDTIME instruction
    INSTRET         = 'hC02,  // Instructions-retired counter for RDINSTRET instruction
    HPMCOUNTER3     = 'hC03,  // Performance-monitoring counter
    HPMCOUNTER4     = 'hC04,  // Performance-monitoring counter
    HPMCOUNTER5     = 'hC05,  // Performance-monitoring counter
    HPMCOUNTER6     = 'hC06,  // Performance-monitoring counter
    HPMCOUNTER7     = 'hC07,  // Performance-monitoring counter
    HPMCOUNTER8     = 'hC08,  // Performance-monitoring counter
    HPMCOUNTER9     = 'hC09,  // Performance-monitoring counter
    HPMCOUNTER10    = 'hC0A,  // Performance-monitoring counter
    HPMCOUNTER11    = 'hC0B,  // Performance-monitoring counter
    HPMCOUNTER12    = 'hC0C,  // Performance-monitoring counter
    HPMCOUNTER13    = 'hC0D,  // Performance-monitoring counter
    HPMCOUNTER14    = 'hC0E,  // Performance-monitoring counter
    HPMCOUNTER15    = 'hC0F,  // Performance-monitoring counter
    HPMCOUNTER16    = 'hC10,  // Performance-monitoring counter
    HPMCOUNTER17    = 'hC11,  // Performance-monitoring counter
    HPMCOUNTER18    = 'hC12,  // Performance-monitoring counter
    HPMCOUNTER19    = 'hC13,  // Performance-monitoring counter
    HPMCOUNTER20    = 'hC14,  // Performance-monitoring counter
    HPMCOUNTER21    = 'hC15,  // Performance-monitoring counter
    HPMCOUNTER22    = 'hC16,  // Performance-monitoring counter
    HPMCOUNTER23    = 'hC17,  // Performance-monitoring counter
    HPMCOUNTER24    = 'hC18,  // Performance-monitoring counter
    HPMCOUNTER25    = 'hC19,  // Performance-monitoring counter
    HPMCOUNTER26    = 'hC1A,  // Performance-monitoring counter
    HPMCOUNTER27    = 'hC1B,  // Performance-monitoring counter
    HPMCOUNTER28    = 'hC1C,  // Performance-monitoring counter
    HPMCOUNTER29    = 'hC1D,  // Performance-monitoring counter
    HPMCOUNTER30    = 'hC1E,  // Performance-monitoring counter
    HPMCOUNTER31    = 'hC1F,  // Performance-monitoring counter
    CYCLEH          = 'hC80,  // Upper 32 bits of CYCLE, RV32I only
    TIMEH           = 'hC81,  // Upper 32 bits of TIME, RV32I only
    INSTRETH        = 'hC82,  // Upper 32 bits of INSTRET, RV32I only
    HPMCOUNTER3H    = 'hC83,  // Upper 32 bits of HPMCOUNTER3, RV32I only
    HPMCOUNTER4H    = 'hC84,  // Upper 32 bits of HPMCOUNTER4, RV32I only
    HPMCOUNTER5H    = 'hC85,  // Upper 32 bits of HPMCOUNTER5, RV32I only
    HPMCOUNTER6H    = 'hC86,  // Upper 32 bits of HPMCOUNTER6, RV32I only
    HPMCOUNTER7H    = 'hC87,  // Upper 32 bits of HPMCOUNTER7, RV32I only
    HPMCOUNTER8H    = 'hC88,  // Upper 32 bits of HPMCOUNTER8, RV32I only
    HPMCOUNTER9H    = 'hC89,  // Upper 32 bits of HPMCOUNTER9, RV32I only
    HPMCOUNTER10H   = 'hC8A,  // Upper 32 bits of HPMCOUNTER10, RV32I only
    HPMCOUNTER11H   = 'hC8B,  // Upper 32 bits of HPMCOUNTER11, RV32I only
    HPMCOUNTER12H   = 'hC8C,  // Upper 32 bits of HPMCOUNTER12, RV32I only
    HPMCOUNTER13H   = 'hC8D,  // Upper 32 bits of HPMCOUNTER13, RV32I only
    HPMCOUNTER14H   = 'hC8E,  // Upper 32 bits of HPMCOUNTER14, RV32I only
    HPMCOUNTER15H   = 'hC8F,  // Upper 32 bits of HPMCOUNTER15, RV32I only
    HPMCOUNTER16H   = 'hC90,  // Upper 32 bits of HPMCOUNTER16, RV32I only
    HPMCOUNTER17H   = 'hC91,  // Upper 32 bits of HPMCOUNTER17, RV32I only
    HPMCOUNTER18H   = 'hC92,  // Upper 32 bits of HPMCOUNTER18, RV32I only
    HPMCOUNTER19H   = 'hC93,  // Upper 32 bits of HPMCOUNTER19, RV32I only
    HPMCOUNTER20H   = 'hC94,  // Upper 32 bits of HPMCOUNTER20, RV32I only
    HPMCOUNTER21H   = 'hC95,  // Upper 32 bits of HPMCOUNTER21, RV32I only
    HPMCOUNTER22H   = 'hC96,  // Upper 32 bits of HPMCOUNTER22, RV32I only
    HPMCOUNTER23H   = 'hC97,  // Upper 32 bits of HPMCOUNTER23, RV32I only
    HPMCOUNTER24H   = 'hC98,  // Upper 32 bits of HPMCOUNTER24, RV32I only
    HPMCOUNTER25H   = 'hC99,  // Upper 32 bits of HPMCOUNTER25, RV32I only
    HPMCOUNTER26H   = 'hC9A,  // Upper 32 bits of HPMCOUNTER26, RV32I only
    HPMCOUNTER27H   = 'hC9B,  // Upper 32 bits of HPMCOUNTER27, RV32I only
    HPMCOUNTER28H   = 'hC9C,  // Upper 32 bits of HPMCOUNTER28, RV32I only
    HPMCOUNTER29H   = 'hC9D,  // Upper 32 bits of HPMCOUNTER29, RV32I only
    HPMCOUNTER30H   = 'hC9E,  // Upper 32 bits of HPMCOUNTER30, RV32I only
    HPMCOUNTER31H   = 'hC9F,  // Upper 32 bits of HPMCOUNTER31, RV32I only
    // Supervisor mode register
    SSTATUS         = 'h100,  // Supervisor status
    SEDELEG         = 'h102,  // Supervisor exception delegation register
    SIDELEG         = 'h103,  // Supervisor interrupt delegation register
    SIE             = 'h104,  // Supervisor interrupt-enable register
    STVEC           = 'h105,  // Supervisor trap-handler base address
    SCOUNTEREN      = 'h106,  // Supervisor counter enable
    SSCRATCH        = 'h140,  // Scratch register for supervisor trap handlers
    SEPC            = 'h141,  // Supervisor exception program counter
    SCAUSE          = 'h142,  // Supervisor trap cause
    STVAL           = 'h143,  // Supervisor bad address or instruction
    SIP             = 'h144,  // Supervisor interrupt pending
    SATP            = 'h180,  // Supervisor address translation and protection
    // Machine mode register
    MVENDORID       = 'hF11,  // Vendor ID
    MARCHID         = 'hF12,  // Architecture ID
    MIMPID          = 'hF13,  // Implementation ID
    MHARTID         = 'hF14,  // Hardware thread ID
    MSTATUS         = 'h300,  // Machine status
    MISA            = 'h301,  // ISA and extensions
    MEDELEG         = 'h302,  // Machine exception delegation register
    MIDELEG         = 'h303,  // Machine interrupt delegation register
    MIE             = 'h304,  // Machine interrupt-enable register
    MTVEC           = 'h305,  // Machine trap-handler base address
    MCOUNTEREN      = 'h306,  // Machine counter enable
    MSCRATCH        = 'h340,  // Scratch register for machine trap handlers
    MEPC            = 'h341,  // Machine exception program counter
    MCAUSE          = 'h342,  // Machine trap cause
    MTVAL           = 'h343,  // Machine bad address or instruction
    MIP             = 'h344,  // Machine interrupt pending
    PMPCFG0         = 'h3A0,  // Physical memory protection configuration
    PMPCFG1         = 'h3A1,  // Physical memory protection configuration, RV32 only
    PMPCFG2         = 'h3A2,  // Physical memory protection configuration
    PMPCFG3         = 'h3A3,  // Physical memory protection configuration, RV32 only
    PMPADDR0        = 'h3B0,  // Physical memory protection address register
    PMPADDR1        = 'h3B1,  // Physical memory protection address register
    PMPADDR2        = 'h3B2,  // Physical memory protection address register
    PMPADDR3        = 'h3B3,  // Physical memory protection address register
    PMPADDR4        = 'h3B4,  // Physical memory protection address register
    PMPADDR5        = 'h3B5,  // Physical memory protection address register
    PMPADDR6        = 'h3B6,  // Physical memory protection address register
    PMPADDR7        = 'h3B7,  // Physical memory protection address register
    PMPADDR8        = 'h3B8,  // Physical memory protection address register
    PMPADDR9        = 'h3B9,  // Physical memory protection address register
    PMPADDR10       = 'h3BA,  // Physical memory protection address register
    PMPADDR11       = 'h3BB,  // Physical memory protection address register
    PMPADDR12       = 'h3BC,  // Physical memory protection address register
    PMPADDR13       = 'h3BD,  // Physical memory protection address register
    PMPADDR14       = 'h3BE,  // Physical memory protection address register
    PMPADDR15       = 'h3BF,  // Physical memory protection address register
    MCYCLE          = 'hB00,  // Machine cycle counter
    MINSTRET        = 'hB02,  // Machine instructions-retired counter
    MHPMCOUNTER3    = 'hB03,  // Machine performance-monitoring counter
    MHPMCOUNTER4    = 'hB04,  // Machine performance-monitoring counter
    MHPMCOUNTER5    = 'hB05,  // Machine performance-monitoring counter
    MHPMCOUNTER6    = 'hB06,  // Machine performance-monitoring counter
    MHPMCOUNTER7    = 'hB07,  // Machine performance-monitoring counter
    MHPMCOUNTER8    = 'hB08,  // Machine performance-monitoring counter
    MHPMCOUNTER9    = 'hB09,  // Machine performance-monitoring counter
    MHPMCOUNTER10   = 'hB0A,  // Machine performance-monitoring counter
    MHPMCOUNTER11   = 'hB0B,  // Machine performance-monitoring counter
    MHPMCOUNTER12   = 'hB0C,  // Machine performance-monitoring counter
    MHPMCOUNTER13   = 'hB0D,  // Machine performance-monitoring counter
    MHPMCOUNTER14   = 'hB0E,  // Machine performance-monitoring counter
    MHPMCOUNTER15   = 'hB0F,  // Machine performance-monitoring counter
    MHPMCOUNTER16   = 'hB10,  // Machine performance-monitoring counter
    MHPMCOUNTER17   = 'hB11,  // Machine performance-monitoring counter
    MHPMCOUNTER18   = 'hB12,  // Machine performance-monitoring counter
    MHPMCOUNTER19   = 'hB13,  // Machine performance-monitoring counter
    MHPMCOUNTER20   = 'hB14,  // Machine performance-monitoring counter
    MHPMCOUNTER21   = 'hB15,  // Machine performance-monitoring counter
    MHPMCOUNTER22   = 'hB16,  // Machine performance-monitoring counter
    MHPMCOUNTER23   = 'hB17,  // Machine performance-monitoring counter
    MHPMCOUNTER24   = 'hB18,  // Machine performance-monitoring counter
    MHPMCOUNTER25   = 'hB19,  // Machine performance-monitoring counter
    MHPMCOUNTER26   = 'hB1A,  // Machine performance-monitoring counter
    MHPMCOUNTER27   = 'hB1B,  // Machine performance-monitoring counter
    MHPMCOUNTER28   = 'hB1C,  // Machine performance-monitoring counter
    MHPMCOUNTER29   = 'hB1D,  // Machine performance-monitoring counter
    MHPMCOUNTER30   = 'hB1E,  // Machine performance-monitoring counter
    MHPMCOUNTER31   = 'hB1F,  // Machine performance-monitoring counter
    MCYCLEH         = 'hB80,  // Upper 32 bits of MCYCLE, RV32I only
    MINSTRETH       = 'hB82,  // Upper 32 bits of MINSTRET, RV32I only
    MHPMCOUNTER3H   = 'hB83,  // Upper 32 bits of HPMCOUNTER3, RV32I only
    MHPMCOUNTER4H   = 'hB84,  // Upper 32 bits of HPMCOUNTER4, RV32I only
    MHPMCOUNTER5H   = 'hB85,  // Upper 32 bits of HPMCOUNTER5, RV32I only
    MHPMCOUNTER6H   = 'hB86,  // Upper 32 bits of HPMCOUNTER6, RV32I only
    MHPMCOUNTER7H   = 'hB87,  // Upper 32 bits of HPMCOUNTER7, RV32I only
    MHPMCOUNTER8H   = 'hB88,  // Upper 32 bits of HPMCOUNTER8, RV32I only
    MHPMCOUNTER9H   = 'hB89,  // Upper 32 bits of HPMCOUNTER9, RV32I only
    MHPMCOUNTER10H  = 'hB8A,  // Upper 32 bits of HPMCOUNTER10, RV32I only
    MHPMCOUNTER11H  = 'hB8B,  // Upper 32 bits of HPMCOUNTER11, RV32I only
    MHPMCOUNTER12H  = 'hB8C,  // Upper 32 bits of HPMCOUNTER12, RV32I only
    MHPMCOUNTER13H  = 'hB8D,  // Upper 32 bits of HPMCOUNTER13, RV32I only
    MHPMCOUNTER14H  = 'hB8E,  // Upper 32 bits of HPMCOUNTER14, RV32I only
    MHPMCOUNTER15H  = 'hB8F,  // Upper 32 bits of HPMCOUNTER15, RV32I only
    MHPMCOUNTER16H  = 'hB90,  // Upper 32 bits of HPMCOUNTER16, RV32I only
    MHPMCOUNTER17H  = 'hB91,  // Upper 32 bits of HPMCOUNTER17, RV32I only
    MHPMCOUNTER18H  = 'hB92,  // Upper 32 bits of HPMCOUNTER18, RV32I only
    MHPMCOUNTER19H  = 'hB93,  // Upper 32 bits of HPMCOUNTER19, RV32I only
    MHPMCOUNTER20H  = 'hB94,  // Upper 32 bits of HPMCOUNTER20, RV32I only
    MHPMCOUNTER21H  = 'hB95,  // Upper 32 bits of HPMCOUNTER21, RV32I only
    MHPMCOUNTER22H  = 'hB96,  // Upper 32 bits of HPMCOUNTER22, RV32I only
    MHPMCOUNTER23H  = 'hB97,  // Upper 32 bits of HPMCOUNTER23, RV32I only
    MHPMCOUNTER24H  = 'hB98,  // Upper 32 bits of HPMCOUNTER24, RV32I only
    MHPMCOUNTER25H  = 'hB99,  // Upper 32 bits of HPMCOUNTER25, RV32I only
    MHPMCOUNTER26H  = 'hB9A,  // Upper 32 bits of HPMCOUNTER26, RV32I only
    MHPMCOUNTER27H  = 'hB9B,  // Upper 32 bits of HPMCOUNTER27, RV32I only
    MHPMCOUNTER28H  = 'hB9C,  // Upper 32 bits of HPMCOUNTER28, RV32I only
    MHPMCOUNTER29H  = 'hB9D,  // Upper 32 bits of HPMCOUNTER29, RV32I only
    MHPMCOUNTER30H  = 'hB9E,  // Upper 32 bits of HPMCOUNTER30, RV32I only
    MHPMCOUNTER31H  = 'hB9F,  // Upper 32 bits of HPMCOUNTER31, RV32I only
    MCOUNTINHIBIT   = 'h320,  // Machine counter-inhibit register
    MHPMEVENT3      = 'h323,  // Machine performance-monitoring event selector
    MHPMEVENT4      = 'h324,  // Machine performance-monitoring event selector
    MHPMEVENT5      = 'h325,  // Machine performance-monitoring event selector
    MHPMEVENT6      = 'h326,  // Machine performance-monitoring event selector
    MHPMEVENT7      = 'h327,  // Machine performance-monitoring event selector
    MHPMEVENT8      = 'h328,  // Machine performance-monitoring event selector
    MHPMEVENT9      = 'h329,  // Machine performance-monitoring event selector
    MHPMEVENT10     = 'h32A,  // Machine performance-monitoring event selector
    MHPMEVENT11     = 'h32B,  // Machine performance-monitoring event selector
    MHPMEVENT12     = 'h32C,  // Machine performance-monitoring event selector
    MHPMEVENT13     = 'h32D,  // Machine performance-monitoring event selector
    MHPMEVENT14     = 'h32E,  // Machine performance-monitoring event selector
    MHPMEVENT15     = 'h32F,  // Machine performance-monitoring event selector
    MHPMEVENT16     = 'h330,  // Machine performance-monitoring event selector
    MHPMEVENT17     = 'h331,  // Machine performance-monitoring event selector
    MHPMEVENT18     = 'h332,  // Machine performance-monitoring event selector
    MHPMEVENT19     = 'h333,  // Machine performance-monitoring event selector
    MHPMEVENT20     = 'h334,  // Machine performance-monitoring event selector
    MHPMEVENT21     = 'h335,  // Machine performance-monitoring event selector
    MHPMEVENT22     = 'h336,  // Machine performance-monitoring event selector
    MHPMEVENT23     = 'h337,  // Machine performance-monitoring event selector
    MHPMEVENT24     = 'h338,  // Machine performance-monitoring event selector
    MHPMEVENT25     = 'h339,  // Machine performance-monitoring event selector
    MHPMEVENT26     = 'h33A,  // Machine performance-monitoring event selector
    MHPMEVENT27     = 'h33B,  // Machine performance-monitoring event selector
    MHPMEVENT28     = 'h33C,  // Machine performance-monitoring event selector
    MHPMEVENT29     = 'h33D,  // Machine performance-monitoring event selector
    MHPMEVENT30     = 'h33E,  // Machine performance-monitoring event selector
    MHPMEVENT31     = 'h33F,  // Machine performance-monitoring event selector
    TSELECT         = 'h7A0,  // Debug/Trace trigger register select
    TDATA1          = 'h7A1,  // First Debug/Trace trigger data register
    TDATA2          = 'h7A2,  // Second Debug/Trace trigger data register
    TDATA3          = 'h7A3,  // Third Debug/Trace trigger data register
    TINFO           = 'h7A4,  // Debug trigger info register
    TCONTROL        = 'h7A5,  // Debug trigger control register
    MCONTEXT        = 'h7A8,  // Machine mode trigger context register
    SCONTEXT        = 'h7AA,  // Supervisor mode trigger context register
    DCSR            = 'h7B0,  // Debug control and status register
    DPC             = 'h7B1,  // Debug PC
    DSCRATCH0       = 'h7B2,  // Debug scratch register
    DSCRATCH1       = 'h7B3,  // Debug scratch register (last one)
    VSTART          = 'h008,  // Vector start position
    VXSTAT          = 'h009,  // Fixed point saturate flag
    VXRM            = 'h00A,  // Fixed point rounding mode
    VL              = 'hC20,  // Vector length
    VTYPE           = 'hC21,  // Vector data type register
    VLENB           = 'hC22   // VLEN/8 (vector register length in bytes)
  } privileged_reg_t;

  typedef enum bit [5:0] {
    RSVD,       // Reserved field
    MXL,        // mis.mxl
    EXTENSION,  // mis.extension
    MODE,       // satp.mode
    ASID,       // satp.asid
    PPN         // satp.ppn
  } privileged_reg_fld_t;

  typedef enum bit [1:0] {
    M_LEVEL = 2'b11,  // Machine mode
    S_LEVEL = 2'b01,  // Supervisor mode
    U_LEVEL = 2'b00   // User mode
  } privileged_level_t;

  typedef enum bit [1:0] {
    WPRI, // Reserved Writes Preserve Values, Reads Ignore Value
    WLRL, // Write/Read Only Legal Values
    WARL  // Write Any Values, Reads Legal Values
  } reg_field_access_t;

  //Pseudo instructions
  typedef enum bit [7:0] {
    LI = 0,
    LA
  } riscv_pseudo_instr_name_t;

  // Data pattern of the memory model
  typedef enum bit [1:0] {
    RAND_DATA = 0,
    ALL_ZERO,
    INCR_VAL
  } data_pattern_t;

  typedef enum bit [2:0] {
    NEXT_LEVEL_PAGE   = 3'b000, // Pointer to next level of page table.
    READ_ONLY_PAGE    = 3'b001, // Read-only page.
    READ_WRITE_PAGE   = 3'b011, // Read-write page.
    EXECUTE_ONLY_PAGE = 3'b100, // Execute-only page.
    READ_EXECUTE_PAGE = 3'b101, // Read-execute page.
    R_W_EXECUTE_PAGE  = 3'b111  // Read-write-execute page
  } pte_permission_t;

  typedef enum bit [3:0] {
    U_SOFTWARE_INTR  = 4'h0,
    S_SOFTWARE_INTR  = 4'h1,
    M_SOFTWARE_INTR  = 4'h3,
    U_TIMER_INTR     = 4'h4,
    S_TIMER_INTR     = 4'h5,
    M_TIMER_INTR     = 4'h7,
    U_EXTERNAL_INTR  = 4'h8,
    S_EXTERNAL_INTR  = 4'h9,
    M_EXTERNAL_INTR  = 4'hB
  } interrupt_cause_t;

  typedef enum bit [3:0] {
    INSTRUCTION_ADDRESS_MISALIGNED = 4'h0,
    INSTRUCTION_ACCESS_FAULT       = 4'h1,
    ILLEGAL_INSTRUCTION            = 4'h2,
    BREAKPOINT                     = 4'h3,
    LOAD_ADDRESS_MISALIGNED        = 4'h4,
    LOAD_ACCESS_FAULT              = 4'h5,
    STORE_AMO_ADDRESS_MISALIGNED   = 4'h6,
    STORE_AMO_ACCESS_FAULT         = 4'h7,
    ECALL_UMODE                    = 4'h8,
    ECALL_SMODE                    = 4'h9,
    ECALL_MMODE                    = 4'hB,
    INSTRUCTION_PAGE_FAULT         = 4'hC,
    LOAD_PAGE_FAULT                = 4'hD,
    STORE_AMO_PAGE_FAULT           = 4'hF
  } exception_cause_t;

  typedef enum int {
    MISA_EXT_A = 0,
    MISA_EXT_B,
    MISA_EXT_C,
    MISA_EXT_D,
    MISA_EXT_E,
    MISA_EXT_F,
    MISA_EXT_G,
    MISA_EXT_H,
    MISA_EXT_I,
    MISA_EXT_J,
    MISA_EXT_K,
    MISA_EXT_L,
    MISA_EXT_M,
    MISA_EXT_N,
    MISA_EXT_O,
    MISA_EXT_P,
    MISA_EXT_Q,
    MISA_EXT_R,
    MISA_EXT_S,
    MISA_EXT_T,
    MISA_EXT_U,
    MISA_EXT_V,
    MISA_EXT_W,
    MISA_EXT_X,
    MISA_EXT_Y,
    MISA_EXT_Z
  } misa_ext_t;

  typedef enum bit [1:0] {
    NO_HAZARD,
    RAW_HAZARD,
    WAR_HAZARD,
    WAW_HAZARD
  } hazard_e;

  `include "riscv_core_setting.sv"

  // PMP address matching mode
  typedef enum bit [1:0] {
    OFF   = 2'b00,
    TOR   = 2'b01,
    NA4   = 2'b10,
    NAPOT = 2'b11
  } pmp_addr_mode_t;

  // PMP configuration register layout
  // This configuration struct includes the pmp address for simplicity
  // TODO (udinator) allow a full 34 bit address for rv32?
`ifdef _VCP //GRK958
  typedef struct packed {
    bit                   l;
    bit [1:0]                  zero;
    pmp_addr_mode_t       a;
    bit                   x;
    bit                   w;
    bit                   r;
    // RV32: the pmpaddr is the top 32 bits of a 34 bit PMP address
    // RV64: the pmpaddr is the top 54 bits of a 56 bit PMP address
    bit [XLEN - 1 : 0]    addr;
    // The offset from the address of <main> - automatically populated by the
    // PMP generation routine.
    bit [XLEN - 1 : 0]    offset;
`else
  typedef struct{
    rand bit                   l;
    bit [1:0]                  zero;
    rand pmp_addr_mode_t       a;
    rand bit                   x;
    rand bit                   w;
    rand bit                   r;
    // RV32: the pmpaddr is the top 32 bits of a 34 bit PMP address
    // RV64: the pmpaddr is the top 54 bits of a 56 bit PMP address
    bit [XLEN - 1 : 0]    addr;
    // The offset from the address of <main> - automatically populated by the
    // PMP generation routine.
    rand bit [XLEN - 1 : 0]    offset;
`endif
  } pmp_cfg_reg_t;

  function automatic string hart_prefix(int hart = 0);
    if (NUM_HARTS <= 1) begin
      return "";
    end else begin
      return $sformatf("h%0d_", hart);
    end
  endfunction : hart_prefix

  function automatic string get_label(string label, int hart = 0);
    return {hart_prefix(hart), label};
  endfunction : get_label

  typedef struct packed {
    bit ill;
    bit fractional_lmul;
    bit [XLEN-2:7] reserved;
    int vediv;
    int vsew;
    int vlmul;
  } vtype_t;

  typedef enum bit [1:0] {
    RoundToNearestUp,
    RoundToNearestEven,
    RoundDown,
    RoundToOdd
  } vxrm_t;

  typedef enum int {
    ZBB,
    ZBS,
    ZBP,
    ZBE,
    ZBF,
    ZBC,
    ZBR,
    ZBM,
    ZBT,
    ZB_TMP // for uncategorized instructions
  } b_ext_group_t;

  `VECTOR_INCLUDE("riscv_instr_pkg_inc_variables.sv")

  typedef bit [15:0] program_id_t;

  // xSTATUS bit mask
  parameter bit [XLEN - 1 : 0] MPRV_BIT_MASK = 'h1 << 17;
  parameter bit [XLEN - 1 : 0] SUM_BIT_MASK  = 'h1 << 18;
  parameter bit [XLEN - 1 : 0] MPP_BIT_MASK  = 'h3 << 11;

  parameter int IMM25_WIDTH = 25;
  parameter int IMM12_WIDTH = 12;
  parameter int INSTR_WIDTH = 32;
  parameter int DATA_WIDTH  = 32;

  // Parameters for output assembly program formatting
  parameter int MAX_INSTR_STR_LEN = 11;
  parameter int LABEL_STR_LEN     = 18;

  // Parameter for program generation
  parameter int MAX_CALLSTACK_DEPTH = 20;
  parameter int MAX_SUB_PROGRAM_CNT = 20;
  parameter int MAX_CALL_PER_FUNC   = 5;

  string indent = {LABEL_STR_LEN{" "}};

  // Format the string to a fixed length
  function automatic string format_string(string str, int len = 10);
    string formatted_str;
    formatted_str = {len{" "}};
    if(len < str.len()) return str;
    formatted_str = {str, formatted_str.substr(0, len - str.len() - 1)};
    return formatted_str;
  endfunction

  // Print the data in the following format
  // 0xabcd, 0x1234, 0x3334 ...
  function automatic string format_data(bit [7:0] data[], int unsigned byte_per_group = 4);
    string str;
    int cnt;
    str = "0x";
    foreach(data[i]) begin
      if((i % byte_per_group == 0) && (i != data.size() - 1) && (i != 0)) begin
        str = {str, ", 0x"};
      end
      str = {str, $sformatf("%2x", data[i])};
    end
    return str;
  endfunction

  // Get the instr name enum from a string
  function automatic riscv_instr_name_t get_instr_name(string str);
    riscv_instr_name_t instr = instr.first;
    forever begin
      if(str.toupper() == instr.name()) begin
        return instr;
      end
      if(instr == instr.last) begin
        return INVALID_INSTR;
      end
      instr = instr.next;
    end
  endfunction

  // Push general purpose register to stack, this is needed before trap handling
  function automatic void push_gpr_to_kernel_stack(privileged_reg_t status,
                                                   privileged_reg_t scratch,
                                                   bit mprv,
                                                   riscv_reg_t sp,
                                                   riscv_reg_t tp,
                                                   ref string instr[$]);
    string store_instr = (XLEN == 32) ? "sw" : "sd";
    if (scratch inside {implemented_csr}) begin
      // Use kernal stack for handling exceptions
      // Save the user mode stack pointer to the scratch register
      instr.push_back($sformatf("csrrw x%0d, 0x%0x, x%0d", sp, scratch, sp));
      // Move TP to SP
      instr.push_back($sformatf("add x%0d, x%0d, zero", sp, tp));
    end
    // If MPRV is set and MPP is S/U mode, it means the address translation and memory protection
    // for load/store instruction is the same as the mode indicated by MPP. In this case, we
    // need to use the virtual address to access the kernel stack.
    if((status == MSTATUS) && (SATP_MODE != BARE)) begin
      // We temporarily use tp to check mstatus to avoid changing other GPR. The value of sp has
      // been saved to xScratch and can be restored later.
      if(mprv) begin
        instr.push_back($sformatf("csrr x%0d, 0x%0x // MSTATUS", tp, status));
        instr.push_back($sformatf("srli x%0d, x%0d, 11", tp, tp));  // Move MPP to bit 0
        instr.push_back($sformatf("andi x%0d, x%0d, 0x3", tp, tp)); // keep the MPP bits
        // Check if MPP equals to M-mode('b11)
        instr.push_back($sformatf("xori x%0d, x%0d, 0x3", tp, tp));
        instr.push_back($sformatf("bnez x%0d, 1f", tp));      // Use physical address for kernel SP
        // Use virtual address for stack pointer
        instr.push_back($sformatf("slli x%0d, x%0d, %0d", sp, sp, XLEN - MAX_USED_VADDR_BITS));
        instr.push_back($sformatf("srli x%0d, x%0d, %0d", sp, sp, XLEN - MAX_USED_VADDR_BITS));
      end
    end
    // Reserve space from kernel stack to save all 32 GPR except for x0
    instr.push_back($sformatf("1: addi x%0d, x%0d, -%0d", sp, sp, 31 * (XLEN/8)));
    // Push all GPRs to kernel stack
    for(int i = 1; i < 32; i++) begin
      instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", store_instr, i, i * (XLEN/8), sp));
    end
  endfunction

  // Pop general purpose register from stack, this is needed before returning to user program
  function automatic void pop_gpr_from_kernel_stack(privileged_reg_t status,
                                                    privileged_reg_t scratch,
                                                    bit mprv,
                                                    riscv_reg_t sp,
                                                    riscv_reg_t tp,
                                                    ref string instr[$]);
    string load_instr = (XLEN == 32) ? "lw" : "ld";
    // Pop user mode GPRs from kernel stack
    for(int i = 1; i < 32; i++) begin
      instr.push_back($sformatf("%0s  x%0d, %0d(x%0d)", load_instr, i, i * (XLEN/8), sp));
    end
    // Restore kernel stack pointer
    instr.push_back($sformatf("addi x%0d, x%0d, %0d", sp, sp, 31 * (XLEN/8)));
    if (scratch inside {implemented_csr}) begin
      // Move SP to TP
      instr.push_back($sformatf("add x%0d, x%0d, zero", tp, sp));
      // Restore user mode stack pointer
      instr.push_back($sformatf("csrrw x%0d, 0x%0x, x%0d", sp, scratch, sp));
    end
  endfunction

  // Get an integer argument from comand line
  function automatic void get_int_arg_value(string cmdline_str, ref int val);
    string s;
    if(inst.get_arg_value(cmdline_str, s)) begin
      val = s.atoi();
    end
  endfunction

  // Get a bool argument from comand line
  function automatic void get_bool_arg_value(string cmdline_str, ref bit val);
    string s;
    if(inst.get_arg_value(cmdline_str, s)) begin
      val = s.atobin();
    end
  endfunction

  // Get a hex argument from command line
  function automatic void get_hex_arg_value(string cmdline_str,
                                            ref bit [XLEN - 1 : 0] val);
    string s;
    if(inst.get_arg_value(cmdline_str, s)) begin
      val = s.atohex();
    end
  endfunction

  class cmdline_enum_processor #(parameter type T = riscv_instr_group_t);
    static function void get_array_values(string cmdline_str, ref T vals[]);
      string s;
      void'(inst.get_arg_value(cmdline_str, s));
      if(s != "") begin
        string cmdline_list[$];
        T value;
        uvm_split_string(s, ",", cmdline_list);
        vals = new[cmdline_list.size];
        foreach (cmdline_list[i]) begin
          if (uvm_enum_wrapper#(T)::from_name(
             cmdline_list[i].toupper(), value)) begin
            vals[i] = value;
          end else begin
            `uvm_fatal("riscv_instr_pkg", $sformatf(
                "Invalid value (%0s) specified in command line: %0s", cmdline_list[i], cmdline_str))
          end
        end
      end
    endfunction
  endclass

  riscv_reg_t all_gpr[] = {ZERO, RA, SP, GP, TP, T0, T1, T2, S0, S1, A0,
                           A1, A2, A3, A4, A5, A6, A7, S2, S3, S4, S5, S6,
                           S7, S8, S9, S10, S11, T3, T4, T5, T6};

  riscv_reg_t compressed_gpr[] = {S0, S1, A0, A1, A2, A3, A4, A5};

  riscv_instr_category_t all_categories[] = {
    LOAD, STORE, SHIFT, ARITHMETIC, LOGICAL, COMPARE, BRANCH, JUMP,
    SYNCH, SYSTEM, COUNTER, CSR, CHANGELEVEL, TRAP, INTERRUPT, AMO
  };

  function automatic void get_val(input string str, output bit [XLEN-1:0] val, input hex = 0);
    if (str.len() > 2) begin
      if (str.substr(0, 1) == "0x") begin
        str = str.substr(2, str.len() -1);
        val = str.atohex();
        return;
      end
    end
    if (hex) begin
      val = str.atohex();
    end else begin
      if (str.substr(0, 0) == "-") begin
        str = str.substr(1, str.len() - 1);
        val = -str.atoi();
      end else begin
        val = str.atoi();
      end
    end
    `uvm_info("riscv_instr_pkg", $sformatf("imm:%0s -> 0x%0x/%0d", str, val, $signed(val)),
              UVM_FULL)
  endfunction : get_val

  `include "riscv_vector_cfg.sv"
  `include "riscv_pmp_cfg.sv"
  typedef class riscv_instr;
  typedef class riscv_b_instr;
  `include "riscv_instr_gen_config.sv"
  `include "isa/riscv_instr.sv"
  `include "isa/riscv_amo_instr.sv"
  `include "isa/riscv_b_instr.sv"
  `include "isa/riscv_floating_point_instr.sv"
  `include "isa/riscv_vector_instr.sv"
  `include "isa/riscv_compressed_instr.sv"
  `include "isa/rv32a_instr.sv"
  `include "isa/rv32c_instr.sv"
  `include "isa/rv32dc_instr.sv"
  `include "isa/rv32d_instr.sv"
  `include "isa/rv32fc_instr.sv"
  `include "isa/rv32f_instr.sv"
  `include "isa/rv32i_instr.sv"
  `include "isa/rv32b_instr.sv"
  `include "isa/rv32m_instr.sv"
  `include "isa/rv64a_instr.sv"
  `include "isa/rv64b_instr.sv"
  `include "isa/rv64c_instr.sv"
  `include "isa/rv64d_instr.sv"
  `include "isa/rv64f_instr.sv"
  `include "isa/rv64i_instr.sv"
  `include "isa/rv64m_instr.sv"
  `include "isa/rv128c_instr.sv"
  `include "isa/rv32v_instr.sv"
  `include "isa/custom/riscv_custom_instr.sv"
  `include "isa/custom/rv32x_instr.sv"
  `include "isa/custom/rv64x_instr.sv"

  `include "riscv_pseudo_instr.sv"
  `include "riscv_illegal_instr.sv"
  `include "riscv_reg.sv"
  `include "riscv_privil_reg.sv"
  `include "riscv_page_table_entry.sv"
  `include "riscv_page_table_exception_cfg.sv"
  `include "riscv_page_table.sv"
  `include "riscv_page_table_list.sv"
  `include "riscv_privileged_common_seq.sv"
  `include "riscv_callstack_gen.sv"
  `include "riscv_data_page_gen.sv"

  `include "riscv_instr_stream.sv"
  `include "riscv_loop_instr.sv"
  `include "riscv_directed_instr_lib.sv"
  `include "riscv_load_store_instr_lib.sv"
  `include "riscv_amo_instr_lib.sv"

  `include "riscv_instr_sequence.sv"
  `include "riscv_asm_program_gen.sv"
  `include "riscv_debug_rom_gen.sv"
  `include "riscv_instr_cover_group.sv"
  `include "user_extension.svh"

endpackage
