// Copyright lowRISC contributors.
// Copyright 2017 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Package with constants used by Ibex
 */
package ibex_pkg;


/////////////
// Opcodes //
/////////////

typedef enum logic [6:0] {
  OPCODE_LOAD     = 7'h03,
  OPCODE_MISC_MEM = 7'h0f,
  OPCODE_OP_IMM   = 7'h13,
  OPCODE_AUIPC    = 7'h17,
  OPCODE_STORE    = 7'h23,
  OPCODE_OP       = 7'h33,
  OPCODE_LUI      = 7'h37,
  OPCODE_BRANCH   = 7'h63,
  OPCODE_JALR     = 7'h67,
  OPCODE_JAL      = 7'h6f,
  OPCODE_SYSTEM   = 7'h73
} opcode_e;


////////////////////
// ALU operations //
////////////////////

typedef enum logic [4:0] {
  // Arithmetics
  ALU_ADD,
  ALU_SUB,

  // Logics
  ALU_XOR,
  ALU_OR,
  ALU_AND,

  // Shifts
  ALU_SRA,
  ALU_SRL,
  ALU_SLL,

  // Comparisons
  ALU_LT,
  ALU_LTU,
  ALU_LE,
  ALU_LEU,
  ALU_GT,
  ALU_GTU,
  ALU_GE,
  ALU_GEU,
  ALU_EQ,
  ALU_NE,

  // Set lower than
  ALU_SLT,
  ALU_SLTU,
  ALU_SLET,
  ALU_SLETU
} alu_op_e;

typedef enum logic [1:0] {
  // Multiplier/divider
  MD_OP_MULL,
  MD_OP_MULH,
  MD_OP_DIV,
  MD_OP_REM
} md_op_e;


//////////////////////////////////
// Control and status registers //
//////////////////////////////////

// CSR operations
typedef enum logic [1:0] {
  CSR_OP_READ,
  CSR_OP_WRITE,
  CSR_OP_SET,
  CSR_OP_CLEAR
} csr_op_e;

// Privileged mode
typedef enum logic[1:0] {
  PRIV_LVL_M = 2'b11,
  PRIV_LVL_H = 2'b10,
  PRIV_LVL_S = 2'b01,
  PRIV_LVL_U = 2'b00
} priv_lvl_e;

// Constants for the dcsr.xdebugver fields
typedef enum logic[3:0] {
   XDEBUGVER_NO     = 4'd0, // no external debug support
   XDEBUGVER_STD    = 4'd4, // external debug according to RISC-V debug spec
   XDEBUGVER_NONSTD = 4'd15 // debug not conforming to RISC-V debug spec
} x_debug_ver_e;


//////////////
// ID stage //
//////////////

// Operand a selection
typedef enum logic[1:0] {
  OP_A_REG_A,
  OP_A_FWD,
  OP_A_CURRPC,
  OP_A_IMM
} op_a_sel_e;

// Immediate a selection
typedef enum logic {
  IMM_A_Z,
  IMM_A_ZERO
} imm_a_sel_e;

// Operand b selection
typedef enum logic {
  OP_B_REG_B,
  OP_B_IMM
} op_b_sel_e;

// Immediate b selection
typedef enum logic [2:0] {
  IMM_B_I,
  IMM_B_S,
  IMM_B_B,
  IMM_B_U,
  IMM_B_J,
  IMM_B_INCR_PC,
  IMM_B_INCR_ADDR
} imm_b_sel_e;

// Regfile write data selection
typedef enum logic [1:0] {
  RF_WD_LSU,
  RF_WD_EX,
  RF_WD_CSR
} rf_wd_sel_e;

//////////////
// IF stage //
//////////////

// PC mux selection
typedef enum logic [2:0] {
  PC_BOOT,
  PC_JUMP,
  PC_EXC,
  PC_ERET,
  PC_DRET
} pc_sel_e;

// Exception PC mux selection
typedef enum logic [1:0] {
  EXC_PC_EXC,
  EXC_PC_IRQ,
  EXC_PC_DBD,
  EXC_PC_DBG_EXC // Exception while in debug mode
} exc_pc_sel_e;

// Exception cause
typedef enum logic [5:0] {
  EXC_CAUSE_IRQ_SOFTWARE_M     = {1'b1, 5'd03},
  EXC_CAUSE_IRQ_TIMER_M        = {1'b1, 5'd07},
  EXC_CAUSE_IRQ_EXTERNAL_M     = {1'b1, 5'd11},
  // EXC_CAUSE_IRQ_FAST_0      = {1'b1, 5'd16},
  // EXC_CAUSE_IRQ_FAST_14     = {1'b1, 5'd30},
  EXC_CAUSE_IRQ_NM             = {1'b1, 5'd31}, // == EXC_CAUSE_IRQ_FAST_15
  EXC_CAUSE_INSN_ADDR_MISA     = {1'b0, 5'd00},
  EXC_CAUSE_INSTR_ACCESS_FAULT = {1'b0, 5'd01},
  EXC_CAUSE_ILLEGAL_INSN       = {1'b0, 5'd02},
  EXC_CAUSE_BREAKPOINT         = {1'b0, 5'd03},
  EXC_CAUSE_LOAD_ACCESS_FAULT  = {1'b0, 5'd05},
  EXC_CAUSE_STORE_ACCESS_FAULT = {1'b0, 5'd07},
  EXC_CAUSE_ECALL_UMODE        = {1'b0, 5'd08},
  EXC_CAUSE_ECALL_MMODE        = {1'b0, 5'd11}
} exc_cause_e;

// Debug cause
typedef enum logic [2:0] {
  DBG_CAUSE_NONE    = 3'h0,
  DBG_CAUSE_EBREAK  = 3'h1,
  DBG_CAUSE_TRIGGER = 3'h2,
  DBG_CAUSE_HALTREQ = 3'h3,
  DBG_CAUSE_STEP    = 3'h4
} dbg_cause_e;

// PMP constants
parameter int unsigned PMP_MAX_REGIONS      = 16;
parameter int unsigned PMP_CFG_W            = 8;

// PMP acces type
parameter int unsigned PMP_I = 0;
parameter int unsigned PMP_D = 1;

typedef enum logic [1:0] {
  PMP_ACC_EXEC    = 2'b00,
  PMP_ACC_WRITE   = 2'b01,
  PMP_ACC_READ    = 2'b10
} pmp_req_e;

// PMP cfg structures
typedef enum logic [1:0] {
  PMP_MODE_OFF   = 2'b00,
  PMP_MODE_TOR   = 2'b01,
  PMP_MODE_NA4   = 2'b10,
  PMP_MODE_NAPOT = 2'b11
} pmp_cfg_mode_e;

typedef struct packed {
  logic          lock;
  pmp_cfg_mode_e mode;
  logic          exec;
  logic          write;
  logic          read;
} pmp_cfg_t;

// CSRs
typedef enum logic[11:0] {
  // Machine information
  CSR_MHARTID   = 12'hF14,

  // Machine trap setup
  CSR_MSTATUS   = 12'h300,
  CSR_MISA      = 12'h301,
  CSR_MIE       = 12'h304,
  CSR_MTVEC     = 12'h305,

  // Machine trap handling
  CSR_MSCRATCH  = 12'h340,
  CSR_MEPC      = 12'h341,
  CSR_MCAUSE    = 12'h342,
  CSR_MTVAL     = 12'h343,
  CSR_MIP       = 12'h344,

  // Physical memory protection
  CSR_PMPCFG0   = 12'h3A0,
  CSR_PMPCFG1   = 12'h3A1,
  CSR_PMPCFG2   = 12'h3A2,
  CSR_PMPCFG3   = 12'h3A3,
  CSR_PMPADDR0  = 12'h3B0,
  CSR_PMPADDR1  = 12'h3B1,
  CSR_PMPADDR2  = 12'h3B2,
  CSR_PMPADDR3  = 12'h3B3,
  CSR_PMPADDR4  = 12'h3B4,
  CSR_PMPADDR5  = 12'h3B5,
  CSR_PMPADDR6  = 12'h3B6,
  CSR_PMPADDR7  = 12'h3B7,
  CSR_PMPADDR8  = 12'h3B8,
  CSR_PMPADDR9  = 12'h3B9,
  CSR_PMPADDR10 = 12'h3BA,
  CSR_PMPADDR11 = 12'h3BB,
  CSR_PMPADDR12 = 12'h3BC,
  CSR_PMPADDR13 = 12'h3BD,
  CSR_PMPADDR14 = 12'h3BE,
  CSR_PMPADDR15 = 12'h3BF,

  // Debug/trace
  CSR_DCSR      = 12'h7b0,
  CSR_DPC       = 12'h7b1,

  // Debug
  CSR_DSCRATCH0 = 12'h7b2, // optional
  CSR_DSCRATCH1 = 12'h7b3, // optional

  // Machine Counter/Timers
  CSR_MCOUNTINHIBIT      = 12'h320,
  CSR_MCYCLE             = 12'hB00,
  CSR_MCYCLEH            = 12'hB80,
  CSR_MINSTRET           = 12'hB02,
  CSR_MINSTRETH          = 12'hB82
} csr_num_e;

// CSR pmp-related offsets
parameter logic [11:0] CSR_OFF_PMP_CFG  = 12'h3A0; // pmp_cfg  @ 12'h3a0 - 12'h3a3
parameter logic [11:0] CSR_OFF_PMP_ADDR = 12'h3B0; // pmp_addr @ 12'h3b0 - 12'h3bf

// CSR mhpmcounter-related offsets and mask
parameter logic [11:0] CSR_OFF_MCOUNTER_SETUP = 12'h320; // mcounter_setup @ 12'h323 - 12'h33F
parameter logic [11:0] CSR_OFF_MCOUNTER       = 12'hB00; // mcounter       @ 12'hB03 - 12'hB1F
parameter logic [11:0] CSR_OFF_MCOUNTERH      = 12'hB80; // mcounterh      @ 12'hB83 - 12'hB9F
parameter logic [11:0] CSR_MASK_MCOUNTER      = 12'hFE0;

// CSR status bits
parameter int unsigned CSR_MSTATUS_MIE_BIT      = 3;
parameter int unsigned CSR_MSTATUS_MPIE_BIT     = 7;
parameter int unsigned CSR_MSTATUS_MPP_BIT_LOW  = 11;
parameter int unsigned CSR_MSTATUS_MPP_BIT_HIGH = 12;
parameter int unsigned CSR_MSTATUS_MPRV_BIT     = 17;
parameter int unsigned CSR_MSTATUS_TW_BIT       = 21;

// CSR interrupt pending/enable bits
parameter int unsigned CSR_MSIX_BIT      = 3;
parameter int unsigned CSR_MTIX_BIT      = 7;
parameter int unsigned CSR_MEIX_BIT      = 11;
parameter int unsigned CSR_MFIX_BIT_LOW  = 16;
parameter int unsigned CSR_MFIX_BIT_HIGH = 30;

endpackage
