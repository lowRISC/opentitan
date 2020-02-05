// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Control and Status Registers
 *
 * Control and Status Registers (CSRs) following the RISC-V Privileged
 * Specification, draft version 1.11
 */

`include "prim_assert.sv"

module ibex_cs_registers #(
    parameter bit          DbgTriggerEn     = 0,
    parameter int unsigned MHPMCounterNum   = 8,
    parameter int unsigned MHPMCounterWidth = 40,
    parameter bit          PMPEnable        = 0,
    parameter int unsigned PMPGranularity   = 0,
    parameter int unsigned PMPNumRegions    = 4,
    parameter bit          RV32E            = 0,
    parameter bit          RV32M            = 0
) (
    // Clock and Reset
    input  logic                 clk_i,
    input  logic                 rst_ni,

    // Hart ID
    input  logic [31:0]          hart_id_i,

    // Privilege mode
    output ibex_pkg::priv_lvl_e  priv_mode_id_o,
    output ibex_pkg::priv_lvl_e  priv_mode_if_o,
    output ibex_pkg::priv_lvl_e  priv_mode_lsu_o,
    output logic                 csr_mstatus_tw_o,

    // mtvec
    output logic [31:0]          csr_mtvec_o,
    input  logic                 csr_mtvec_init_i,
    input  logic [31:0]          boot_addr_i,

    // Interface to registers (SRAM like)
    input  logic                 csr_access_i,
    input  ibex_pkg::csr_num_e   csr_addr_i,
    input  logic [31:0]          csr_wdata_i,
    input  ibex_pkg::csr_op_e    csr_op_i,
    output logic [31:0]          csr_rdata_o,

    // interrupts
    input  logic                 irq_software_i,
    input  logic                 irq_timer_i,
    input  logic                 irq_external_i,
    input  logic [14:0]          irq_fast_i,
    input  logic                 nmi_mode_i,
    output logic                 irq_pending_o,          // interrupt request pending
    output ibex_pkg::irqs_t      irqs_o,                 // interrupt requests qualified with mie
    output logic                 csr_mstatus_mie_o,
    output logic [31:0]          csr_mepc_o,

    // PMP
    output ibex_pkg::pmp_cfg_t   csr_pmp_cfg_o  [PMPNumRegions],
    output logic [33:0]          csr_pmp_addr_o [PMPNumRegions],

    // debug
    input  logic                 debug_mode_i,
    input  ibex_pkg::dbg_cause_e debug_cause_i,
    input  logic                 debug_csr_save_i,
    output logic [31:0]          csr_depc_o,
    output logic                 debug_single_step_o,
    output logic                 debug_ebreakm_o,
    output logic                 debug_ebreaku_o,
    output logic                 trigger_match_o,

    input  logic [31:0]          pc_if_i,
    input  logic [31:0]          pc_id_i,

    input  logic                 csr_save_if_i,
    input  logic                 csr_save_id_i,
    input  logic                 csr_restore_mret_i,
    input  logic                 csr_restore_dret_i,
    input  logic                 csr_save_cause_i,
    input  ibex_pkg::exc_cause_e csr_mcause_i,
    input  logic [31:0]          csr_mtval_i,
    output logic                 illegal_csr_insn_o,     // access to non-existent CSR,
                                                         // with wrong priviledge level, or
                                                         // missing write permissions
    input  logic                 instr_new_id_i,         // ID stage sees a new instr

    // Performance Counters
    input  logic                 instr_ret_i,            // instr retired in ID/EX stage
    input  logic                 instr_ret_compressed_i, // compressed instr retired
    input  logic                 imiss_i,                // instr fetch
    input  logic                 pc_set_i,               // PC was set to a new value
    input  logic                 jump_i,                 // jump instr seen (j, jr, jal, jalr)
    input  logic                 branch_i,               // branch instr seen (bf, bnf)
    input  logic                 branch_taken_i,         // branch was taken
    input  logic                 mem_load_i,             // load from memory in this cycle
    input  logic                 mem_store_i,            // store to memory in this cycle
    input  logic                 lsu_busy_i
);

  import ibex_pkg::*;

  // misa
  localparam logic [1:0] MXL = 2'd1; // M-XLEN: XLEN in M-Mode for RV32
  localparam logic [31:0] MISA_VALUE =
      (0          <<  0)  // A - Atomic Instructions extension
    | (1          <<  2)  // C - Compressed extension
    | (0          <<  3)  // D - Double precision floating-point extension
    | (32'(RV32E) <<  4)  // E - RV32E base ISA
    | (0          <<  5)  // F - Single precision floating-point extension
    | (1          <<  8)  // I - RV32I/64I/128I base ISA
    | (32'(RV32M) << 12)  // M - Integer Multiply/Divide extension
    | (0          << 13)  // N - User level interrupts supported
    | (0          << 18)  // S - Supervisor mode implemented
    | (1          << 20)  // U - User mode implemented
    | (0          << 23)  // X - Non-standard extensions present
    | (32'(MXL)   << 30); // M-XLEN

  typedef struct packed {
    logic      mie;
    logic      mpie;
    priv_lvl_e mpp;
    logic      mprv;
    logic      tw;
  } Status_t;

  typedef struct packed {
    logic      mpie;
    priv_lvl_e mpp;
  } StatusStk_t;

  typedef struct packed {
      x_debug_ver_e xdebugver;
      logic [11:0]  zero2;
      logic         ebreakm;
      logic         zero1;
      logic         ebreaks;
      logic         ebreaku;
      logic         stepie;
      logic         stopcount;
      logic         stoptime;
      dbg_cause_e   cause;
      logic         zero0;
      logic         mprven;
      logic         nmip;
      logic         step;
      priv_lvl_e    prv;
  } Dcsr_t;

  // Interrupt and exception control signals
  logic [31:0] exception_pc;

  // CSRs
  priv_lvl_e   priv_lvl_q, priv_lvl_d;
  Status_t     mstatus_q, mstatus_d;
  irqs_t       mie_q, mie_d;
  logic [31:0] mscratch_q, mscratch_d;
  logic [31:0] mepc_q, mepc_d;
  logic  [5:0] mcause_q, mcause_d;
  logic [31:0] mtval_q, mtval_d;
  logic [31:0] mtvec_q, mtvec_d;
  irqs_t       mip;
  Dcsr_t       dcsr_q, dcsr_d;
  logic [31:0] depc_q, depc_d;
  logic [31:0] dscratch0_q, dscratch0_d;
  logic [31:0] dscratch1_q, dscratch1_d;

  // CSRs for recoverable NMIs
  // NOTE: these CSRS are nonstandard, see https://github.com/riscv/riscv-isa-manual/issues/261
  StatusStk_t  mstack_q, mstack_d;
  logic [31:0] mstack_epc_q, mstack_epc_d;
  logic  [5:0] mstack_cause_q, mstack_cause_d;

  // PMP Signals
  logic [31:0]                 pmp_addr_rdata  [PMP_MAX_REGIONS];
  logic [PMP_CFG_W-1:0]        pmp_cfg_rdata   [PMP_MAX_REGIONS];

  // Hardware performance monitor signals
  logic [31:0]                 mcountinhibit;
  // Only have mcountinhibit flops for counters that actually exist
  logic [MHPMCounterNum+3-1:0] mcountinhibit_d, mcountinhibit_q;
  logic                        mcountinhibit_we;

  logic [63:0] mhpmcounter_d [32];
  // mhpmcounter flops are elaborated below providing only the precise number that is required based
  // on MHPMCounterNum/MHPMCounterWidth. This signal connects to the Q output of these flops
  // where they exist and is otherwise 0.
  logic [63:0] mhpmcounter [32];
  logic [31:0] mhpmcounter_we;
  logic [31:0] mhpmcounterh_we;
  logic [31:0] mhpmcounter_incr;
  logic [31:0] mhpmevent [32];
  logic  [4:0] mhpmcounter_idx;

  // Debug / trigger registers
  logic [31:0] tselect_rdata;
  logic [31:0] tmatch_control_rdata;
  logic [31:0] tmatch_value_rdata;

  // CSR update logic
  logic [31:0] csr_wdata_int;
  logic [31:0] csr_rdata_int;
  logic        csr_we_int;
  logic        csr_wreq;

  // Access violation signals
  logic        illegal_csr;
  logic        illegal_csr_priv;
  logic        illegal_csr_write;

  logic [7:0]  unused_boot_addr;
  logic [2:0]  unused_csr_addr;

  assign unused_boot_addr = boot_addr_i[7:0];

  /////////////
  // CSR reg //
  /////////////

  logic [$bits(csr_num_e)-1:0] csr_addr;
  assign csr_addr           = {csr_addr_i};
  assign unused_csr_addr    = csr_addr[7:5];
  assign mhpmcounter_idx    = csr_addr[4:0];

  // See RISC-V Privileged Specification, version 1.11, Section 2.1
  assign illegal_csr_priv   = (csr_addr[9:8] > {priv_lvl_q});
  assign illegal_csr_write  = (csr_addr[11:10] == 2'b11) && csr_wreq;
  assign illegal_csr_insn_o = csr_access_i & (illegal_csr | illegal_csr_write | illegal_csr_priv);

  // mip CSR is purely combinational - must be able to re-enable the clock upon WFI
  assign mip.irq_software = irq_software_i;
  assign mip.irq_timer    = irq_timer_i;
  assign mip.irq_external = irq_external_i;
  assign mip.irq_fast     = irq_fast_i;

  // read logic
  always_comb begin
    csr_rdata_int = '0;
    illegal_csr   = 1'b0;

    unique case (csr_addr_i)
      // mhartid: unique hardware thread id
      CSR_MHARTID: csr_rdata_int = hart_id_i;

      // mstatus: always M-mode, contains IE bit
      CSR_MSTATUS: begin
        csr_rdata_int                                                   = '0;
        csr_rdata_int[CSR_MSTATUS_MIE_BIT]                              = mstatus_q.mie;
        csr_rdata_int[CSR_MSTATUS_MPIE_BIT]                             = mstatus_q.mpie;
        csr_rdata_int[CSR_MSTATUS_MPP_BIT_HIGH:CSR_MSTATUS_MPP_BIT_LOW] = mstatus_q.mpp;
        csr_rdata_int[CSR_MSTATUS_MPRV_BIT]                             = mstatus_q.mprv;
        csr_rdata_int[CSR_MSTATUS_TW_BIT]                               = mstatus_q.tw;
      end

      // misa
      CSR_MISA: csr_rdata_int = MISA_VALUE;

      // interrupt enable
      CSR_MIE: begin
        csr_rdata_int                                     = '0;
        csr_rdata_int[CSR_MSIX_BIT]                       = mie_q.irq_software;
        csr_rdata_int[CSR_MTIX_BIT]                       = mie_q.irq_timer;
        csr_rdata_int[CSR_MEIX_BIT]                       = mie_q.irq_external;
        csr_rdata_int[CSR_MFIX_BIT_HIGH:CSR_MFIX_BIT_LOW] = mie_q.irq_fast;
      end

      CSR_MSCRATCH: csr_rdata_int = mscratch_q;

      // mtvec: trap-vector base address
      CSR_MTVEC: csr_rdata_int = mtvec_q;

      // mepc: exception program counter
      CSR_MEPC: csr_rdata_int = mepc_q;

      // mcause: exception cause
      CSR_MCAUSE: csr_rdata_int = {mcause_q[5], 26'b0, mcause_q[4:0]};

      // mtval: trap value
      CSR_MTVAL: csr_rdata_int = mtval_q;

      // mip: interrupt pending
      CSR_MIP: begin
        csr_rdata_int                                     = '0;
        csr_rdata_int[CSR_MSIX_BIT]                       = mip.irq_software;
        csr_rdata_int[CSR_MTIX_BIT]                       = mip.irq_timer;
        csr_rdata_int[CSR_MEIX_BIT]                       = mip.irq_external;
        csr_rdata_int[CSR_MFIX_BIT_HIGH:CSR_MFIX_BIT_LOW] = mip.irq_fast;
      end

      // PMP registers
      CSR_PMPCFG0:   csr_rdata_int = {pmp_cfg_rdata[3],  pmp_cfg_rdata[2],
                                      pmp_cfg_rdata[1],  pmp_cfg_rdata[0]};
      CSR_PMPCFG1:   csr_rdata_int = {pmp_cfg_rdata[7],  pmp_cfg_rdata[6],
                                      pmp_cfg_rdata[5],  pmp_cfg_rdata[4]};
      CSR_PMPCFG2:   csr_rdata_int = {pmp_cfg_rdata[11], pmp_cfg_rdata[10],
                                      pmp_cfg_rdata[9],  pmp_cfg_rdata[8]};
      CSR_PMPCFG3:   csr_rdata_int = {pmp_cfg_rdata[15], pmp_cfg_rdata[14],
                                      pmp_cfg_rdata[13], pmp_cfg_rdata[12]};
      CSR_PMPADDR0:  csr_rdata_int = pmp_addr_rdata[0];
      CSR_PMPADDR1:  csr_rdata_int = pmp_addr_rdata[1];
      CSR_PMPADDR2:  csr_rdata_int = pmp_addr_rdata[2];
      CSR_PMPADDR3:  csr_rdata_int = pmp_addr_rdata[3];
      CSR_PMPADDR4:  csr_rdata_int = pmp_addr_rdata[4];
      CSR_PMPADDR5:  csr_rdata_int = pmp_addr_rdata[5];
      CSR_PMPADDR6:  csr_rdata_int = pmp_addr_rdata[6];
      CSR_PMPADDR7:  csr_rdata_int = pmp_addr_rdata[7];
      CSR_PMPADDR8:  csr_rdata_int = pmp_addr_rdata[8];
      CSR_PMPADDR9:  csr_rdata_int = pmp_addr_rdata[9];
      CSR_PMPADDR10: csr_rdata_int = pmp_addr_rdata[10];
      CSR_PMPADDR11: csr_rdata_int = pmp_addr_rdata[11];
      CSR_PMPADDR12: csr_rdata_int = pmp_addr_rdata[12];
      CSR_PMPADDR13: csr_rdata_int = pmp_addr_rdata[13];
      CSR_PMPADDR14: csr_rdata_int = pmp_addr_rdata[14];
      CSR_PMPADDR15: csr_rdata_int = pmp_addr_rdata[15];

      CSR_DCSR: begin
        csr_rdata_int = dcsr_q;
        illegal_csr = ~debug_mode_i;
      end
      CSR_DPC: begin
        csr_rdata_int = depc_q;
        illegal_csr = ~debug_mode_i;
      end
      CSR_DSCRATCH0: begin
        csr_rdata_int = dscratch0_q;
        illegal_csr = ~debug_mode_i;
      end
      CSR_DSCRATCH1: begin
        csr_rdata_int = dscratch1_q;
        illegal_csr = ~debug_mode_i;
      end

      // machine counter/timers
      CSR_MCOUNTINHIBIT: csr_rdata_int = mcountinhibit;
      CSR_MHPMEVENT3,
      CSR_MHPMEVENT4,  CSR_MHPMEVENT5,  CSR_MHPMEVENT6,  CSR_MHPMEVENT7,
      CSR_MHPMEVENT8,  CSR_MHPMEVENT9,  CSR_MHPMEVENT10, CSR_MHPMEVENT11,
      CSR_MHPMEVENT12, CSR_MHPMEVENT13, CSR_MHPMEVENT14, CSR_MHPMEVENT15,
      CSR_MHPMEVENT16, CSR_MHPMEVENT17, CSR_MHPMEVENT18, CSR_MHPMEVENT19,
      CSR_MHPMEVENT20, CSR_MHPMEVENT21, CSR_MHPMEVENT22, CSR_MHPMEVENT23,
      CSR_MHPMEVENT24, CSR_MHPMEVENT25, CSR_MHPMEVENT26, CSR_MHPMEVENT27,
      CSR_MHPMEVENT28, CSR_MHPMEVENT29, CSR_MHPMEVENT30, CSR_MHPMEVENT31: begin
        csr_rdata_int = mhpmevent[mhpmcounter_idx];
      end

      CSR_MCYCLE,
      CSR_MINSTRET,
      CSR_MHPMCOUNTER3,
      CSR_MHPMCOUNTER4,  CSR_MHPMCOUNTER5,  CSR_MHPMCOUNTER6,  CSR_MHPMCOUNTER7,
      CSR_MHPMCOUNTER8,  CSR_MHPMCOUNTER9,  CSR_MHPMCOUNTER10, CSR_MHPMCOUNTER11,
      CSR_MHPMCOUNTER12, CSR_MHPMCOUNTER13, CSR_MHPMCOUNTER14, CSR_MHPMCOUNTER15,
      CSR_MHPMCOUNTER16, CSR_MHPMCOUNTER17, CSR_MHPMCOUNTER18, CSR_MHPMCOUNTER19,
      CSR_MHPMCOUNTER20, CSR_MHPMCOUNTER21, CSR_MHPMCOUNTER22, CSR_MHPMCOUNTER23,
      CSR_MHPMCOUNTER24, CSR_MHPMCOUNTER25, CSR_MHPMCOUNTER26, CSR_MHPMCOUNTER27,
      CSR_MHPMCOUNTER28, CSR_MHPMCOUNTER29, CSR_MHPMCOUNTER30, CSR_MHPMCOUNTER31: begin
        csr_rdata_int = mhpmcounter[mhpmcounter_idx][31:0];
      end

      CSR_MCYCLEH,
      CSR_MINSTRETH,
      CSR_MHPMCOUNTER3H,
      CSR_MHPMCOUNTER4H,  CSR_MHPMCOUNTER5H,  CSR_MHPMCOUNTER6H,  CSR_MHPMCOUNTER7H,
      CSR_MHPMCOUNTER8H,  CSR_MHPMCOUNTER9H,  CSR_MHPMCOUNTER10H, CSR_MHPMCOUNTER11H,
      CSR_MHPMCOUNTER12H, CSR_MHPMCOUNTER13H, CSR_MHPMCOUNTER14H, CSR_MHPMCOUNTER15H,
      CSR_MHPMCOUNTER16H, CSR_MHPMCOUNTER17H, CSR_MHPMCOUNTER18H, CSR_MHPMCOUNTER19H,
      CSR_MHPMCOUNTER20H, CSR_MHPMCOUNTER21H, CSR_MHPMCOUNTER22H, CSR_MHPMCOUNTER23H,
      CSR_MHPMCOUNTER24H, CSR_MHPMCOUNTER25H, CSR_MHPMCOUNTER26H, CSR_MHPMCOUNTER27H,
      CSR_MHPMCOUNTER28H, CSR_MHPMCOUNTER29H, CSR_MHPMCOUNTER30H, CSR_MHPMCOUNTER31H: begin
        csr_rdata_int = mhpmcounter[mhpmcounter_idx][63:32];
      end

      // Debug triggers
      CSR_TSELECT: begin
        csr_rdata_int = tselect_rdata;
        illegal_csr   = ~DbgTriggerEn;
      end
      CSR_TDATA1: begin
        csr_rdata_int = tmatch_control_rdata;
        illegal_csr   = ~DbgTriggerEn;
      end
      CSR_TDATA2: begin
        csr_rdata_int = tmatch_value_rdata;
        illegal_csr   = ~DbgTriggerEn;
      end
      CSR_TDATA3: begin
        csr_rdata_int = '0;
        illegal_csr   = ~DbgTriggerEn;
      end
      CSR_MCONTEXT: begin
        csr_rdata_int = '0;
        illegal_csr   = ~DbgTriggerEn;
      end
      CSR_SCONTEXT: begin
        csr_rdata_int = '0;
        illegal_csr   = ~DbgTriggerEn;
      end

      default: begin
        illegal_csr = 1'b1;
      end
    endcase
  end

  // write logic
  always_comb begin
    exception_pc = pc_id_i;

    priv_lvl_d   = priv_lvl_q;
    mstatus_d    = mstatus_q;
    mie_d        = mie_q;
    mscratch_d   = mscratch_q;
    mepc_d       = mepc_q;
    mcause_d     = mcause_q;
    mtval_d      = mtval_q;
    mtvec_d      = csr_mtvec_init_i ? {boot_addr_i[31:8], 6'b0, 2'b01} : mtvec_q;
    dcsr_d       = dcsr_q;
    depc_d       = depc_q;
    dscratch0_d  = dscratch0_q;
    dscratch1_d  = dscratch1_q;

    mstack_d       = mstack_q;
    mstack_epc_d   = mstack_epc_q;
    mstack_cause_d = mstack_cause_q;

    mcountinhibit_we = 1'b0;
    mhpmcounter_we   = '0;
    mhpmcounterh_we  = '0;

    if (csr_we_int) begin
      unique case (csr_addr_i)
        // mstatus: IE bit
        CSR_MSTATUS: begin
          mstatus_d = '{
              mie:  csr_wdata_int[CSR_MSTATUS_MIE_BIT],
              mpie: csr_wdata_int[CSR_MSTATUS_MPIE_BIT],
              mpp:  priv_lvl_e'(csr_wdata_int[CSR_MSTATUS_MPP_BIT_HIGH:CSR_MSTATUS_MPP_BIT_LOW]),
              mprv: csr_wdata_int[CSR_MSTATUS_MPRV_BIT],
              tw:   csr_wdata_int[CSR_MSTATUS_TW_BIT]
          };
          // Convert illegal values to M-mode
          if ((mstatus_d.mpp != PRIV_LVL_M) && (mstatus_d.mpp != PRIV_LVL_U)) begin
            mstatus_d.mpp = PRIV_LVL_M;
          end
        end

        // interrupt enable
        CSR_MIE: begin
          mie_d.irq_software = csr_wdata_int[CSR_MSIX_BIT];
          mie_d.irq_timer    = csr_wdata_int[CSR_MTIX_BIT];
          mie_d.irq_external = csr_wdata_int[CSR_MEIX_BIT];
          mie_d.irq_fast     = csr_wdata_int[CSR_MFIX_BIT_HIGH:CSR_MFIX_BIT_LOW];
        end

        CSR_MSCRATCH: mscratch_d = csr_wdata_int;

        // mepc: exception program counter
        CSR_MEPC: mepc_d = {csr_wdata_int[31:1], 1'b0};

        // mcause
        CSR_MCAUSE: mcause_d = {csr_wdata_int[31], csr_wdata_int[4:0]};

        // mtval: trap value
        CSR_MTVAL: mtval_d = csr_wdata_int;

        // mtvec
        // mtvec.MODE set to vectored
        // mtvec.BASE must be 256-byte aligned
        CSR_MTVEC: mtvec_d = {csr_wdata_int[31:8], 6'b0, 2'b01};

        CSR_DCSR: begin
          dcsr_d = csr_wdata_int;
          dcsr_d.xdebugver = XDEBUGVER_STD;
          // Change to PRIV_LVL_M if software writes an unsupported value
          if ((dcsr_d.prv != PRIV_LVL_M) && (dcsr_d.prv != PRIV_LVL_U)) begin
            dcsr_d.prv = PRIV_LVL_M;
          end

          // currently not supported:
          dcsr_d.nmip = 1'b0;
          dcsr_d.mprven = 1'b0;
          dcsr_d.stopcount = 1'b0;
          dcsr_d.stoptime = 1'b0;

          // forced to be zero
          dcsr_d.zero0 = 1'b0;
          dcsr_d.zero1 = 1'b0;
          dcsr_d.zero2 = 12'h0;
        end

        // dpc: debug program counter
        CSR_DPC: depc_d = {csr_wdata_int[31:1], 1'b0};

        CSR_DSCRATCH0: dscratch0_d = csr_wdata_int;
        CSR_DSCRATCH1: dscratch1_d = csr_wdata_int;

        // machine counter/timers
        CSR_MCOUNTINHIBIT: mcountinhibit_we = 1'b1;

        CSR_MCYCLE,
        CSR_MINSTRET,
        CSR_MHPMCOUNTER3,
        CSR_MHPMCOUNTER4,  CSR_MHPMCOUNTER5,  CSR_MHPMCOUNTER6,  CSR_MHPMCOUNTER7,
        CSR_MHPMCOUNTER8,  CSR_MHPMCOUNTER9,  CSR_MHPMCOUNTER10, CSR_MHPMCOUNTER11,
        CSR_MHPMCOUNTER12, CSR_MHPMCOUNTER13, CSR_MHPMCOUNTER14, CSR_MHPMCOUNTER15,
        CSR_MHPMCOUNTER16, CSR_MHPMCOUNTER17, CSR_MHPMCOUNTER18, CSR_MHPMCOUNTER19,
        CSR_MHPMCOUNTER20, CSR_MHPMCOUNTER21, CSR_MHPMCOUNTER22, CSR_MHPMCOUNTER23,
        CSR_MHPMCOUNTER24, CSR_MHPMCOUNTER25, CSR_MHPMCOUNTER26, CSR_MHPMCOUNTER27,
        CSR_MHPMCOUNTER28, CSR_MHPMCOUNTER29, CSR_MHPMCOUNTER30, CSR_MHPMCOUNTER31: begin
          mhpmcounter_we[mhpmcounter_idx] = 1'b1;
        end

        CSR_MCYCLEH,
        CSR_MINSTRETH,
        CSR_MHPMCOUNTER3H,
        CSR_MHPMCOUNTER4H,  CSR_MHPMCOUNTER5H,  CSR_MHPMCOUNTER6H,  CSR_MHPMCOUNTER7H,
        CSR_MHPMCOUNTER8H,  CSR_MHPMCOUNTER9H,  CSR_MHPMCOUNTER10H, CSR_MHPMCOUNTER11H,
        CSR_MHPMCOUNTER12H, CSR_MHPMCOUNTER13H, CSR_MHPMCOUNTER14H, CSR_MHPMCOUNTER15H,
        CSR_MHPMCOUNTER16H, CSR_MHPMCOUNTER17H, CSR_MHPMCOUNTER18H, CSR_MHPMCOUNTER19H,
        CSR_MHPMCOUNTER20H, CSR_MHPMCOUNTER21H, CSR_MHPMCOUNTER22H, CSR_MHPMCOUNTER23H,
        CSR_MHPMCOUNTER24H, CSR_MHPMCOUNTER25H, CSR_MHPMCOUNTER26H, CSR_MHPMCOUNTER27H,
        CSR_MHPMCOUNTER28H, CSR_MHPMCOUNTER29H, CSR_MHPMCOUNTER30H, CSR_MHPMCOUNTER31H: begin
          mhpmcounterh_we[mhpmcounter_idx] = 1'b1;
        end

        default:;
      endcase
    end

    // exception controller gets priority over other writes
    unique case (1'b1)

      csr_save_cause_i: begin
        unique case (1'b1)
          csr_save_if_i: begin
            exception_pc = pc_if_i;
          end
          csr_save_id_i: begin
            exception_pc = pc_id_i;
          end
          default:;
        endcase

        // Any exception, including debug mode, causes a switch to M-mode
        priv_lvl_d = PRIV_LVL_M;

        if (debug_csr_save_i) begin
          // all interrupts are masked
          // do not update cause, epc, tval, epc and status
          dcsr_d.prv   = priv_lvl_q;
          dcsr_d.cause = debug_cause_i;
          depc_d       = exception_pc;
        end else if (!debug_mode_i) begin
          // In debug mode, "exceptions do not update any registers. That
          // includes cause, epc, tval, dpc and mstatus." [Debug Spec v0.13.2, p.39]
          mtval_d        = csr_mtval_i;
          mstatus_d.mie  = 1'b0; // disable interrupts
          // save current status
          mstatus_d.mpie = mstatus_q.mie;
          mstatus_d.mpp  = priv_lvl_q;
          mepc_d         = exception_pc;
          mcause_d       = {csr_mcause_i};
          // save previous status for recoverable NMI
          mstack_d.mpie  = mstatus_q.mpie;
          mstack_d.mpp   = mstatus_q.mpp;
          mstack_epc_d   = mepc_q;
          mstack_cause_d = mcause_q;
        end
      end // csr_save_cause_i

      csr_restore_dret_i: begin // DRET
        priv_lvl_d = dcsr_q.prv;
      end // csr_restore_dret_i

      csr_restore_mret_i: begin // MRET
        priv_lvl_d     = mstatus_q.mpp;
        mstatus_d.mie  = mstatus_q.mpie; // re-enable interrupts

        if (nmi_mode_i) begin
          // when returning from an NMI restore state from mstack CSR
          mstatus_d.mpie = mstack_q.mpie;
          mstatus_d.mpp  = mstack_q.mpp;
          mepc_d         = mstack_epc_q;
          mcause_d       = mstack_cause_q;
        end else begin
          // otherwise just set mstatus.MPIE/MPP
          // See RISC-V Privileged Specification, version 1.11, Section 3.1.6.1
          mstatus_d.mpie = 1'b1;
          mstatus_d.mpp  = PRIV_LVL_U;
        end
      end // csr_restore_mret_i

      default:;
    endcase
  end

  // CSR operation logic
  always_comb begin
    csr_wreq = 1'b1;

    unique case (csr_op_i)
      CSR_OP_WRITE: csr_wdata_int =  csr_wdata_i;
      CSR_OP_SET:   csr_wdata_int =  csr_wdata_i | csr_rdata_o;
      CSR_OP_CLEAR: csr_wdata_int = ~csr_wdata_i & csr_rdata_o;
      CSR_OP_READ: begin
        csr_wdata_int = csr_wdata_i;
        csr_wreq      = 1'b0;
      end
      default: begin
        csr_wdata_int = csr_wdata_i;
        csr_wreq      = 1'b0;
      end
    endcase
  end

  // only write CSRs during one clock cycle
  assign csr_we_int  = csr_wreq & ~illegal_csr_insn_o & instr_new_id_i;

  assign csr_rdata_o = csr_rdata_int;

  // directly output some registers
  assign csr_mepc_o  = mepc_q;
  assign csr_depc_o  = depc_q;
  assign csr_mtvec_o = mtvec_q;

  assign csr_mstatus_mie_o   = mstatus_q.mie;
  assign csr_mstatus_tw_o    = mstatus_q.tw;
  assign debug_single_step_o = dcsr_q.step;
  assign debug_ebreakm_o     = dcsr_q.ebreakm;
  assign debug_ebreaku_o     = dcsr_q.ebreaku;

  // Qualify incoming interrupt requests in mip CSR with mie CSR for controller and to re-enable
  // clock upon WFI (must be purely combinational).
  assign irqs_o        = mip & mie_q;
  assign irq_pending_o = |irqs_o;

  // actual registers
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      priv_lvl_q     <= PRIV_LVL_M;
      mstatus_q      <= '{
          mie:  1'b0,
          mpie: 1'b1,
          mpp:  PRIV_LVL_U,
          mprv: 1'b0,
          tw:   1'b0
      };
      mie_q          <= '0;
      mscratch_q     <= '0;
      mepc_q         <= '0;
      mcause_q       <= '0;
      mtval_q        <= '0;
      mtvec_q        <= 32'b01;
      dcsr_q         <= '{
          xdebugver: XDEBUGVER_STD,
          cause:     DBG_CAUSE_NONE, // 3'h0
          prv:       PRIV_LVL_M,
          default:   '0
      };
      depc_q         <= '0;
      dscratch0_q    <= '0;
      dscratch1_q    <= '0;

      mstack_q       <= '{
          mpie: 1'b1,
          mpp:  PRIV_LVL_U
      };
      mstack_epc_q   <= '0;
      mstack_cause_q <= '0;

    end else begin
      // update CSRs
      priv_lvl_q     <= priv_lvl_d;
      mstatus_q      <= mstatus_d;
      mie_q          <= mie_d;
      mscratch_q     <= mscratch_d;
      mepc_q         <= mepc_d;
      mcause_q       <= mcause_d;
      mtval_q        <= mtval_d;
      mtvec_q        <= mtvec_d;
      dcsr_q         <= dcsr_d;
      depc_q         <= depc_d;
      dscratch0_q    <= dscratch0_d;
      dscratch1_q    <= dscratch1_d;

      mstack_q       <= mstack_d;
      mstack_epc_q   <= mstack_epc_d;
      mstack_cause_q <= mstack_cause_d;

    end
  end

  // Send current priv level to the decoder
  assign priv_mode_id_o = priv_lvl_q;
  // New instruction fetches need to account for updates to priv_lvl_q this cycle
  assign priv_mode_if_o = priv_lvl_d;
  // Load/store instructions must factor in MPRV for PMP checking
  assign priv_mode_lsu_o = mstatus_q.mprv ? mstatus_q.mpp : priv_lvl_q;

  // -----------------
  // PMP registers
  // -----------------

  if (PMPEnable) begin : g_pmp_registers
    pmp_cfg_t                    pmp_cfg         [PMPNumRegions];
    pmp_cfg_t                    pmp_cfg_wdata   [PMPNumRegions];
    logic [31:0]                 pmp_addr        [PMPNumRegions];
    logic [PMPNumRegions-1:0]    pmp_cfg_we;
    logic [PMPNumRegions-1:0]    pmp_addr_we;

    // Expanded / qualified register read data
    for (genvar i = 0; i < PMP_MAX_REGIONS; i++) begin : g_exp_rd_data
      if (i < PMPNumRegions) begin : g_implemented_regions
        // Add in zero padding for reserved fields
        assign pmp_cfg_rdata[i] = {pmp_cfg[i].lock, 2'b00, pmp_cfg[i].mode,
                                   pmp_cfg[i].exec, pmp_cfg[i].write, pmp_cfg[i].read};

        // Address field read data depends on the current programmed mode and the granularity
        // See RISC-V Privileged Specification, version 1.11, Section 3.6.1
        if (PMPGranularity == 0) begin : g_pmp_g0
          // If G == 0, read data is unmodified
          assign pmp_addr_rdata[i] = pmp_addr[i];

        end else if (PMPGranularity == 1) begin : g_pmp_g1
          // If G == 1, bit [G-1] reads as zero in TOR or OFF mode
          always_comb begin
            pmp_addr_rdata[i] = pmp_addr[i];
            if ((pmp_cfg[i].mode == PMP_MODE_OFF) || (pmp_cfg[i].mode == PMP_MODE_TOR)) begin
              pmp_addr_rdata[i][PMPGranularity-1:0] = '0;
            end
          end

        end else begin : g_pmp_g2
          // For G >= 2, bits are masked to one or zero depending on the mode
          always_comb begin
            pmp_addr_rdata[i] = pmp_addr[i];
            if ((pmp_cfg[i].mode == PMP_MODE_OFF) || (pmp_cfg[i].mode == PMP_MODE_TOR)) begin
              // In TOR or OFF mode, bits [G-1:0] must read as zero
              pmp_addr_rdata[i][PMPGranularity-1:0] = '0;
            end else if (pmp_cfg[i].mode == PMP_MODE_NAPOT) begin
              // In NAPOT mode, bits [G-2:0] must read as one
              pmp_addr_rdata[i][PMPGranularity-2:0] = '1;
            end
          end
        end

      end else begin : g_other_regions
        // Non-implemented regions read as zero
        assign pmp_cfg_rdata[i]  = '0;
        assign pmp_addr_rdata[i] = '0;
      end
    end

    // Write data calculation
    for (genvar i = 0; i < PMPNumRegions; i++) begin : g_pmp_csrs
      // -------------------------
      // Instantiate cfg registers
      // -------------------------
      assign pmp_cfg_we[i] = csr_we_int & ~pmp_cfg[i].lock &
                             (csr_addr == (CSR_OFF_PMP_CFG + (i[11:0] >> 2)));

      // Select the correct WDATA (each CSR contains 4 CFG fields, each with 2 RES bits)
      assign pmp_cfg_wdata[i].lock  = csr_wdata_int[(i%4)*PMP_CFG_W+7];
      // NA4 mode is not selectable when G > 0, mode is treated as OFF
      always_comb begin
        unique case (csr_wdata_int[(i%4)*PMP_CFG_W+3+:2])
          2'b00   : pmp_cfg_wdata[i].mode = PMP_MODE_OFF;
          2'b01   : pmp_cfg_wdata[i].mode = PMP_MODE_TOR;
          2'b10   : pmp_cfg_wdata[i].mode = (PMPGranularity == 0) ? PMP_MODE_NA4:
                                                                    PMP_MODE_OFF;
          2'b11   : pmp_cfg_wdata[i].mode = PMP_MODE_NAPOT;
          default : pmp_cfg_wdata[i].mode = PMP_MODE_OFF;
        endcase
      end
      assign pmp_cfg_wdata[i].exec  = csr_wdata_int[(i%4)*PMP_CFG_W+2];
      // W = 1, R = 0 is a reserved combination. For now, we force W to 0 if R == 0
      assign pmp_cfg_wdata[i].write = &csr_wdata_int[(i%4)*PMP_CFG_W+:2];
      assign pmp_cfg_wdata[i].read  = csr_wdata_int[(i%4)*PMP_CFG_W];

      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          pmp_cfg[i] <= pmp_cfg_t'('b0);
        end else if (pmp_cfg_we[i]) begin
          pmp_cfg[i] <= pmp_cfg_wdata[i];
        end
      end

      // --------------------------
      // Instantiate addr registers
      // --------------------------
      if (i < PMPNumRegions - 1) begin : g_lower
        assign pmp_addr_we[i] = csr_we_int & ~pmp_cfg[i].lock &
                                (pmp_cfg[i+1].mode != PMP_MODE_TOR) &
                                (csr_addr == (CSR_OFF_PMP_ADDR + i[11:0]));
      end else begin : g_upper
        assign pmp_addr_we[i] = csr_we_int & ~pmp_cfg[i].lock &
                                (csr_addr == (CSR_OFF_PMP_ADDR + i[11:0]));
      end

      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          pmp_addr[i] <= 'b0;
        end else if (pmp_addr_we[i]) begin
          pmp_addr[i] <= csr_wdata_int;
        end
      end
      assign csr_pmp_cfg_o[i]  = pmp_cfg[i];
      assign csr_pmp_addr_o[i] = {pmp_addr[i],2'b00};
    end

  end else begin : g_no_pmp_tieoffs
    // Generate tieoffs when PMP is not configured
    for (genvar i = 0; i < PMP_MAX_REGIONS; i++) begin : g_rdata
      assign pmp_addr_rdata[i] = '0;
      assign pmp_cfg_rdata[i]  = '0;
    end
    for (genvar i = 0; i < PMPNumRegions; i++) begin : g_outputs
      assign csr_pmp_cfg_o[i]  = pmp_cfg_t'(1'b0);
      assign csr_pmp_addr_o[i] = '0;
    end
  end

  //////////////////////////
  //  Performance monitor //
  //////////////////////////

  // update enable signals
  always_comb begin : mcountinhibit_update
    if (mcountinhibit_we == 1'b1) begin
      mcountinhibit_d = {csr_wdata_int[MHPMCounterNum+2:2], 1'b0, csr_wdata_int[0]}; // bit 1 must always be 0
    end else begin
      mcountinhibit_d = mcountinhibit_q;
    end
  end

  // event selection (hardwired) & control
  always_comb begin : gen_mhpmcounter_incr

    // When adding or altering performance counter meanings and default
    // mappings please update dv/verilator/pcount/cpp/ibex_pcounts.cc
    // appropriately.
    //
    // active counters
    mhpmcounter_incr[0]  = 1'b1;                   // mcycle
    mhpmcounter_incr[1]  = 1'b0;                   // reserved
    mhpmcounter_incr[2]  = instr_ret_i;            // minstret
    mhpmcounter_incr[3]  = lsu_busy_i;             // cycles waiting for data memory
    mhpmcounter_incr[4]  = imiss_i & ~pc_set_i;    // cycles waiting for instr fetches
                                                   // excl. jump and branch set cycles
    mhpmcounter_incr[5]  = mem_load_i;             // num of loads
    mhpmcounter_incr[6]  = mem_store_i;            // num of stores
    mhpmcounter_incr[7]  = jump_i;                 // num of jumps (unconditional)
    mhpmcounter_incr[8]  = branch_i;               // num of branches (conditional)
    mhpmcounter_incr[9]  = branch_taken_i;         // num of taken branches (conditional)
    mhpmcounter_incr[10] = instr_ret_compressed_i; // num of compressed instr

    // inactive counters
    for (int unsigned i=3+MHPMCounterNum; i<32; i++) begin : gen_mhpmcounter_incr_inactive
      mhpmcounter_incr[i] = 1'b0;
    end
  end

  // event selector (hardwired, 0 means no event)
  always_comb begin : gen_mhpmevent

    // activate all
    for (int i=0; i<32; i++) begin : gen_mhpmevent_active
      mhpmevent[i]    =   '0;
      mhpmevent[i][i] = 1'b1;
    end

    // deactivate
    mhpmevent[1] = '0; // not existing, reserved
    for (int unsigned i=3+MHPMCounterNum; i<32; i++) begin : gen_mhpmevent_inactive
      mhpmevent[i] = '0;
    end
  end

  // update
  always_comb begin : mhpmcounter_update
    mhpmcounter_d = mhpmcounter;

    for (int i=0; i<32; i++) begin : gen_mhpmcounter_update

      // increment
      if (mhpmcounter_incr[i] & ~mcountinhibit[i]) begin
        mhpmcounter_d[i] = mhpmcounter[i] + 64'h1;
      end

      // write
      if (mhpmcounter_we[i]) begin
        mhpmcounter_d[i][31: 0] = csr_wdata_int;
      end else if (mhpmcounterh_we[i]) begin
        mhpmcounter_d[i][63:32] = csr_wdata_int;
      end
    end
  end

  // Performance monitor registers
  // Only elaborate flops that are needed from the given MHPMCounterWidth and MHPMCounterNum
  // parameters
  for (genvar i = 0; i < 32; i++) begin : g_mhpmcounter
    // First 3 counters (cycle, time, instret) must always be elaborated
    if (i < 3 + MHPMCounterNum) begin : g_mhpmcounter_exists
      // First 3 counters must be 64-bit the rest have parameterisable width
      localparam int unsigned IMHPMCounterWidth = i < 3 ? 64 : MHPMCounterWidth;

      logic [IMHPMCounterWidth-1:0] mhpmcounter_q;

      always @(posedge clk_i or negedge rst_ni) begin
        if(~rst_ni) begin
          mhpmcounter_q <= '0;
        end else begin
          mhpmcounter_q <= mhpmcounter_d[i][IMHPMCounterWidth-1:0];
        end
      end

      if (IMHPMCounterWidth < 64) begin : g_mhpmcounter_narrow
        assign mhpmcounter[i][IMHPMCounterWidth-1:0] = mhpmcounter_q;
        assign mhpmcounter[i][63:IMHPMCounterWidth]  = '0;
      end else begin : g_mhpmcounter_full
        assign mhpmcounter[i] = mhpmcounter_q;
      end
    end else begin : g_no_mhpmcounter
      assign mhpmcounter[i] = '0;
    end
  end

  if(MHPMCounterNum < 29) begin : g_mcountinhibit_reduced
    assign mcountinhibit = {{29-MHPMCounterNum{1'b1}}, mcountinhibit_q};
  end else begin : g_mcountinhibit_full
    assign mcountinhibit = mcountinhibit_q;
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      mcountinhibit_q <= '0;
    end else begin
      mcountinhibit_q <= mcountinhibit_d;
    end
  end

  /////////////////////////////
  // Debug trigger registers //
  /////////////////////////////

  if (DbgTriggerEn) begin : gen_trigger_regs
    // Register values
    logic        tmatch_control_d, tmatch_control_q;
    logic [31:0] tmatch_value_d, tmatch_value_q;
    // Write enables
    logic tmatch_control_we;
    logic tmatch_value_we;

    // Write select
    assign tmatch_control_we = csr_we_int & debug_mode_i & (csr_addr_i == CSR_TDATA1);
    assign tmatch_value_we   = csr_we_int & debug_mode_i & (csr_addr_i == CSR_TDATA2);

    // tmatch_control is enabled when the execute bit is set
    assign tmatch_control_d = tmatch_control_we ? csr_wdata_int[2] :
                                                  tmatch_control_q;
    // tmatch_value has its own clock gate
    assign tmatch_value_d   = csr_wdata_int[31:0];

    // Registers
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        tmatch_control_q <= 'b0;
      end else begin
        tmatch_control_q <= tmatch_control_d;
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        tmatch_value_q <= 'b0;
      end else if (tmatch_value_we) begin
        tmatch_value_q <= tmatch_value_d;
      end
    end

    // Assign read data
    // TSELECT - only one supported
    assign tselect_rdata = 'b0;
    // TDATA0 - only support simple address matching
    assign tmatch_control_rdata = {4'h2,              // type    : address/data match
                                   1'b1,              // dmode   : access from D mode only
                                   6'h00,             // maskmax : exact match only
                                   1'b0,              // hit     : not supported
                                   1'b0,              // select  : address match only
                                   1'b0,              // timing  : match before execution
                                   2'b00,             // sizelo  : match any access
                                   4'h1,              // action  : enter debug mode
                                   1'b0,              // chain   : not supported
                                   4'h0,              // match   : simple match
                                   1'b1,              // m       : match in m-mode
                                   1'b0,              // 0       : zero
                                   1'b0,              // s       : not supported
                                   1'b1,              // u       : match in u-mode
                                   tmatch_control_q,  // execute : match instruction address
                                   1'b0,              // store   : not supported
                                   1'b0};             // load    : not supported
    // TDATA1 - address match value only
    assign tmatch_value_rdata = tmatch_value_q;

    // Breakpoint matching
    // We match against the next address, as the breakpoint must be taken before execution
    assign trigger_match_o = tmatch_control_q & (pc_if_i[31:0] == tmatch_value_q[31:0]);

  end else begin : gen_no_trigger_regs
    assign tselect_rdata        = 'b0;
    assign tmatch_control_rdata = 'b0;
    assign tmatch_value_rdata   = 'b0;
    assign trigger_match_o      = 'b0;
  end

  ////////////////
  // Assertions //
  ////////////////

  // Selectors must be known/valid.
  `ASSERT(IbexCsrOpValid, csr_op_i inside {
      CSR_OP_READ,
      CSR_OP_WRITE,
      CSR_OP_SET,
      CSR_OP_CLEAR
      }, clk_i, !rst_ni)
  `ASSERT_KNOWN(IbexCsrWdataIntKnown, csr_wdata_int, clk_i, !rst_ni)

endmodule
