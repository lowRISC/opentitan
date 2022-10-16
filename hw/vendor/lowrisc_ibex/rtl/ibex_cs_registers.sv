// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * Control and Status Registers
 */

`include "prim_assert.sv"

module ibex_cs_registers #(
  parameter bit               DbgTriggerEn      = 0,
  parameter int unsigned      DbgHwBreakNum     = 1,
  parameter bit               DataIndTiming     = 1'b0,
  parameter bit               DummyInstructions = 1'b0,
  parameter bit               ShadowCSR         = 1'b0,
  parameter bit               ICache            = 1'b0,
  parameter int unsigned      MHPMCounterNum    = 10,
  parameter int unsigned      MHPMCounterWidth  = 40,
  parameter bit               PMPEnable         = 0,
  parameter int unsigned      PMPGranularity    = 0,
  parameter int unsigned      PMPNumRegions     = 4,
  parameter bit               RV32E             = 0,
  parameter ibex_pkg::rv32m_e RV32M             = ibex_pkg::RV32MFast,
  parameter ibex_pkg::rv32b_e RV32B             = ibex_pkg::RV32BNone
) (
  // Clock and Reset
  input  logic                 clk_i,
  input  logic                 rst_ni,

  // Hart ID
  input  logic [31:0]          hart_id_i,

  // Privilege mode
  output ibex_pkg::priv_lvl_e  priv_mode_id_o,
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
  input                        csr_op_en_i,
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
  output logic [31:0]          csr_mtval_o,

  // PMP
  output ibex_pkg::pmp_cfg_t     csr_pmp_cfg_o  [PMPNumRegions],
  output logic [33:0]            csr_pmp_addr_o [PMPNumRegions],
  output ibex_pkg::pmp_mseccfg_t csr_pmp_mseccfg_o,

  // debug
  input  logic                 debug_mode_i,
  input  logic                 debug_mode_entering_i,
  input  ibex_pkg::dbg_cause_e debug_cause_i,
  input  logic                 debug_csr_save_i,
  output logic [31:0]          csr_depc_o,
  output logic                 debug_single_step_o,
  output logic                 debug_ebreakm_o,
  output logic                 debug_ebreaku_o,
  output logic                 trigger_match_o,

  input  logic [31:0]          pc_if_i,
  input  logic [31:0]          pc_id_i,
  input  logic [31:0]          pc_wb_i,

  // CPU control and status bits
  output logic                 data_ind_timing_o,
  output logic                 dummy_instr_en_o,
  output logic [2:0]           dummy_instr_mask_o,
  output logic                 dummy_instr_seed_en_o,
  output logic [31:0]          dummy_instr_seed_o,
  output logic                 icache_enable_o,
  output logic                 csr_shadow_err_o,
  input  logic                 ic_scr_key_valid_i,

  // Exception save/restore
  input  logic                 csr_save_if_i,
  input  logic                 csr_save_id_i,
  input  logic                 csr_save_wb_i,
  input  logic                 csr_restore_mret_i,
  input  logic                 csr_restore_dret_i,
  input  logic                 csr_save_cause_i,
  input  ibex_pkg::exc_cause_t csr_mcause_i,
  input  logic [31:0]          csr_mtval_i,
  output logic                 illegal_csr_insn_o,     // access to non-existent CSR,
                                                        // with wrong priviledge level, or
                                                        // missing write permissions
  output logic                 double_fault_seen_o,
  // Performance Counters
  input  logic                 instr_ret_i,                 // instr retired in ID/EX stage
  input  logic                 instr_ret_compressed_i,      // compressed instr retired
  input  logic                 instr_ret_spec_i,            // speculative instr_ret_i
  input  logic                 instr_ret_compressed_spec_i, // speculative instr_ret_compressed_i
  input  logic                 iside_wait_i,                // core waiting for the iside
  input  logic                 jump_i,                      // jump instr seen (j, jr, jal, jalr)
  input  logic                 branch_i,                    // branch instr seen (bf, bnf)
  input  logic                 branch_taken_i,              // branch was taken
  input  logic                 mem_load_i,                  // load from memory in this cycle
  input  logic                 mem_store_i,                 // store to memory in this cycle
  input  logic                 dside_wait_i,                // core waiting for the dside
  input  logic                 mul_wait_i,                  // core waiting for multiply
  input  logic                 div_wait_i                   // core waiting for divide
);

  import ibex_pkg::*;

  // Is a PMP config a locked one that allows M-mode execution when MSECCFG.MML is set (either
  // M mode alone or shared M/U mode execution)?
  function automatic logic is_mml_m_exec_cfg(ibex_pkg::pmp_cfg_t pmp_cfg);
    logic unused_cfg;
    unused_cfg = ^{pmp_cfg.mode};

    if (pmp_cfg.lock) begin
      unique case ({pmp_cfg.read, pmp_cfg.write, pmp_cfg.exec})
        3'b001, 3'b010, 3'b011, 3'b101: return 1'b1;
        default: return 1'b0;
      endcase
    end

    return 1'b0;
  endfunction

  localparam int unsigned RV32BExtra = (RV32B == RV32BOTEarlGrey) || (RV32B == RV32BFull) ? 1 : 0;
  localparam int unsigned RV32MEnabled = (RV32M == RV32MNone) ? 0 : 1;
  localparam int unsigned PMPAddrWidth = (PMPGranularity > 0) ? 33 - PMPGranularity : 32;

  // misa
  localparam logic [31:0] MISA_VALUE =
      (0                 <<  0)  // A - Atomic Instructions extension
    | (0                 <<  1)  // B - Bit-Manipulation extension
    | (1                 <<  2)  // C - Compressed extension
    | (0                 <<  3)  // D - Double precision floating-point extension
    | (32'(RV32E)        <<  4)  // E - RV32E base ISA
    | (0                 <<  5)  // F - Single precision floating-point extension
    | (32'(!RV32E)       <<  8)  // I - RV32I/64I/128I base ISA
    | (RV32MEnabled      << 12)  // M - Integer Multiply/Divide extension
    | (0                 << 13)  // N - User level interrupts supported
    | (0                 << 18)  // S - Supervisor mode implemented
    | (1                 << 20)  // U - User mode implemented
    | (RV32BExtra        << 23)  // X - Non-standard extensions present
    | (32'(CSR_MISA_MXL) << 30); // M-XLEN

  typedef struct packed {
    logic      mie;
    logic      mpie;
    priv_lvl_e mpp;
    logic      mprv;
    logic      tw;
  } status_t;

  typedef struct packed {
    logic      mpie;
    priv_lvl_e mpp;
  } status_stk_t;

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
  } dcsr_t;

  // Partial CPU control and status register fields
  // ICache scramble key valid (ic_scr_key_valid) is registered seperately to this struct. This is
  // because it is sampled from the top-level every cycle whilst the other fields only change
  // occasionally.
  typedef struct packed {
    logic        double_fault_seen;
    logic        sync_exc_seen;
    logic [2:0]  dummy_instr_mask;
    logic        dummy_instr_en;
    logic        data_ind_timing;
    logic        icache_enable;
  } cpu_ctrl_sts_part_t;

  // Interrupt and exception control signals
  logic [31:0] exception_pc;

  // CSRs
  priv_lvl_e   priv_lvl_q, priv_lvl_d;
  status_t     mstatus_q, mstatus_d;
  logic        mstatus_err;
  logic        mstatus_en;
  irqs_t       mie_q, mie_d;
  logic        mie_en;
  logic [31:0] mscratch_q;
  logic        mscratch_en;
  logic [31:0] mepc_q, mepc_d;
  logic        mepc_en;
  exc_cause_t  mcause_q, mcause_d;
  logic        mcause_en;
  logic [31:0] mtval_q, mtval_d;
  logic        mtval_en;
  logic [31:0] mtvec_q, mtvec_d;
  logic        mtvec_err;
  logic        mtvec_en;
  irqs_t       mip;
  dcsr_t       dcsr_q, dcsr_d;
  logic        dcsr_en;
  logic [31:0] depc_q, depc_d;
  logic        depc_en;
  logic [31:0] dscratch0_q;
  logic [31:0] dscratch1_q;
  logic        dscratch0_en, dscratch1_en;

  // CSRs for recoverable NMIs
  // NOTE: these CSRS are nonstandard, see https://github.com/riscv/riscv-isa-manual/issues/261
  status_stk_t mstack_q, mstack_d;
  logic        mstack_en;
  logic [31:0] mstack_epc_q, mstack_epc_d;
  exc_cause_t  mstack_cause_q, mstack_cause_d;

  // PMP Signals
  logic [31:0]                 pmp_addr_rdata  [PMP_MAX_REGIONS];
  logic [PMP_CFG_W-1:0]        pmp_cfg_rdata   [PMP_MAX_REGIONS];
  logic                        pmp_csr_err;
  pmp_mseccfg_t                pmp_mseccfg;

  // Hardware performance monitor signals
  logic [31:0]                 mcountinhibit;
  // Only have mcountinhibit flops for counters that actually exist
  logic [MHPMCounterNum+3-1:0] mcountinhibit_d, mcountinhibit_q;
  logic                        mcountinhibit_we;

  // mhpmcounter flops are elaborated below providing only the precise number that is required based
  // on MHPMCounterNum/MHPMCounterWidth. This signal connects to the Q output of these flops
  // where they exist and is otherwise 0.
  logic [63:0] mhpmcounter [32];
  logic [31:0] mhpmcounter_we;
  logic [31:0] mhpmcounterh_we;
  logic [31:0] mhpmcounter_incr;
  logic [31:0] mhpmevent [32];
  logic  [4:0] mhpmcounter_idx;
  logic        unused_mhpmcounter_we_1;
  logic        unused_mhpmcounterh_we_1;
  logic        unused_mhpmcounter_incr_1;

  logic [63:0] minstret_next, minstret_raw;

  // Debug / trigger registers
  logic [31:0] tselect_rdata;
  logic [31:0] tmatch_control_rdata;
  logic [31:0] tmatch_value_rdata;

  // CPU control bits
  cpu_ctrl_sts_part_t cpuctrlsts_part_q, cpuctrlsts_part_d;
  cpu_ctrl_sts_part_t cpuctrlsts_part_wdata_raw, cpuctrlsts_part_wdata;
  logic               cpuctrlsts_part_we;
  logic               cpuctrlsts_part_err;

  logic cpuctrlsts_ic_scr_key_valid_q;
  logic cpuctrlsts_ic_scr_key_err;

  // CSR update logic
  logic [31:0] csr_wdata_int;
  logic [31:0] csr_rdata_int;
  logic        csr_we_int;
  logic        csr_wr;

  // Access violation signals
  logic        dbg_csr;
  logic        illegal_csr;
  logic        illegal_csr_priv;
  logic        illegal_csr_dbg;
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

  assign illegal_csr_dbg    = dbg_csr & ~debug_mode_i;
  assign illegal_csr_priv   = (csr_addr[9:8] > {priv_lvl_q});
  assign illegal_csr_write  = (csr_addr[11:10] == 2'b11) && csr_wr;
  assign illegal_csr_insn_o = csr_access_i & (illegal_csr | illegal_csr_write | illegal_csr_priv |
                                              illegal_csr_dbg);

  // mip CSR is purely combinational - must be able to re-enable the clock upon WFI
  assign mip.irq_software = irq_software_i;
  assign mip.irq_timer    = irq_timer_i;
  assign mip.irq_external = irq_external_i;
  assign mip.irq_fast     = irq_fast_i;

  // read logic
  always_comb begin
    csr_rdata_int = '0;
    illegal_csr   = 1'b0;
    dbg_csr       = 1'b0;

    unique case (csr_addr_i)
      // mvendorid: encoding of manufacturer/provider
      CSR_MVENDORID: csr_rdata_int = CSR_MVENDORID_VALUE;
      // marchid: encoding of base microarchitecture
      CSR_MARCHID: csr_rdata_int = CSR_MARCHID_VALUE;
      // mimpid: encoding of processor implementation version
      CSR_MIMPID: csr_rdata_int = CSR_MIMPID_VALUE;
      // mhartid: unique hardware thread id
      CSR_MHARTID: csr_rdata_int = hart_id_i;
      // mconfigptr: pointer to configuration data structre
      CSR_MCONFIGPTR: csr_rdata_int = CSR_MCONFIGPTR_VALUE;

      // mstatus: always M-mode, contains IE bit
      CSR_MSTATUS: begin
        csr_rdata_int                                                   = '0;
        csr_rdata_int[CSR_MSTATUS_MIE_BIT]                              = mstatus_q.mie;
        csr_rdata_int[CSR_MSTATUS_MPIE_BIT]                             = mstatus_q.mpie;
        csr_rdata_int[CSR_MSTATUS_MPP_BIT_HIGH:CSR_MSTATUS_MPP_BIT_LOW] = mstatus_q.mpp;
        csr_rdata_int[CSR_MSTATUS_MPRV_BIT]                             = mstatus_q.mprv;
        csr_rdata_int[CSR_MSTATUS_TW_BIT]                               = mstatus_q.tw;
      end

      // mstatush: All zeros for Ibex (fixed little endian and all other bits reserved)
      CSR_MSTATUSH: csr_rdata_int = '0;

      // menvcfg: machine environment configuration, all zeros for Ibex (none of the relevant
      // features are implemented)
      CSR_MENVCFG, CSR_MENVCFGH: csr_rdata_int = '0;

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

      // mcounteren: machine counter enable
      CSR_MCOUNTEREN: begin
        csr_rdata_int = '0;
      end

      CSR_MSCRATCH: csr_rdata_int = mscratch_q;

      // mtvec: trap-vector base address
      CSR_MTVEC: csr_rdata_int = mtvec_q;

      // mepc: exception program counter
      CSR_MEPC: csr_rdata_int = mepc_q;

      // mcause: exception cause
      CSR_MCAUSE: csr_rdata_int = {mcause_q.irq_ext | mcause_q.irq_int,
                                   mcause_q.irq_int ? {26{1'b1}} : 26'b0,
                                   mcause_q.lower_cause[4:0]};

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

      CSR_MSECCFG: begin
        if (PMPEnable) begin
          csr_rdata_int                       = '0;
          csr_rdata_int[CSR_MSECCFG_MML_BIT]  = pmp_mseccfg.mml;
          csr_rdata_int[CSR_MSECCFG_MMWP_BIT] = pmp_mseccfg.mmwp;
          csr_rdata_int[CSR_MSECCFG_RLB_BIT]  = pmp_mseccfg.rlb;
        end else begin
          illegal_csr = 1'b1;
        end
      end

      CSR_MSECCFGH: begin
        if (PMPEnable) begin
          csr_rdata_int = '0;
        end else begin
          illegal_csr = 1'b1;
        end
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
        dbg_csr       = 1'b1;
      end
      CSR_DPC: begin
        csr_rdata_int = depc_q;
        dbg_csr       = 1'b1;
      end
      CSR_DSCRATCH0: begin
        csr_rdata_int = dscratch0_q;
        dbg_csr       = 1'b1;
      end
      CSR_DSCRATCH1: begin
        csr_rdata_int = dscratch1_q;
        dbg_csr       = 1'b1;
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
      CSR_MSCONTEXT: begin
        csr_rdata_int = '0;
        illegal_csr   = ~DbgTriggerEn;
      end

      // Custom CSR for controlling CPU features and reporting CPU status
      CSR_CPUCTRLSTS: begin
        csr_rdata_int = {{32 - $bits(cpu_ctrl_sts_part_t) - 1 {1'b0}},
                         cpuctrlsts_ic_scr_key_valid_q,
                         cpuctrlsts_part_q};
      end

      // Custom CSR for LFSR re-seeding (cannot be read)
      CSR_SECURESEED: begin
        csr_rdata_int = '0;
      end

      default: begin
        illegal_csr = 1'b1;
      end
    endcase

    if (!PMPEnable) begin
      if (csr_addr inside {CSR_PMPCFG0,   CSR_PMPCFG1,   CSR_PMPCFG2,   CSR_PMPCFG3,
                           CSR_PMPADDR0,  CSR_PMPADDR1,  CSR_PMPADDR2,  CSR_PMPADDR3,
                           CSR_PMPADDR4,  CSR_PMPADDR5,  CSR_PMPADDR6,  CSR_PMPADDR7,
                           CSR_PMPADDR8,  CSR_PMPADDR9,  CSR_PMPADDR10, CSR_PMPADDR11,
                           CSR_PMPADDR12, CSR_PMPADDR13, CSR_PMPADDR14, CSR_PMPADDR15}) begin
        illegal_csr = 1'b1;
      end
    end
  end

  // write logic
  always_comb begin
    exception_pc = pc_id_i;

    priv_lvl_d   = priv_lvl_q;
    mstatus_en   = 1'b0;
    mstatus_d    = mstatus_q;
    mie_en       = 1'b0;
    mscratch_en  = 1'b0;
    mepc_en      = 1'b0;
    mepc_d       = {csr_wdata_int[31:1], 1'b0};
    mcause_en    = 1'b0;
    mcause_d     = '{irq_ext :    csr_wdata_int[31:30] == 2'b10,
                     irq_int :    csr_wdata_int[31:30] == 2'b11,
                     lower_cause: csr_wdata_int[4:0]};
    mtval_en     = 1'b0;
    mtval_d      = csr_wdata_int;
    mtvec_en     = csr_mtvec_init_i;
    // mtvec.MODE set to vectored
    // mtvec.BASE must be 256-byte aligned
    mtvec_d      = csr_mtvec_init_i ? {boot_addr_i[31:8], 6'b0, 2'b01} :
                                      {csr_wdata_int[31:8], 6'b0, 2'b01};
    dcsr_en      = 1'b0;
    dcsr_d       = dcsr_q;
    depc_d       = {csr_wdata_int[31:1], 1'b0};
    depc_en      = 1'b0;
    dscratch0_en = 1'b0;
    dscratch1_en = 1'b0;

    mstack_en      = 1'b0;
    mstack_d.mpie  = mstatus_q.mpie;
    mstack_d.mpp   = mstatus_q.mpp;
    mstack_epc_d   = mepc_q;
    mstack_cause_d = mcause_q;

    mcountinhibit_we = 1'b0;
    mhpmcounter_we   = '0;
    mhpmcounterh_we  = '0;

    cpuctrlsts_part_we = 1'b0;
    cpuctrlsts_part_d  = cpuctrlsts_part_q;

    double_fault_seen_o = 1'b0;

    if (csr_we_int) begin
      unique case (csr_addr_i)
        // mstatus: IE bit
        CSR_MSTATUS: begin
          mstatus_en = 1'b1;
          mstatus_d    = '{
              mie:  csr_wdata_int[CSR_MSTATUS_MIE_BIT],
              mpie: csr_wdata_int[CSR_MSTATUS_MPIE_BIT],
              mpp:  priv_lvl_e'(csr_wdata_int[CSR_MSTATUS_MPP_BIT_HIGH:CSR_MSTATUS_MPP_BIT_LOW]),
              mprv: csr_wdata_int[CSR_MSTATUS_MPRV_BIT],
              tw:   csr_wdata_int[CSR_MSTATUS_TW_BIT]
          };
          // Convert illegal values to U-mode
          if ((mstatus_d.mpp != PRIV_LVL_M) && (mstatus_d.mpp != PRIV_LVL_U)) begin
            mstatus_d.mpp = PRIV_LVL_U;
          end
        end

        // interrupt enable
        CSR_MIE: mie_en = 1'b1;

        CSR_MSCRATCH: mscratch_en = 1'b1;

        // mepc: exception program counter
        CSR_MEPC: mepc_en = 1'b1;

        // mcause
        CSR_MCAUSE: mcause_en = 1'b1;

        // mtval: trap value
        CSR_MTVAL: mtval_en = 1'b1;

        // mtvec
        CSR_MTVEC: mtvec_en = 1'b1;

        CSR_DCSR: begin
          dcsr_d = csr_wdata_int;
          dcsr_d.xdebugver = XDEBUGVER_STD;
          // Change to PRIV_LVL_U if software writes an unsupported value
          if ((dcsr_d.prv != PRIV_LVL_M) && (dcsr_d.prv != PRIV_LVL_U)) begin
            dcsr_d.prv = PRIV_LVL_U;
          end

          // Read-only for SW
          dcsr_d.cause = dcsr_q.cause;

          // Interrupts always disabled during single stepping
          dcsr_d.stepie = 1'b0;

          // currently not supported:
          dcsr_d.nmip = 1'b0;
          dcsr_d.mprven = 1'b0;
          dcsr_d.stopcount = 1'b0;
          dcsr_d.stoptime = 1'b0;

          // forced to be zero
          dcsr_d.zero0 = 1'b0;
          dcsr_d.zero1 = 1'b0;
          dcsr_d.zero2 = 12'h0;
          dcsr_en      = 1'b1;
        end

        // dpc: debug program counter
        CSR_DPC: depc_en = 1'b1;

        CSR_DSCRATCH0: dscratch0_en = 1'b1;
        CSR_DSCRATCH1: dscratch1_en = 1'b1;

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

        CSR_CPUCTRLSTS: begin
          cpuctrlsts_part_d  = cpuctrlsts_part_wdata;
          cpuctrlsts_part_we = 1'b1;
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
          csr_save_wb_i: begin
            exception_pc = pc_wb_i;
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
          dcsr_en      = 1'b1;
          depc_d       = exception_pc;
          depc_en      = 1'b1;
        end else if (!debug_mode_i) begin
          // Exceptions do not update CSRs in debug mode, so ony write these CSRs if we're not in
          // debug mode.
          mtval_en       = 1'b1;
          mtval_d        = csr_mtval_i;
          mstatus_en     = 1'b1;
          mstatus_d.mie  = 1'b0; // disable interrupts
          // save current status
          mstatus_d.mpie = mstatus_q.mie;
          mstatus_d.mpp  = priv_lvl_q;
          mepc_en        = 1'b1;
          mepc_d         = exception_pc;
          mcause_en      = 1'b1;
          mcause_d       = csr_mcause_i;
          // save previous status for recoverable NMI
          mstack_en      = 1'b1;

          if (!(mcause_d.irq_ext || mcause_d.irq_int)) begin
            // SEC_CM: EXCEPTION.CTRL_FLOW.LOCAL_ESC
            // SEC_CM: EXCEPTION.CTRL_FLOW.GLOBAL_ESC
            cpuctrlsts_part_we = 1'b1;

            cpuctrlsts_part_d.sync_exc_seen = 1'b1;
            if (cpuctrlsts_part_q.sync_exc_seen) begin
              double_fault_seen_o                 = 1'b1;
              cpuctrlsts_part_d.double_fault_seen = 1'b1;
            end
          end
        end
      end // csr_save_cause_i

      csr_restore_dret_i: begin // DRET
        priv_lvl_d = dcsr_q.prv;
      end // csr_restore_dret_i

      csr_restore_mret_i: begin // MRET
        priv_lvl_d     = mstatus_q.mpp;
        mstatus_en     = 1'b1;
        mstatus_d.mie  = mstatus_q.mpie; // re-enable interrupts

        if (mstatus_q.mpp != PRIV_LVL_M) begin
          mstatus_d.mprv = 1'b0;
        end

        // SEC_CM: EXCEPTION.CTRL_FLOW.LOCAL_ESC
        // SEC_CM: EXCEPTION.CTRL_FLOW.GLOBAL_ESC
        cpuctrlsts_part_we              = 1'b1;
        cpuctrlsts_part_d.sync_exc_seen = 1'b0;

        if (nmi_mode_i) begin
          // when returning from an NMI restore state from mstack CSR
          mstatus_d.mpie = mstack_q.mpie;
          mstatus_d.mpp  = mstack_q.mpp;
          mepc_en        = 1'b1;
          mepc_d         = mstack_epc_q;
          mcause_en      = 1'b1;
          mcause_d       = mstack_cause_q;
        end else begin
          // otherwise just set mstatus.MPIE/MPP
          mstatus_d.mpie = 1'b1;
          mstatus_d.mpp  = PRIV_LVL_U;
        end
      end // csr_restore_mret_i

      default:;
    endcase
  end

  // Update current priv level
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      priv_lvl_q     <= PRIV_LVL_M;
    end else begin
      priv_lvl_q     <= priv_lvl_d;
    end
  end

  // Send current priv level to the decoder
  assign priv_mode_id_o = priv_lvl_q;
  // Load/store instructions must factor in MPRV for PMP checking
  assign priv_mode_lsu_o = mstatus_q.mprv ? mstatus_q.mpp : priv_lvl_q;

  // CSR operation logic
  always_comb begin
    unique case (csr_op_i)
      CSR_OP_WRITE: csr_wdata_int =  csr_wdata_i;
      CSR_OP_SET:   csr_wdata_int =  csr_wdata_i | csr_rdata_o;
      CSR_OP_CLEAR: csr_wdata_int = ~csr_wdata_i & csr_rdata_o;
      CSR_OP_READ:  csr_wdata_int = csr_wdata_i;
      default:      csr_wdata_int = csr_wdata_i;
    endcase
  end

  assign csr_wr = (csr_op_i inside {CSR_OP_WRITE, CSR_OP_SET, CSR_OP_CLEAR});

  // only write CSRs during one clock cycle
  assign csr_we_int  = csr_wr & csr_op_en_i & ~illegal_csr_insn_o;

  assign csr_rdata_o = csr_rdata_int;

  // directly output some registers
  assign csr_mepc_o  = mepc_q;
  assign csr_depc_o  = depc_q;
  assign csr_mtvec_o = mtvec_q;
  assign csr_mtval_o = mtval_q;

  assign csr_mstatus_mie_o   = mstatus_q.mie;
  assign csr_mstatus_tw_o    = mstatus_q.tw;
  assign debug_single_step_o = dcsr_q.step;
  assign debug_ebreakm_o     = dcsr_q.ebreakm;
  assign debug_ebreaku_o     = dcsr_q.ebreaku;

  // Qualify incoming interrupt requests in mip CSR with mie CSR for controller and to re-enable
  // clock upon WFI (must be purely combinational).
  assign irqs_o        = mip & mie_q;
  assign irq_pending_o = |irqs_o;

  ////////////////////////
  // CSR instantiations //
  ////////////////////////

  // MSTATUS
  localparam status_t MSTATUS_RST_VAL = '{mie:  1'b0,
                                          mpie: 1'b1,
                                          mpp:  PRIV_LVL_U,
                                          mprv: 1'b0,
                                          tw:   1'b0};
  ibex_csr #(
    .Width     ($bits(status_t)),
    .ShadowCopy(ShadowCSR),
    .ResetValue({MSTATUS_RST_VAL})
  ) u_mstatus_csr (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),
    .wr_data_i ({mstatus_d}),
    .wr_en_i   (mstatus_en),
    .rd_data_o (mstatus_q),
    .rd_error_o(mstatus_err)
  );

  // MEPC
  ibex_csr #(
    .Width     (32),
    .ShadowCopy(1'b0),
    .ResetValue('0)
  ) u_mepc_csr (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),
    .wr_data_i (mepc_d),
    .wr_en_i   (mepc_en),
    .rd_data_o (mepc_q),
    .rd_error_o()
  );

  // MIE
  assign mie_d.irq_software = csr_wdata_int[CSR_MSIX_BIT];
  assign mie_d.irq_timer    = csr_wdata_int[CSR_MTIX_BIT];
  assign mie_d.irq_external = csr_wdata_int[CSR_MEIX_BIT];
  assign mie_d.irq_fast     = csr_wdata_int[CSR_MFIX_BIT_HIGH:CSR_MFIX_BIT_LOW];
  ibex_csr #(
    .Width     ($bits(irqs_t)),
    .ShadowCopy(1'b0),
    .ResetValue('0)
  ) u_mie_csr (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),
    .wr_data_i ({mie_d}),
    .wr_en_i   (mie_en),
    .rd_data_o (mie_q),
    .rd_error_o()
  );

  // MSCRATCH
  ibex_csr #(
    .Width     (32),
    .ShadowCopy(1'b0),
    .ResetValue('0)
  ) u_mscratch_csr (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),
    .wr_data_i (csr_wdata_int),
    .wr_en_i   (mscratch_en),
    .rd_data_o (mscratch_q),
    .rd_error_o()
  );

  // MCAUSE
  ibex_csr #(
    .Width     ($bits(exc_cause_t)),
    .ShadowCopy(1'b0),
    .ResetValue('0)
  ) u_mcause_csr (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),
    .wr_data_i ({mcause_d}),
    .wr_en_i   (mcause_en),
    .rd_data_o (mcause_q),
    .rd_error_o()
  );

  // MTVAL
  ibex_csr #(
    .Width     (32),
    .ShadowCopy(1'b0),
    .ResetValue('0)
  ) u_mtval_csr (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),
    .wr_data_i (mtval_d),
    .wr_en_i   (mtval_en),
    .rd_data_o (mtval_q),
    .rd_error_o()
  );

  // MTVEC
  ibex_csr #(
    .Width     (32),
    .ShadowCopy(ShadowCSR),
    .ResetValue(32'd1)
  ) u_mtvec_csr (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),
    .wr_data_i (mtvec_d),
    .wr_en_i   (mtvec_en),
    .rd_data_o (mtvec_q),
    .rd_error_o(mtvec_err)
  );

  // DCSR
  localparam dcsr_t DCSR_RESET_VAL = '{
      xdebugver: XDEBUGVER_STD,
      cause: DBG_CAUSE_NONE,  // 3'h0
      prv: PRIV_LVL_M,
      default: '0
  };
  ibex_csr #(
    .Width     ($bits(dcsr_t)),
    .ShadowCopy(1'b0),
    .ResetValue({DCSR_RESET_VAL})
  ) u_dcsr_csr (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),
    .wr_data_i ({dcsr_d}),
    .wr_en_i   (dcsr_en),
    .rd_data_o (dcsr_q),
    .rd_error_o()
  );

  // DEPC
  ibex_csr #(
    .Width     (32),
    .ShadowCopy(1'b0),
    .ResetValue('0)
  ) u_depc_csr (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),
    .wr_data_i (depc_d),
    .wr_en_i   (depc_en),
    .rd_data_o (depc_q),
    .rd_error_o()
  );

  // DSCRATCH0
  ibex_csr #(
    .Width     (32),
    .ShadowCopy(1'b0),
    .ResetValue('0)
  ) u_dscratch0_csr (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),
    .wr_data_i (csr_wdata_int),
    .wr_en_i   (dscratch0_en),
    .rd_data_o (dscratch0_q),
    .rd_error_o()
  );

  // DSCRATCH1
  ibex_csr #(
    .Width     (32),
    .ShadowCopy(1'b0),
    .ResetValue('0)
  ) u_dscratch1_csr (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),
    .wr_data_i (csr_wdata_int),
    .wr_en_i   (dscratch1_en),
    .rd_data_o (dscratch1_q),
    .rd_error_o()
  );

  // MSTACK
  localparam status_stk_t MSTACK_RESET_VAL = '{mpie: 1'b1, mpp: PRIV_LVL_U};
  ibex_csr #(
    .Width     ($bits(status_stk_t)),
    .ShadowCopy(1'b0),
    .ResetValue({MSTACK_RESET_VAL})
  ) u_mstack_csr (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),
    .wr_data_i ({mstack_d}),
    .wr_en_i   (mstack_en),
    .rd_data_o (mstack_q),
    .rd_error_o()
  );

  // MSTACK_EPC
  ibex_csr #(
    .Width     (32),
    .ShadowCopy(1'b0),
    .ResetValue('0)
  ) u_mstack_epc_csr (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),
    .wr_data_i (mstack_epc_d),
    .wr_en_i   (mstack_en),
    .rd_data_o (mstack_epc_q),
    .rd_error_o()
  );

  // MSTACK_CAUSE
  ibex_csr #(
    .Width     ($bits(exc_cause_t)),
    .ShadowCopy(1'b0),
    .ResetValue('0)
  ) u_mstack_cause_csr (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),
    .wr_data_i (mstack_cause_d),
    .wr_en_i   (mstack_en),
    .rd_data_o (mstack_cause_q),
    .rd_error_o()
  );

  // -----------------
  // PMP registers
  // -----------------

  if (PMPEnable) begin : g_pmp_registers
    // PMP reset values
    `ifdef IBEX_CUSTOM_PMP_RESET_VALUES
      `include "ibex_pmp_reset.svh"
    `else
      `include "ibex_pmp_reset_default.svh"
    `endif

    pmp_mseccfg_t                pmp_mseccfg_q, pmp_mseccfg_d;
    logic                        pmp_mseccfg_we;
    logic                        pmp_mseccfg_err;
    pmp_cfg_t                    pmp_cfg         [PMPNumRegions];
    logic [PMPNumRegions-1:0]    pmp_cfg_locked;
    logic [PMPNumRegions-1:0]    pmp_cfg_wr_suppress;
    pmp_cfg_t                    pmp_cfg_wdata   [PMPNumRegions];
    logic [PMPAddrWidth-1:0]     pmp_addr        [PMPNumRegions];
    logic [PMPNumRegions-1:0]    pmp_cfg_we;
    logic [PMPNumRegions-1:0]    pmp_cfg_err;
    logic [PMPNumRegions-1:0]    pmp_addr_we;
    logic [PMPNumRegions-1:0]    pmp_addr_err;
    logic                        any_pmp_entry_locked;

    // Expanded / qualified register read data
    for (genvar i = 0; i < PMP_MAX_REGIONS; i++) begin : g_exp_rd_data
      if (i < PMPNumRegions) begin : g_implemented_regions
        // Add in zero padding for reserved fields
        assign pmp_cfg_rdata[i] = {pmp_cfg[i].lock, 2'b00, pmp_cfg[i].mode,
                                   pmp_cfg[i].exec, pmp_cfg[i].write, pmp_cfg[i].read};

        // Address field read data depends on the current programmed mode and the granularity
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
            // In NAPOT mode, bits [G-2:0] must read as one
            pmp_addr_rdata[i] = {pmp_addr[i], {PMPGranularity - 1{1'b1}}};

            if ((pmp_cfg[i].mode == PMP_MODE_OFF) || (pmp_cfg[i].mode == PMP_MODE_TOR)) begin
              // In TOR or OFF mode, bits [G-1:0] must read as zero
              pmp_addr_rdata[i][PMPGranularity-1:0] = '0;
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
      assign pmp_cfg_we[i] = csr_we_int                                       &
                             ~pmp_cfg_locked[i]                               &
                             ~pmp_cfg_wr_suppress[i]                          &
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
      // When MSECCFG.MML is unset, W = 1, R = 0 is a reserved combination, so force W to 0 if R ==
      // 0. Otherwise allow all possible values to be written.
      assign pmp_cfg_wdata[i].write = pmp_mseccfg_q.mml ? csr_wdata_int[(i%4)*PMP_CFG_W+1] :
                                                          &csr_wdata_int[(i%4)*PMP_CFG_W+:2];
      assign pmp_cfg_wdata[i].read  = csr_wdata_int[(i%4)*PMP_CFG_W];

      ibex_csr #(
        .Width     ($bits(pmp_cfg_t)),
        .ShadowCopy(ShadowCSR),
        .ResetValue(pmp_cfg_rst[i])
      ) u_pmp_cfg_csr (
        .clk_i     (clk_i),
        .rst_ni    (rst_ni),
        .wr_data_i ({pmp_cfg_wdata[i]}),
        .wr_en_i   (pmp_cfg_we[i]),
        .rd_data_o (pmp_cfg[i]),
        .rd_error_o(pmp_cfg_err[i])
      );

      // MSECCFG.RLB allows the lock bit to be bypassed (allowing cfg writes when MSECCFG.RLB is
      // set).
      assign pmp_cfg_locked[i] = pmp_cfg[i].lock & ~pmp_mseccfg_q.rlb;

      // When MSECCFG.MML is set cannot add new regions allowing M mode execution unless MSECCFG.RLB
      // is set
      assign pmp_cfg_wr_suppress[i] = pmp_mseccfg_q.mml                   &
                                      ~pmp_mseccfg.rlb                    &
                                      is_mml_m_exec_cfg(pmp_cfg_wdata[i]);

      // --------------------------
      // Instantiate addr registers
      // --------------------------
      if (i < PMPNumRegions - 1) begin : g_lower
        assign pmp_addr_we[i] = csr_we_int & ~pmp_cfg_locked[i] &
                                (~pmp_cfg_locked[i+1] | (pmp_cfg[i+1].mode != PMP_MODE_TOR)) &
                                (csr_addr == (CSR_OFF_PMP_ADDR + i[11:0]));
      end else begin : g_upper
        assign pmp_addr_we[i] = csr_we_int & ~pmp_cfg_locked[i] &
                                (csr_addr == (CSR_OFF_PMP_ADDR + i[11:0]));
      end

      ibex_csr #(
        .Width     (PMPAddrWidth),
        .ShadowCopy(ShadowCSR),
        .ResetValue(pmp_addr_rst[i][33-:PMPAddrWidth])
      ) u_pmp_addr_csr (
        .clk_i     (clk_i),
        .rst_ni    (rst_ni),
        .wr_data_i (csr_wdata_int[31-:PMPAddrWidth]),
        .wr_en_i   (pmp_addr_we[i]),
        .rd_data_o (pmp_addr[i]),
        .rd_error_o(pmp_addr_err[i])
      );

      `ASSERT_INIT(PMPAddrRstLowBitsZero_A, pmp_addr_rst[i][33-PMPAddrWidth:0] == '0)

      assign csr_pmp_cfg_o[i]  = pmp_cfg[i];
      assign csr_pmp_addr_o[i] = {pmp_addr_rdata[i], 2'b00};
    end

    assign pmp_mseccfg_we = csr_we_int & (csr_addr == CSR_MSECCFG);

    // MSECCFG.MML/MSECCFG.MMWP cannot be unset once set
    assign pmp_mseccfg_d.mml  = pmp_mseccfg_q.mml  ? 1'b1 : csr_wdata_int[CSR_MSECCFG_MML_BIT];
    assign pmp_mseccfg_d.mmwp = pmp_mseccfg_q.mmwp ? 1'b1 : csr_wdata_int[CSR_MSECCFG_MMWP_BIT];

    // pmp_cfg_locked factors in MSECCFG.RLB so any_pmp_entry_locked will only be set if MSECCFG.RLB
    // is unset
    assign any_pmp_entry_locked = |pmp_cfg_locked;

    // When any PMP entry is locked (A PMP entry has the L bit set and MSECCFG.RLB is unset),
    // MSECCFG.RLB cannot be set again
    assign pmp_mseccfg_d.rlb = any_pmp_entry_locked ? 1'b0 : csr_wdata_int[CSR_MSECCFG_RLB_BIT];

    ibex_csr #(
      .Width     ($bits(pmp_mseccfg_t)),
      .ShadowCopy(ShadowCSR),
      .ResetValue(pmp_mseccfg_rst)
    ) u_pmp_mseccfg (
      .clk_i     (clk_i),
      .rst_ni    (rst_ni),
      .wr_data_i (pmp_mseccfg_d),
      .wr_en_i   (pmp_mseccfg_we),
      .rd_data_o (pmp_mseccfg_q),
      .rd_error_o(pmp_mseccfg_err)
    );

    assign pmp_csr_err = (|pmp_cfg_err) | (|pmp_addr_err) | pmp_mseccfg_err;
    assign pmp_mseccfg = pmp_mseccfg_q;

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
    assign pmp_csr_err = 1'b0;
    assign pmp_mseccfg = '0;
  end

  assign csr_pmp_mseccfg_o = pmp_mseccfg;

  //////////////////////////
  //  Performance monitor //
  //////////////////////////

  // update enable signals
  always_comb begin : mcountinhibit_update
    if (mcountinhibit_we == 1'b1) begin
      // bit 1 must always be 0
      mcountinhibit_d = {csr_wdata_int[MHPMCounterNum+2:2], 1'b0, csr_wdata_int[0]};
    end else begin
      mcountinhibit_d = mcountinhibit_q;
    end
  end

  // event selection (hardwired) & control
  always_comb begin : gen_mhpmcounter_incr

    // Assign inactive counters (first to prevent latch inference)
    for (int unsigned i = 0; i < 32; i++) begin : gen_mhpmcounter_incr_inactive
      mhpmcounter_incr[i] = 1'b0;
    end

    // When adding or altering performance counter meanings and default
    // mappings please update dv/verilator/pcount/cpp/ibex_pcounts.cc
    // appropriately.
    //
    // active counters
    mhpmcounter_incr[0]  = 1'b1;                   // mcycle
    mhpmcounter_incr[1]  = 1'b0;                   // reserved
    mhpmcounter_incr[2]  = instr_ret_i;            // minstret
    mhpmcounter_incr[3]  = dside_wait_i;           // cycles waiting for data memory
    mhpmcounter_incr[4]  = iside_wait_i;           // cycles waiting for instr fetches
    mhpmcounter_incr[5]  = mem_load_i;             // num of loads
    mhpmcounter_incr[6]  = mem_store_i;            // num of stores
    mhpmcounter_incr[7]  = jump_i;                 // num of jumps (unconditional)
    mhpmcounter_incr[8]  = branch_i;               // num of branches (conditional)
    mhpmcounter_incr[9]  = branch_taken_i;         // num of taken branches (conditional)
    mhpmcounter_incr[10] = instr_ret_compressed_i; // num of compressed instr
    mhpmcounter_incr[11] = mul_wait_i;             // cycles waiting for multiply
    mhpmcounter_incr[12] = div_wait_i;             // cycles waiting for divide
  end

  // event selector (hardwired, 0 means no event)
  always_comb begin : gen_mhpmevent

    // activate all
    for (int i = 0; i < 32; i++) begin : gen_mhpmevent_active
      mhpmevent[i] = '0;

      if (i >= 3) begin
        mhpmevent[i][i - 3] = 1'b1;
      end
    end

    // deactivate
    mhpmevent[1] = '0; // not existing, reserved
    for (int unsigned i = 3 + MHPMCounterNum; i < 32; i++) begin : gen_mhpmevent_inactive
      mhpmevent[i] = '0;
    end
  end

  // mcycle
  ibex_counter #(
    .CounterWidth(64)
  ) mcycle_counter_i (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .counter_inc_i(mhpmcounter_incr[0] & ~mcountinhibit[0]),
    .counterh_we_i(mhpmcounterh_we[0]),
    .counter_we_i(mhpmcounter_we[0]),
    .counter_val_i(csr_wdata_int),
    .counter_val_o(mhpmcounter[0]),
    .counter_val_upd_o()
  );


  // minstret
  ibex_counter #(
    .CounterWidth(64),
    .ProvideValUpd(1)
  ) minstret_counter_i (
    .clk_i(clk_i),
    .rst_ni(rst_ni),
    .counter_inc_i(mhpmcounter_incr[2] & ~mcountinhibit[2]),
    .counterh_we_i(mhpmcounterh_we[2]),
    .counter_we_i(mhpmcounter_we[2]),
    .counter_val_i(csr_wdata_int),
    .counter_val_o(minstret_raw),
    .counter_val_upd_o(minstret_next)
  );

  // Where the writeback stage is present instruction in ID observing value of minstret must take
  // into account any instruction in the writeback stage. If one is present the incremented value of
  // minstret is used. A speculative version of the signal is used to aid timing. When the writeback
  // stage sees an exception (so the speculative signal is incorrect) the ID stage will be flushed
  // so the incorrect value doesn't matter. A similar behaviour is required for the compressed
  // instruction retired counter below. When the writeback stage isn't present the speculative
  // signals are always 0.
  assign mhpmcounter[2] = instr_ret_spec_i & ~mcountinhibit[2] ? minstret_next : minstret_raw;

  // reserved:
  assign mhpmcounter[1]            = '0;
  assign unused_mhpmcounter_we_1   = mhpmcounter_we[1];
  assign unused_mhpmcounterh_we_1  = mhpmcounterh_we[1];
  assign unused_mhpmcounter_incr_1 = mhpmcounter_incr[1];

  // Iterate through optionally included counters (MHPMCounterNum controls how many are included)
  for (genvar i = 0; i < 29; i++) begin : gen_cntrs
    localparam int Cnt = i + 3;

    if (i < MHPMCounterNum) begin : gen_imp
      logic [63:0] mhpmcounter_raw, mhpmcounter_next;

      ibex_counter #(
        .CounterWidth(MHPMCounterWidth),
        .ProvideValUpd(Cnt == 10)
      ) mcounters_variable_i (
        .clk_i(clk_i),
        .rst_ni(rst_ni),
        .counter_inc_i(mhpmcounter_incr[Cnt] & ~mcountinhibit[Cnt]),
        .counterh_we_i(mhpmcounterh_we[Cnt]),
        .counter_we_i(mhpmcounter_we[Cnt]),
        .counter_val_i(csr_wdata_int),
        .counter_val_o(mhpmcounter_raw),
        .counter_val_upd_o(mhpmcounter_next)
      );

      if (Cnt == 10) begin : gen_compressed_instr_cnt
        // Special behaviour for reading compressed instruction retired counter, see comment on
        // `mhpmcounter[2]` above for further information.
        assign mhpmcounter[Cnt] =
          instr_ret_compressed_spec_i & ~mcountinhibit[Cnt] ? mhpmcounter_next:
                                                              mhpmcounter_raw;
      end else begin : gen_other_cnts
        logic [63:0] unused_mhpmcounter_next;
        // All other counters just see the raw counter value directly.
        assign mhpmcounter[Cnt] = mhpmcounter_raw;
        assign unused_mhpmcounter_next = mhpmcounter_next;
      end
    end else begin : gen_unimp
      assign mhpmcounter[Cnt] = '0;

      if (Cnt == 10) begin : gen_no_compressed_instr_cnt
        logic unused_instr_ret_compressed_spec_i;
        assign unused_instr_ret_compressed_spec_i = instr_ret_compressed_spec_i;
      end
    end
  end

  if (MHPMCounterNum < 29) begin : g_mcountinhibit_reduced
    logic [29-MHPMCounterNum-1:0] unused_mhphcounter_we;
    logic [29-MHPMCounterNum-1:0] unused_mhphcounterh_we;
    logic [29-MHPMCounterNum-1:0] unused_mhphcounter_incr;

    assign mcountinhibit = {{29 - MHPMCounterNum{1'b0}}, mcountinhibit_q};
    // Lint tieoffs for unused bits
    assign unused_mhphcounter_we   = mhpmcounter_we[31:MHPMCounterNum+3];
    assign unused_mhphcounterh_we  = mhpmcounterh_we[31:MHPMCounterNum+3];
    assign unused_mhphcounter_incr = mhpmcounter_incr[31:MHPMCounterNum+3];
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
    localparam int unsigned DbgHwNumLen = DbgHwBreakNum > 1 ? $clog2(DbgHwBreakNum) : 1;
    localparam int unsigned MaxTselect = DbgHwBreakNum - 1;

    // Register values
    logic [DbgHwNumLen-1:0]   tselect_d, tselect_q;
    logic                     tmatch_control_d;
    logic [DbgHwBreakNum-1:0] tmatch_control_q;
    logic [31:0]              tmatch_value_d;
    logic [31:0]              tmatch_value_q[DbgHwBreakNum];
    logic                     selected_tmatch_control;
    logic [31:0]              selected_tmatch_value;

    // Write enables
    logic                     tselect_we;
    logic [DbgHwBreakNum-1:0] tmatch_control_we;
    logic [DbgHwBreakNum-1:0] tmatch_value_we;
    // Trigger comparison result
    logic [DbgHwBreakNum-1:0] trigger_match;

    // Write select
    assign tselect_we = csr_we_int & debug_mode_i & (csr_addr_i == CSR_TSELECT);
    for (genvar i = 0; i < DbgHwBreakNum; i++) begin : g_dbg_tmatch_we
      assign tmatch_control_we[i] = (i[DbgHwNumLen-1:0] == tselect_q) & csr_we_int & debug_mode_i &
                                    (csr_addr_i == CSR_TDATA1);
      assign tmatch_value_we[i]   = (i[DbgHwNumLen-1:0] == tselect_q) & csr_we_int & debug_mode_i &
                                    (csr_addr_i == CSR_TDATA2);
    end

    // Debug interface tests the available number of triggers by writing and reading the trigger
    // select register. Only allow changes to the register if it is within the supported region.
    assign tselect_d = (csr_wdata_int < DbgHwBreakNum) ? csr_wdata_int[DbgHwNumLen-1:0] :
                                                         MaxTselect[DbgHwNumLen-1:0];

    // tmatch_control is enabled when the execute bit is set
    assign tmatch_control_d = csr_wdata_int[2];
    assign tmatch_value_d   = csr_wdata_int[31:0];

    // Registers
    ibex_csr #(
      .Width     (DbgHwNumLen),
      .ShadowCopy(1'b0),
      .ResetValue('0)
    ) u_tselect_csr (
      .clk_i     (clk_i),
      .rst_ni    (rst_ni),
      .wr_data_i (tselect_d),
      .wr_en_i   (tselect_we),
      .rd_data_o (tselect_q),
      .rd_error_o()
    );

    for (genvar i = 0; i < DbgHwBreakNum; i++) begin : g_dbg_tmatch_reg
      ibex_csr #(
        .Width     (1),
        .ShadowCopy(1'b0),
        .ResetValue('0)
      ) u_tmatch_control_csr (
        .clk_i     (clk_i),
        .rst_ni    (rst_ni),
        .wr_data_i (tmatch_control_d),
        .wr_en_i   (tmatch_control_we[i]),
        .rd_data_o (tmatch_control_q[i]),
        .rd_error_o()
      );

      ibex_csr #(
        .Width     (32),
        .ShadowCopy(1'b0),
        .ResetValue('0)
      ) u_tmatch_value_csr (
        .clk_i     (clk_i),
        .rst_ni    (rst_ni),
        .wr_data_i (tmatch_value_d),
        .wr_en_i   (tmatch_value_we[i]),
        .rd_data_o (tmatch_value_q[i]),
        .rd_error_o()
      );
    end

    // Assign read data
    // TSELECT - number of supported triggers defined by parameter DbgHwBreakNum
    localparam int unsigned TSelectRdataPadlen = DbgHwNumLen >= 32 ? 0 : (32 - DbgHwNumLen);
    assign tselect_rdata = {{TSelectRdataPadlen{1'b0}}, tselect_q};

    if (DbgHwBreakNum > 1) begin : g_dbg_tmatch_multiple_select
      assign selected_tmatch_control = tmatch_control_q[tselect_q];
      assign selected_tmatch_value   = tmatch_value_q[tselect_q];
    end else begin : g_dbg_tmatch_single_select
      assign selected_tmatch_control = tmatch_control_q[0];
      assign selected_tmatch_value   = tmatch_value_q[0];
    end

    // TDATA0 - only support simple address matching
    assign tmatch_control_rdata = {4'h2,                    // type    : address/data match
                                   1'b1,                    // dmode   : access from D mode only
                                   6'h00,                   // maskmax : exact match only
                                   1'b0,                    // hit     : not supported
                                   1'b0,                    // select  : address match only
                                   1'b0,                    // timing  : match before execution
                                   2'b00,                   // sizelo  : match any access
                                   4'h1,                    // action  : enter debug mode
                                   1'b0,                    // chain   : not supported
                                   4'h0,                    // match   : simple match
                                   1'b1,                    // m       : match in m-mode
                                   1'b0,                    // 0       : zero
                                   1'b0,                    // s       : not supported
                                   1'b1,                    // u       : match in u-mode
                                   selected_tmatch_control, // execute : match instruction address
                                   1'b0,                    // store   : not supported
                                   1'b0};                   // load    : not supported

    // TDATA1 - address match value only
    assign tmatch_value_rdata = selected_tmatch_value;

    // Breakpoint matching
    // We match against the next address, as the breakpoint must be taken before execution
    for (genvar i = 0; i < DbgHwBreakNum; i++) begin : g_dbg_trigger_match
      assign trigger_match[i] = tmatch_control_q[i] & (pc_if_i[31:0] == tmatch_value_q[i]);
    end
    assign trigger_match_o = |trigger_match;

  end else begin : gen_no_trigger_regs
    assign tselect_rdata        = 'b0;
    assign tmatch_control_rdata = 'b0;
    assign tmatch_value_rdata   = 'b0;
    assign trigger_match_o      = 'b0;
  end

  //////////////////////////
  // CPU control register //
  //////////////////////////

  // Cast register write data
  assign cpuctrlsts_part_wdata_raw =
    cpu_ctrl_sts_part_t'(csr_wdata_int[$bits(cpu_ctrl_sts_part_t)-1:0]);

  // Generate fixed time execution bit
  if (DataIndTiming) begin : gen_dit
    // SEC_CM: CORE.DATA_REG_SW.SCA
    assign cpuctrlsts_part_wdata.data_ind_timing = cpuctrlsts_part_wdata_raw.data_ind_timing;

  end else begin : gen_no_dit
    // tieoff for the unused bit
    logic unused_dit;
    assign unused_dit = cpuctrlsts_part_wdata_raw.data_ind_timing;

    // field will always read as zero if not configured
    assign cpuctrlsts_part_wdata.data_ind_timing = 1'b0;
  end

  assign data_ind_timing_o = cpuctrlsts_part_q.data_ind_timing;

  // Generate dummy instruction signals
  if (DummyInstructions) begin : gen_dummy
    // SEC_CM: CTRL_FLOW.UNPREDICTABLE
    assign cpuctrlsts_part_wdata.dummy_instr_en   = cpuctrlsts_part_wdata_raw.dummy_instr_en;
    assign cpuctrlsts_part_wdata.dummy_instr_mask = cpuctrlsts_part_wdata_raw.dummy_instr_mask;

    // Signal a write to the seed register
    assign dummy_instr_seed_en_o = csr_we_int && (csr_addr == CSR_SECURESEED);
    assign dummy_instr_seed_o    = csr_wdata_int;

  end else begin : gen_no_dummy
    // tieoff for the unused bit
    logic       unused_dummy_en;
    logic [2:0] unused_dummy_mask;
    assign unused_dummy_en   = cpuctrlsts_part_wdata_raw.dummy_instr_en;
    assign unused_dummy_mask = cpuctrlsts_part_wdata_raw.dummy_instr_mask;

    // field will always read as zero if not configured
    assign cpuctrlsts_part_wdata.dummy_instr_en   = 1'b0;
    assign cpuctrlsts_part_wdata.dummy_instr_mask = 3'b000;
    assign dummy_instr_seed_en_o             = 1'b0;
    assign dummy_instr_seed_o                = '0;
  end

  assign dummy_instr_en_o   = cpuctrlsts_part_q.dummy_instr_en;
  assign dummy_instr_mask_o = cpuctrlsts_part_q.dummy_instr_mask;

  // Generate icache enable bit
  if (ICache) begin : gen_icache_enable
    assign cpuctrlsts_part_wdata.icache_enable = cpuctrlsts_part_wdata_raw.icache_enable;

    ibex_csr #(
      .Width     (1),
      .ShadowCopy(ShadowCSR),
      .ResetValue(1'b0)
    ) u_cpuctrlsts_ic_scr_key_valid_q_csr (
      .clk_i     (clk_i),
      .rst_ni    (rst_ni),
      .wr_data_i (ic_scr_key_valid_i),
      .wr_en_i   (1'b1),
      .rd_data_o (cpuctrlsts_ic_scr_key_valid_q),
      .rd_error_o(cpuctrlsts_ic_scr_key_err)
    );
  end else begin : gen_no_icache
    // tieoff for the unused icen bit
    logic unused_icen;
    assign unused_icen = cpuctrlsts_part_wdata_raw.icache_enable;

    // icen field will always read as zero if ICache not configured
    assign cpuctrlsts_part_wdata.icache_enable = 1'b0;


    logic unused_ic_scr_key_valid;
    assign unused_ic_scr_key_valid = ic_scr_key_valid_i;

    // ic_scr_key_valid will always read as zero if ICache not configured
    assign cpuctrlsts_ic_scr_key_valid_q = 1'b0;
    assign cpuctrlsts_ic_scr_key_err     = 1'b0;
  end

  assign cpuctrlsts_part_wdata.double_fault_seen = cpuctrlsts_part_wdata_raw.double_fault_seen;
  assign cpuctrlsts_part_wdata.sync_exc_seen     = cpuctrlsts_part_wdata_raw.sync_exc_seen;

  assign icache_enable_o =
    cpuctrlsts_part_q.icache_enable & ~(debug_mode_i | debug_mode_entering_i);

  ibex_csr #(
    .Width     ($bits(cpu_ctrl_sts_part_t)),
    .ShadowCopy(ShadowCSR),
    .ResetValue('0)
  ) u_cpuctrlsts_part_csr (
    .clk_i     (clk_i),
    .rst_ni    (rst_ni),
    .wr_data_i ({cpuctrlsts_part_d}),
    .wr_en_i   (cpuctrlsts_part_we),
    .rd_data_o (cpuctrlsts_part_q),
    .rd_error_o(cpuctrlsts_part_err)
  );

  assign csr_shadow_err_o =
    mstatus_err | mtvec_err | pmp_csr_err | cpuctrlsts_part_err | cpuctrlsts_ic_scr_key_err;

  ////////////////
  // Assertions //
  ////////////////

  `ASSERT(IbexCsrOpEnRequiresAccess, csr_op_en_i |-> csr_access_i)

endmodule
