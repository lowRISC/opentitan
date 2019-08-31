// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Sven Stucki - svstucki@student.ethz.ch                     //
//                                                                            //
// Additional contributions by:                                               //
//                 Andreas Traber - atraber@iis.ee.ethz.ch                    //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    Control and Status Registers                               //
// Project Name:   ibex                                                       //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Control and Status Registers (CSRs) following the RISC-V   //
//                 Privileged Specification, draft version 1.11               //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

/**
 * Control and Status Registers
 *
 * Control and Status Registers (CSRs) following the RISC-V Privileged
 * Specification, draft version 1.11
 */
module ibex_cs_registers #(
    parameter int unsigned MHPMCounterNum   = 8,
    parameter int unsigned MHPMCounterWidth = 40,
    parameter bit RV32E                     = 0,
    parameter bit RV32M                     = 0
) (
    // Clock and Reset
    input  logic                 clk_i,
    input  logic                 rst_ni,

    // Core and Cluster ID
    input  logic  [3:0]          core_id_i,
    input  logic  [5:0]          cluster_id_i,

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
    output logic                 irq_pending_o,          // interupt request pending
    output logic                 csr_msip_o,             // software interrupt pending
    output logic                 csr_mtip_o,             // timer interrupt pending
    output logic                 csr_meip_o,             // external interrupt pending
    output logic [14:0]          csr_mfip_o,             // fast interrupt pending
    output logic                 csr_mstatus_mie_o,
    output logic [31:0]          csr_mepc_o,

    // debug
    input  ibex_pkg::dbg_cause_e debug_cause_i,
    input  logic                 debug_csr_save_i,
    output logic [31:0]          csr_depc_o,
    output logic                 debug_single_step_o,
    output logic                 debug_ebreakm_o,

    input  logic [31:0]          pc_if_i,
    input  logic [31:0]          pc_id_i,

    input  logic                 csr_save_if_i,
    input  logic                 csr_save_id_i,
    input  logic                 csr_restore_mret_i,
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
    | (0          << 20)  // U - User mode implemented
    | (0          << 23)  // X - Non-standard extensions present
    | (32'(MXL)   << 30); // M-XLEN

  typedef struct packed {
    logic      mie;
    logic      mpie;
    priv_lvl_e mpp;
  } Status_t;

  // struct for mip/mie CSRs
  typedef struct packed {
    logic        irq_software;
    logic        irq_timer;
    logic        irq_external;
    logic [14:0] irq_fast; // 15 fast interrupts,
                           // one interrupt is reserved for NMI (not visible through mip/mie)
  } Interrupts_t;

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
  Status_t     mstatus_q, mstatus_d;
  Interrupts_t mie_q, mie_d;
  logic [31:0] mscratch_q, mscratch_d;
  logic [31:0] mepc_q, mepc_d;
  logic  [5:0] mcause_q, mcause_d;
  logic [31:0] mtval_q, mtval_d;
  logic [31:0] mtvec_q, mtvec_d;
  Interrupts_t mip;
  Dcsr_t       dcsr_q, dcsr_d;
  logic [31:0] depc_q, depc_d;
  logic [31:0] dscratch0_q, dscratch0_d;
  logic [31:0] dscratch1_q, dscratch1_d;

  // CSRs for recoverable NMIs
  // NOTE: these CSRS are nonstandard, see https://github.com/riscv/riscv-isa-manual/issues/261
  Status_t     mstack_q, mstack_d;
  logic [31:0] mstack_epc_q, mstack_epc_d;
  logic  [5:0] mstack_cause_q, mstack_cause_d;

  // Hardware performance monitor signals
  logic [31:0] mcountinhibit_d, mcountinhibit_q, mcountinhibit;
  logic [31:0] mcountinhibit_force;
  logic        mcountinhibit_we;
  logic [63:0] mhpmcounter_mask [32];
  logic [63:0] mhpmcounter_d [32];
  logic [63:0] mhpmcounter_q [32];
  logic [31:0] mhpmcounter_we;
  logic [31:0] mhpmcounterh_we;
  logic [31:0] mhpmcounter_incr;
  logic [31:0] mhpmevent [32];
  logic  [4:0] mhpmcounter_idx;

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

  assign unused_boot_addr = boot_addr_i[7:0];

  /////////////
  // CSR reg //
  /////////////

  logic [$bits(csr_num_e)-1:0] csr_addr;
  assign csr_addr           = {csr_addr_i};
  assign mhpmcounter_idx    = csr_addr[4:0];

  assign illegal_csr_priv   = 1'b0; // we only support M-mode
  assign illegal_csr_write  = (csr_addr[11:10] == 2'b11) && csr_wreq;
  assign illegal_csr_insn_o = illegal_csr | illegal_csr_write | illegal_csr_priv;

  // mip CSR is purely combintational - must be able to re-enable the clock upon WFI
  assign mip.irq_software = irq_software_i & mie_q.irq_software;
  assign mip.irq_timer    = irq_timer_i    & mie_q.irq_timer;
  assign mip.irq_external = irq_external_i & mie_q.irq_external;
  assign mip.irq_fast     = irq_fast_i     & mie_q.irq_fast;

  // read logic
  always_comb begin
    csr_rdata_int = '0;
    illegal_csr   = 1'b0;

    unique case (csr_addr_i)
      // mhartid: unique hardware thread id
      CSR_MHARTID: csr_rdata_int = {21'b0, cluster_id_i[5:0], 1'b0, core_id_i[3:0]};

      // mstatus: always M-mode, contains IE bit
      CSR_MSTATUS: begin
        csr_rdata_int                                                   = '0;
        csr_rdata_int[CSR_MSTATUS_MIE_BIT]                              = mstatus_q.mie;
        csr_rdata_int[CSR_MSTATUS_MPIE_BIT]                             = mstatus_q.mpie;
        csr_rdata_int[CSR_MSTATUS_MPP_BIT_HIGH:CSR_MSTATUS_MPP_BIT_LOW] = mstatus_q.mpp;
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

      CSR_DCSR:      csr_rdata_int = dcsr_q;
      CSR_DPC:       csr_rdata_int = depc_q;
      CSR_DSCRATCH0: csr_rdata_int = dscratch0_q;
      CSR_DSCRATCH1: csr_rdata_int = dscratch1_q;

      // machine counter/timers
      CSR_MCOUNTINHIBIT: csr_rdata_int = mcountinhibit;
      CSR_MCYCLE:        csr_rdata_int = mhpmcounter_q[0][31: 0];
      CSR_MCYCLEH:       csr_rdata_int = mhpmcounter_q[0][63:32];
      CSR_MINSTRET:      csr_rdata_int = mhpmcounter_q[2][31: 0];
      CSR_MINSTRETH:     csr_rdata_int = mhpmcounter_q[2][63:32];

      default: begin
        if ((csr_addr & CSR_MASK_MCOUNTER) == CSR_OFF_MCOUNTER_SETUP) begin
          csr_rdata_int = mhpmevent[mhpmcounter_idx];
          // check access to non-existent or already covered CSRs
          if ((csr_addr[4:0] == 5'b00000) ||     // CSR_MCOUNTINHIBIT
              (csr_addr[4:0] == 5'b00001) ||
              (csr_addr[4:0] == 5'b00010)) begin
            illegal_csr = csr_access_i;
          end

        end else if ((csr_addr & CSR_MASK_MCOUNTER) == CSR_OFF_MCOUNTER) begin
          csr_rdata_int = mhpmcounter_q[mhpmcounter_idx][31: 0];
          // check access to non-existent or already covered CSRs
          if ((csr_addr[4:0] == 5'b00000) ||     // CSR_MCYCLE
              (csr_addr[4:0] == 5'b00001) ||
              (csr_addr[4:0] == 5'b00010)) begin // CSR_MINSTRET
            illegal_csr = csr_access_i;
          end

        end else if ((csr_addr & CSR_MASK_MCOUNTER) == CSR_OFF_MCOUNTERH) begin
          csr_rdata_int = mhpmcounter_q[mhpmcounter_idx][63:32];
          // check access to non-existent or already covered CSRs
          if ((csr_addr[4:0] == 5'b00000) ||     // CSR_MCYCLEH
              (csr_addr[4:0] == 5'b00001) ||
              (csr_addr[4:0] == 5'b00010)) begin // CSR_MINSTRETH
            illegal_csr = csr_access_i;
          end
        end else begin
          illegal_csr = csr_access_i;
        end
      end
    endcase
  end

  // write logic
  always_comb begin
    exception_pc = pc_id_i;

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

    unique case (csr_addr_i)
      // mstatus: IE bit
      CSR_MSTATUS: begin
        if (csr_we_int) begin
          mstatus_d = '{
              mie:  csr_wdata_int[CSR_MSTATUS_MIE_BIT],
              mpie: csr_wdata_int[CSR_MSTATUS_MPIE_BIT],
              mpp:  PRIV_LVL_M
          };
        end
      end

      // interrupt enable
      CSR_MIE: begin
        if (csr_we_int) begin
          mie_d.irq_software = csr_wdata_int[CSR_MSIX_BIT];
          mie_d.irq_timer    = csr_wdata_int[CSR_MTIX_BIT];
          mie_d.irq_external = csr_wdata_int[CSR_MEIX_BIT];
          mie_d.irq_fast     = csr_wdata_int[CSR_MFIX_BIT_HIGH:CSR_MFIX_BIT_LOW];
        end
      end

      CSR_MSCRATCH: if (csr_we_int) mscratch_d = csr_wdata_int;

      // mepc: exception program counter
      CSR_MEPC: if (csr_we_int) mepc_d = {csr_wdata_int[31:1], 1'b0};

      // mcause
      CSR_MCAUSE: if (csr_we_int) mcause_d = {csr_wdata_int[31], csr_wdata_int[4:0]};

      // mtval: trap value
      CSR_MTVAL: if (csr_we_int) mtval_d = csr_wdata_int;

      // mtvec
      // mtvec.MODE set to vectored
      // mtvec.BASE must be 256-byte aligned
      CSR_MTVEC: if (csr_we_int) mtvec_d = {csr_wdata_int[31:8], 6'b0, 2'b01};

      CSR_DCSR: begin
        if (csr_we_int) begin
          dcsr_d = csr_wdata_int;
          dcsr_d.xdebugver = XDEBUGVER_STD;
          dcsr_d.prv = PRIV_LVL_M; // only M-mode is supported

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
      end

      CSR_DPC: begin
        // Only valid PC addresses are allowed (half-word aligned with C ext.)
        if (csr_we_int && csr_wdata_int[0] == 1'b0) begin
          depc_d = csr_wdata_int;
        end
      end

      CSR_DSCRATCH0: begin
        if (csr_we_int) begin
          dscratch0_d = csr_wdata_int;
        end
      end

      CSR_DSCRATCH1: begin
        if (csr_we_int) begin
          dscratch1_d = csr_wdata_int;
        end
      end

      CSR_MCOUNTINHIBIT: begin
        if (csr_we_int) begin
          mcountinhibit_we = 1'b1;
        end
      end

      CSR_MCYCLE: begin
        if (csr_we_int) begin
          mhpmcounter_we[0] = 1'b1;
        end
      end

      CSR_MCYCLEH: begin
        if (csr_we_int) begin
          mhpmcounterh_we[0] = 1'b1;
        end
      end

      CSR_MINSTRET: begin
        if (csr_we_int) begin
          mhpmcounter_we[2] = 1'b1;
        end
      end

      CSR_MINSTRETH: begin
        if (csr_we_int) begin
          mhpmcounterh_we[2] = 1'b1;
        end
      end

      default: begin
        if (csr_we_int == 1'b1) begin
          // performance counters and event selector
          if ((csr_addr & CSR_MASK_MCOUNTER) == CSR_OFF_MCOUNTER) begin
            mhpmcounter_we[mhpmcounter_idx] = 1'b1;
          end else if ((csr_addr & CSR_MASK_MCOUNTER) == CSR_OFF_MCOUNTERH) begin
            mhpmcounterh_we[mhpmcounter_idx] = 1'b1;
          end
        end
      end
    endcase

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

        if (debug_csr_save_i) begin
          // all interrupts are masked
          // do not update cause, epc, tval, epc and status
          dcsr_d.prv   = PRIV_LVL_M;
          dcsr_d.cause = debug_cause_i;
          depc_d       = exception_pc;
        end else begin
          mtval_d        = csr_mtval_i;
          mstatus_d.mie  = 1'b0; // disable interrupts
          // save current status
          mstatus_d.mpie = mstatus_q.mie;
          mstatus_d.mpp  = PRIV_LVL_M;
          mepc_d         = exception_pc;
          mcause_d       = {csr_mcause_i};
          // save previous status for recoverable NMI
          mstack_d.mpie  = mstatus_q.mpie;
          mstack_d.mpp   = mstatus_q.mpp;
          mstack_epc_d   = mepc_q;
          mstack_cause_d = mcause_q;
        end
      end // csr_save_cause_i

      csr_restore_mret_i: begin // MRET
        mstatus_d.mie  = mstatus_q.mpie; // re-enable interrupts
        // restore previous status for recoverable NMI
        mstatus_d.mpie = mstack_q.mpie;
        mstatus_d.mpp  = mstack_q.mpp;
        mepc_d         = mstack_epc_q;
        mcause_d       = mstack_cause_q;
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
        csr_wdata_int = 'X;
        csr_wreq      = 1'bX;
      end
    endcase
  end

  // only write CSRs during one clock cycle
  assign csr_we_int  = csr_wreq & instr_new_id_i;

  assign csr_rdata_o = csr_rdata_int;

  // directly output some registers
  assign csr_msip_o  = mip.irq_software;
  assign csr_mtip_o  = mip.irq_timer;
  assign csr_meip_o  = mip.irq_external;
  assign csr_mfip_o  = mip.irq_fast;

  assign csr_mepc_o  = mepc_q;
  assign csr_depc_o  = depc_q;
  assign csr_mtvec_o = mtvec_q;

  assign csr_mstatus_mie_o   = mstatus_q.mie;
  assign debug_single_step_o = dcsr_q.step;
  assign debug_ebreakm_o     = dcsr_q.ebreakm;

  assign irq_pending_o = csr_msip_o | csr_mtip_o | csr_meip_o | (|csr_mfip_o);

  // actual registers
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      mstatus_q      <= '{
          mie:  1'b0,
          mpie: 1'b0,
          mpp:  PRIV_LVL_M
      };
      mie_q          <= '0;
      mscratch_q     <= '0;
      mepc_q         <= '0;
      mcause_q       <= '0;
      mtval_q        <= '0;
      mtvec_q        <= 32'b01;
      dcsr_q         <= '{
          xdebugver: XDEBUGVER_NO,   // 4'h0
          cause:     DBG_CAUSE_NONE, // 3'h0
          prv:       PRIV_LVL_M,
          default:   '0
      };
      depc_q         <= '0;
      dscratch0_q    <= '0;
      dscratch1_q    <= '0;

      mstack_q       <= '{
          mie:  1'b0,
          mpie: 1'b0,
          mpp:  PRIV_LVL_M
      };
      mstack_epc_q   <= '0;
      mstack_cause_q <= '0;

    end else begin
      // update CSRs
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

  //////////////////////////
  //  Performance monitor //
  //////////////////////////

  // update enable signals
  always_comb begin : mcountinhibit_update
    if (mcountinhibit_we == 1'b1) begin
      mcountinhibit_d = {csr_wdata_int[31:2], 1'b0, csr_wdata_int[0]}; // bit 1 must always be 0
    end else begin
      mcountinhibit_d = mcountinhibit_q;
    end
  end

  assign mcountinhibit_force = {{29-MHPMCounterNum{1'b1}}, {MHPMCounterNum{1'b0}}, 3'b000};
  assign mcountinhibit       = mcountinhibit_q | mcountinhibit_force;

  // event selection (hardwired) & control
  always_comb begin : gen_mhpmcounter_incr

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

  // mask, controls effective counter width
  always_comb begin : gen_mask

    for (int i=0; i<3; i++) begin : gen_mask_fixed
      // mcycle, mtime, minstret are always 64 bit wide
      mhpmcounter_mask[i] = {64{1'b1}};
    end

    for (int unsigned i=3; i<3+MHPMCounterNum; i++) begin : gen_mask_configurable
      // mhpmcounters have a configurable width
      mhpmcounter_mask[i] = {{64-MHPMCounterWidth{1'b0}}, {MHPMCounterWidth{1'b1}}};
    end

    for (int unsigned i=3+MHPMCounterNum; i<32; i++) begin : gen_mask_inactive
      // mask inactive mhpmcounters
      mhpmcounter_mask[i] = '0;
    end
  end

  // update
  always_comb begin : mhpmcounter_update
    mhpmcounter_d = mhpmcounter_q;

    for (int i=0; i<32; i++) begin : gen_mhpmcounter_update

      // increment
      if (mhpmcounter_incr[i] & ~mcountinhibit[i]) begin
        mhpmcounter_d[i] = mhpmcounter_mask[i] & (mhpmcounter_q[i] + 64'h1);
      end

      // write
      if (mhpmcounter_we[i]) begin
        mhpmcounter_d[i][31: 0] = mhpmcounter_mask[i][31: 0] & csr_wdata_int;
      end else if (mhpmcounterh_we[i]) begin
        mhpmcounter_d[i][63:32] = mhpmcounter_mask[i][63:32] & csr_wdata_int;
      end
    end
  end

  // performance monitor registers
  always_ff @(posedge clk_i or negedge rst_ni) begin : perf_counter_registers
    if (!rst_ni) begin
      mcountinhibit_q    <= '0;
      for (int i=0; i<32; i++) begin
        mhpmcounter_q[i] <= '0;
      end
    end else begin
      mhpmcounter_q      <= mhpmcounter_d;
      mcountinhibit_q    <= mcountinhibit_d;
    end
  end

endmodule
