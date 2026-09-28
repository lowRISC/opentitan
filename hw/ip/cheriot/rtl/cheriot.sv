// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

// SEC_CM: LOGIC.SHADOW
// TODO: Implement lockstep operation for this module

module cheriot
  import cheriot_reg_pkg::*;
#(
  // TL-UL address type
  parameter type   addr_t           = logic [top_pkg::TL_AW-1:0],
  // Top-level address map parameters
  parameter addr_t                MainSramBaseAddr = 'h1000_0000,
  parameter addr_t                MainSramTopAddr  = 'h1003_0000,
  parameter addr_t                NvmBaseAddr      = 'h3000_0000,
  parameter addr_t                NvmTopAddr       = 'h3020_0000,
  parameter addr_t                MetaSramBaseAddr = 'h1100_0000,
  parameter int unsigned          MemSizeRevbm     = 3072,
  parameter logic [NumAlerts-1:0] AlertAsyncOn     = {NumAlerts{1'b1}},
  parameter int unsigned          AlertSkewCycles  = 1
) (

  input  logic clk_i,
  input  logic rst_ni,

  // CHERIoT mode enabled
  input  prim_mubi_pkg::mubi4_t cheriot_ena_i,

  // Interrupts
  output logic intr_trbe_done_o,

  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,

  // Device interface for CSRs
  input  tlul_pkg::tl_h2d_t regs_tl_d_i,
  output tlul_pkg::tl_d2h_t regs_tl_d_o,

  // Core data input port
  input  tlul_pkg::tl_h2d_t cored_tl_d_i,
  input  logic              cored_tag_h2d_i,
  output tlul_pkg::tl_d2h_t cored_tl_d_o,
  output logic              cored_tag_d2h_o,

  // TRVK revocation bitmap input port
  input  tlul_pkg::tl_h2d_t corerevbm_tl_i,
  output tlul_pkg::tl_d2h_t corerevbm_tl_o,

  // System revocation bitmap port
  input  tlul_pkg::tl_h2d_t revbm_tl_d_i,
  output tlul_pkg::tl_d2h_t revbm_tl_d_o,

  // Core data output port towards interconnect
  output tlul_pkg::tl_h2d_t cored_tl_h_o,
  input  tlul_pkg::tl_d2h_t cored_tl_h_i,

  // Revocation engine read-only port towards interconnect
  output tlul_pkg::tl_h2d_t trbe_tl_h_o,
  input  tlul_pkg::tl_d2h_t trbe_tl_h_i,

  // Meta SRAM host port (to external sram_ctrl)
  output tlul_pkg::tl_h2d_t meta_sram_tl_o,
  input  tlul_pkg::tl_d2h_t meta_sram_tl_i
);

  /////////////////
  // Address map //
  /////////////////

  // Revocation happens on 64-bit or 8-byte granularity.
  localparam int unsigned RevocationGranuleByte = 32'd8;
  // Number of heap bytes a single TL word in the meta store can track
  localparam int unsigned RevocationBytePerWord = top_pkg::TL_DW * RevocationGranuleByte;

  // A capability is 64 bit or 8 byte wide
  localparam int unsigned CapabilitySizeByte    = 32'd8;
  // Byte offset bits of a capability
  localparam int unsigned CapOffsetW            = $clog2(CapabilitySizeByte);
  // Number of capability bytes a single TL word in the meta store can track
  localparam int unsigned CapabilityBytePerWord = top_pkg::TL_DW * CapabilitySizeByte;

  // Size of the TRVK revocation bitmap
  localparam addr_t RevBmSizeWord   = (MainSramTopAddr - MainSramBaseAddr) / RevocationBytePerWord;
  localparam addr_t RevBmSizeByte   = RevBmSizeWord * (top_pkg::TL_DW / 32'd8);
  // Size of the SRAM tag store
  localparam addr_t SramTagSizeWord = (MainSramTopAddr - MainSramBaseAddr) / CapabilityBytePerWord;
  localparam addr_t SramTagSizeByte = SramTagSizeWord * (top_pkg::TL_DW / 32'd8);
  // Size of the NVM tag store
  localparam addr_t NvmTagSizeWord  = (NvmTopAddr - NvmBaseAddr) / CapabilityBytePerWord;
  localparam addr_t NvmTagSizeByte  = NvmTagSizeWord * (top_pkg::TL_DW / 32'd8);

  // Address map
  localparam addr_t MetaRevBmBase       = MetaSramBaseAddr;
  localparam addr_t MetaNvmTagBase      = MetaRevBmBase       + RevBmSizeByte;
  localparam addr_t MetaMainSramTagBase = MetaNvmTagBase      + NvmTagSizeByte;
  localparam addr_t MetaTop             = MetaMainSramTagBase + SramTagSizeByte;

  // Core transactions outstanding at once, the depth of the core's tag filter
  localparam int unsigned CoreOutstanding = 32'd2;
  localparam int unsigned CorePtrW        = prim_util_pkg::vbits(CoreOutstanding);
  // Core writes the revocation engine watches: the presented one and the outstanding ones
  localparam int unsigned NumSnoop        = CoreOutstanding + 32'd1;
  // Words the revocation engine has in flight: the two words of one capability. Required
  // to achieve full throughput.
  localparam int unsigned TrbeInflight    = 32'd2;

  typedef struct packed {
    logic csr_intg;
    logic meta_sram_intg;
    logic meta_sram_data_intg;
    logic rmw_error;
    logic trbe_mover_error;
    logic trbe_revbm_intg;
    logic trbe_revbm_data_intg;
    logic trbe_revbm_error;
  } cheriot_fatal_error_t;

  /////////////
  // Signals //
  /////////////

  tlul_pkg::tl_h2d_t tag_mux_in_tl_h2d[32'd2];
  logic              tag_mux_in_tag_h2d[32'd2];
  logic [4:0]        tag_mux_in_bit_sel[32'd2];
  tlul_pkg::tl_d2h_t tag_mux_in_tl_d2h[32'd2];
  logic              tag_mux_in_tag_d2h[32'd2];

  tlul_pkg::tl_h2d_t rmw_sock_tl_h2d;
  tlul_pkg::tl_h2d_t rmw_tl_h2d;
  logic              rmw_tag_h2d;
  logic [4:0]        rmw_bit_sel;
  tlul_pkg::tl_d2h_t rmw_tl_d2h;
  logic              rmw_tag_d2h;

  logic [NumSnoop-1:0]  trbe_snoop_valid;
  addr_t [NumSnoop-1:0] trbe_snoop_addr;
  logic                 trbe_clear_hit;
  logic                 trbe_clear_valid;
  logic                 trbe_clear_done;
  addr_t                trbe_clear_addr;
  logic                 trbe_clear_at_rmw;
  logic                 trbe_clear_rmw_set;
  logic                 trbe_clear_rmw_en;
  logic                 trbe_clear_rmw_d, trbe_clear_rmw_q;
  logic                 trbe_clear_stale_set;
  logic                 trbe_clear_stale_en;
  logic                 trbe_clear_stale_d, trbe_clear_stale_q;
  logic                 unused_trbe_clear_addr;

  logic                       core_req_write;
  logic                       core_req_done;
  logic                       core_rsp_done;
  logic [CoreOutstanding-1:0] core_wr_valid_q;
  addr_t                      core_wr_addr_q[CoreOutstanding];
  logic [CorePtrW-1:0]        core_wptr, core_rptr;

  // RMW filter errors
  logic rmw_data_intg_err;
  logic rmw_rsp_intg_err;
  logic rmw_dev_err;

  tlul_pkg::tl_h2d_t tags_tl_h2d;
  tlul_pkg::tl_d2h_t tags_tl_d2h;

  tlul_pkg::tl_h2d_t trbe_revbm_tl_h2d;
  tlul_pkg::tl_d2h_t trbe_revbm_tl_d2h;

  tlul_pkg::tl_h2d_t meta_mux_in_tl_h2d[32'd4];
  tlul_pkg::tl_d2h_t meta_mux_in_tl_d2h[32'd4];

  logic                    trbe_valid_d, trbe_valid_q;
  logic                    trbe_ready;
  logic                    trbe_busy;
  logic                    trbe_active, trbe_active_q;
  logic                    trbe_start_err, trbe_start_err_q;
  logic                    trbe_sweep_err, trbe_sweep_err_q;
  logic                    trbe_done;
  logic                    trbe_failed_en;
  logic                    trbe_failed_d, trbe_failed_q;
  logic                    trbe_epoch_en;
  logic [TrbeEpochW-1:0]   trbe_epoch_d, trbe_epoch_q;
  logic                    trbe_mover_err;
  logic                    trbe_revbm_intg_err;
  logic                    trbe_revbm_data_intg_err;
  logic                    trbe_revbm_dev_err;
  addr_t                   trbe_start_addr;
  addr_t                   trbe_num_words;
  logic                    trbe_in_sram;
  logic                    trbe_in_nvm;
  logic                    trbe_in_range;
  addr_t                   trbe_region_top;
  addr_t                   trbe_bytes_to_top;
  addr_t                   trbe_caps_to_top;
  logic [TrbeNumCapsW-1:0] trbe_sweep_caps;

  cheriot_regs_reg2hw_t reg2hw;
  cheriot_regs_hw2reg_t hw2reg;

  logic alert_test;

  // Fatal errors
  cheriot_fatal_error_t cheriot_fatal_error;


  //////////////
  // CSR Node //
  //////////////

  cheriot_regs_reg_top u_reg_regs (
    .clk_i,
    .rst_ni,
    .tl_i      (regs_tl_d_i),
    .tl_o      (regs_tl_d_o),
    .reg2hw,
    .hw2reg,
    // SEC_CM: BUS.INTEGRITY
    .intg_err_o(cheriot_fatal_error.csr_intg)
  );


  ////////////
  // Filter //
  ////////////

  cheriot_access_check #(
    .addr_t(addr_t),
    .CheriotBaseAddr(MetaRevBmBase),
    .CheriotTopAddr(MetaNvmTagBase)
  ) u_cheriot_access_check_trvk (
    .clk_i,
    .rst_ni,
    .cheriot_ena_i,
    .tl_h_i(corerevbm_tl_i),
    .tl_h_o(corerevbm_tl_o),
    .tl_d_o(meta_mux_in_tl_h2d[32'd0]),
    .tl_d_i(meta_mux_in_tl_d2h[32'd0])
  );

  cheriot_tag_filter #(
    .NumOutstanding(CoreOutstanding),
    .addr_t(addr_t),
    .MainSramBaseAddr(MainSramBaseAddr),
    .MainSramTopAddr(MainSramTopAddr),
    .NvmBaseAddr(NvmBaseAddr),
    .NvmTopAddr(NvmTopAddr),
    .MetaMainSramTagBase(MetaMainSramTagBase),
    .MetaNvmTagBase(MetaNvmTagBase)
  ) u_cheriot_tag_filter (
    .clk_i,
    .rst_ni,
    .cheriot_ena_i,
    .tl_d_i     (cored_tl_d_i),
    .tag_d_i    (cored_tag_h2d_i),
    .tl_d_o     (cored_tl_d_o),
    .tag_d_o    (cored_tag_d2h_o),
    .tl_m_o     (tag_mux_in_tl_h2d[32'd0]),
    .tag_m_o    (tag_mux_in_tag_h2d[32'd0]),
    .bit_sel_m_o(tag_mux_in_bit_sel[32'd0]),
    .tl_m_i     (tag_mux_in_tl_d2h[32'd0]),
    .tag_m_i    (tag_mux_in_tag_d2h[32'd0]),
    .tl_h_o     (cored_tl_h_o),
    .tl_h_i     (cored_tl_h_i)
  );

  // Arbitrates the tag traffic of the core's and the revocation engine's tag filters onto the
  // single RMW filter.
  cheriot_socket_m1 #(
    .M(32'd2),
    .HReqDepth('0),
    .HRspDepth('0),
    .DReqDepth('0),
    .DRspDepth('0)
  ) u_cheriot_socket_m1 (
    .clk_i,
    .rst_ni,
    .tl_h_i     (tag_mux_in_tl_h2d),
    .tag_h_i    (tag_mux_in_tag_h2d),
    .bit_sel_h_i(tag_mux_in_bit_sel),
    .tl_h_o     (tag_mux_in_tl_d2h),
    .tag_h_o    (tag_mux_in_tag_d2h),
    .tl_d_o     (rmw_sock_tl_h2d),
    .tag_d_o    (rmw_tag_h2d),
    .bit_sel_d_o(rmw_bit_sel),
    .tl_d_i     (rmw_tl_d2h),
    .tag_d_i    (rmw_tag_d2h)
  );

  //////////////////////
  // Tag Clear Squash //
  //////////////////////

  // A tag clear of the revocation engine that a core write to the same capability overtakes on
  // its way to the RMW filter must not clear the new tag. From the cycle the engine presents a
  // clear until the clear reaches the RMW filter, such a core write marks it stale, and the RMW
  // filter then only reads the tag word. Once the clear is at the RMW filter, the socket holds it
  // there and no core write can reach the RMW filter before it.

  // The socket numbers the revocation engine's port 1 in the source ID's lowest bit
  assign trbe_clear_at_rmw = rmw_sock_tl_h2d.a_valid && rmw_sock_tl_h2d.a_source[0] &&
                             (rmw_sock_tl_h2d.a_opcode != tlul_pkg::Get);

  // Each mark is set on its event and dropped once the clear completes, which takes priority
  assign trbe_clear_rmw_set   = trbe_clear_at_rmw && rmw_tl_d2h.a_ready;
  assign trbe_clear_stale_set = trbe_clear_valid && !trbe_clear_at_rmw && !trbe_clear_rmw_q &&
                                trbe_clear_hit;
  assign trbe_clear_rmw_en    = trbe_clear_done || trbe_clear_rmw_set;
  assign trbe_clear_rmw_d     = !trbe_clear_done;
  assign trbe_clear_stale_en  = trbe_clear_done || trbe_clear_stale_set;
  assign trbe_clear_stale_d   = !trbe_clear_done;

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_trbe_clear_rmw_store
    if (!rst_ni) begin
      trbe_clear_rmw_q <= 1'b0;
    end else begin
      if (trbe_clear_rmw_en) begin
        trbe_clear_rmw_q <= trbe_clear_rmw_d;
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_trbe_clear_stale_store
    if (!rst_ni) begin
      trbe_clear_stale_q <= 1'b0;
    end else begin
      if (trbe_clear_stale_en) begin
        trbe_clear_stale_q <= trbe_clear_stale_d;
      end
    end
  end

  // The clear is compared at capability granularity
  assign unused_trbe_clear_addr = ^trbe_clear_addr[CapOffsetW-1:0];

  always_comb begin : proc_trbe_clear_hit
    trbe_clear_hit = 1'b0;
    for (int unsigned i = 0; i < NumSnoop; i++) begin
      trbe_clear_hit |= trbe_snoop_valid[i] && (trbe_snoop_addr[i][$bits(addr_t)-1:CapOffsetW] ==
                                                trbe_clear_addr[$bits(addr_t)-1:CapOffsetW]);
    end
  end

  // The RMW filter regenerates the command integrity of every request it issues, so the opcode
  // alone is replaced.
  always_comb begin : proc_trbe_clear_squash
    rmw_tl_h2d = rmw_sock_tl_h2d;
    if (trbe_clear_at_rmw && trbe_clear_stale_q) begin
      rmw_tl_h2d.a_opcode = tlul_pkg::Get;
    end
  end

  ////////////////////////
  // Core Write Tracker //
  ////////////////////////

  // Core writes the engine watches: a capability the core writes while the engine is resolving it
  // keeps the tag the core wrote. A write is watched from its presentation until its answer, as
  // an accepted write may still be on its way to memory when the engine reads the same capability.
  assign core_req_write = (cored_tl_d_i.a_opcode == tlul_pkg::PutFullData) ||
                          (cored_tl_d_i.a_opcode == tlul_pkg::PutPartialData);
  assign core_req_done  = cored_tl_d_i.a_valid && cored_tl_d_o.a_ready;
  assign core_rsp_done  = cored_tl_d_o.d_valid && cored_tl_d_i.d_ready;

  // Every core transaction takes an entry, in order, so that the answers free them in order
  prim_fifo_sync_cnt #(
    .Depth      (CoreOutstanding),
    .Secure     (1'b0),
    .NeverClears(1'b1)
  ) u_prim_fifo_sync_cnt_core_wr (
    .clk_i,
    .rst_ni,
    .clr_i      (1'b0),
    .incr_wptr_i(core_req_done),
    .incr_rptr_i(core_rsp_done),
    .wptr_o     (core_wptr),
    .rptr_o     (core_rptr),
    .full_o     (),
    .empty_o    (),
    .depth_o    (),
    .err_o      ()
  );

  for (genvar i = 0; i < CoreOutstanding; i++) begin : gen_core_wr_entry
    logic entry_push;
    logic entry_pop;
    logic entry_valid_en;
    logic entry_valid_d;

    assign entry_push = core_req_done && (core_wptr == CorePtrW'(unsigned'(i)));
    assign entry_pop  = core_rsp_done && (core_rptr == CorePtrW'(unsigned'(i)));

    // A full tracker frees and takes the same entry in one cycle; the new transaction wins
    assign entry_valid_en = entry_push || entry_pop;
    assign entry_valid_d  = entry_push && core_req_write;

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_core_wr_addr_store
      if (!rst_ni) begin
        core_wr_addr_q[i] <= '0;
      end else begin
        if (entry_push) begin
          core_wr_addr_q[i] <= cored_tl_d_i.a_address;
        end
      end
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_core_wr_valid_store
      if (!rst_ni) begin
        core_wr_valid_q[i] <= 1'b0;
      end else begin
        if (entry_valid_en) begin
          core_wr_valid_q[i] <= entry_valid_d;
        end
      end
    end
  end

  assign trbe_snoop_valid[0] = cored_tl_d_i.a_valid && core_req_write;
  assign trbe_snoop_addr[0]  = cored_tl_d_i.a_address;
  for (genvar i = 0; i < CoreOutstanding; i++) begin : gen_trbe_snoop
    assign trbe_snoop_valid[i + 1] = core_wr_valid_q[i];
    assign trbe_snoop_addr[i + 1]  = core_wr_addr_q[i];
  end

  ////////////////
  // RMW Filter //
  ////////////////

  // SEC_CM: BUS.INTEGRITY
  cheriot_rmw_filter #(
    .addr_t(addr_t)
  ) u_cheriot_rmw_filter (
    .clk_i,
    .rst_ni,
    .tl_h_i           (rmw_tl_h2d),
    .tag_h_i          (rmw_tag_h2d),
    .bit_sel_h_i      (rmw_bit_sel),
    .tl_h_o           (rmw_tl_d2h),
    .tag_h_o          (rmw_tag_d2h),
    .tl_d_o           (tags_tl_h2d),
    .tl_d_i           (tags_tl_d2h),
    .data_intg_error_o(rmw_data_intg_err),
    .rsp_intg_error_o (rmw_rsp_intg_err),
    .device_error_o   (rmw_dev_err)
  );

  assign cheriot_fatal_error.meta_sram_data_intg = rmw_data_intg_err;
  assign cheriot_fatal_error.meta_sram_intg      = rmw_rsp_intg_err;
  assign cheriot_fatal_error.rmw_error           = rmw_dev_err;

  ///////////////////
  // Access Checks //
  ///////////////////

  cheriot_access_check #(
    .addr_t(addr_t),
    .CheriotBaseAddr(MetaNvmTagBase),
    .CheriotTopAddr(MetaTop)
  ) u_cheriot_access_check_tags (
    .clk_i,
    .rst_ni,
    .cheriot_ena_i,
    .tl_h_i(tags_tl_h2d),
    .tl_h_o(tags_tl_d2h),
    .tl_d_o(meta_mux_in_tl_h2d[32'd1]),
    .tl_d_i(meta_mux_in_tl_d2h[32'd1])
  );

  cheriot_access_check #(
    .addr_t(addr_t),
    .CheriotBaseAddr(MetaRevBmBase),
    .CheriotTopAddr(MetaNvmTagBase)
  ) u_cheriot_access_check_sys (
    .clk_i,
    .rst_ni,
    .cheriot_ena_i,
    .tl_h_i(revbm_tl_d_i),
    .tl_h_o(revbm_tl_d_o),
    .tl_d_o(meta_mux_in_tl_h2d[32'd2]),
    .tl_d_i(meta_mux_in_tl_d2h[32'd2])
  );

  cheriot_access_check #(
    .addr_t(addr_t),
    .CheriotBaseAddr(MetaRevBmBase),
    .CheriotTopAddr(MetaNvmTagBase)
  ) u_cheriot_access_check_trbe (
    .clk_i,
    .rst_ni,
    .cheriot_ena_i,
    .tl_h_i(trbe_revbm_tl_h2d),
    .tl_h_o(trbe_revbm_tl_d2h),
    .tl_d_o(meta_mux_in_tl_h2d[32'd3]),
    .tl_d_i(meta_mux_in_tl_d2h[32'd3])
  );


  ///////////////////////
  // Meta multiplexing //
  ///////////////////////

  tlul_socket_m1 #(
    .M(32'd4),
    .HReqDepth('0),
    .HRspDepth('0),
    .DReqDepth('0),
    .DRspDepth('0)
  ) u_tlul_socket_m1 (
    .clk_i,
    .rst_ni,
    .tl_h_i(meta_mux_in_tl_h2d),
    .tl_h_o(meta_mux_in_tl_d2h),
    .tl_d_o(meta_sram_tl_o),
    .tl_d_i(meta_sram_tl_i)
  );


  ///////////////////////
  // Revocation Engine //
  ///////////////////////

  assign trbe_start_addr = {reg2hw.trbe_base_addr.q, {CapOffsetW{1'b0}}};

  // A sweep starts in one of the tagged regions, the main SRAM or the NVM, and stops at its top.
  // The bounds are constants, so the regions cost comparators against constants and share one
  // subtractor.
  assign trbe_in_sram      = (trbe_start_addr >= MainSramBaseAddr) &&
                             (trbe_start_addr <  MainSramTopAddr);
  assign trbe_in_nvm       = (trbe_start_addr >= NvmBaseAddr) && (trbe_start_addr < NvmTopAddr);
  assign trbe_in_range     = trbe_in_sram || trbe_in_nvm;
  assign trbe_region_top   = trbe_in_nvm ? NvmTopAddr : MainSramTopAddr;
  assign trbe_bytes_to_top = trbe_region_top - trbe_start_addr;
  assign trbe_caps_to_top  = trbe_bytes_to_top >> CapOffsetW;
  assign trbe_sweep_caps   = (addr_t'(reg2hw.trbe_num_caps.q) > trbe_caps_to_top) ?
                             trbe_caps_to_top[TrbeNumCapsW-1:0] : reg2hw.trbe_num_caps.q;
  assign trbe_num_words    = {trbe_sweep_caps, 1'b0};

  // Held until the engine accepts the sweep; a start without capabilities, outside the tagged
  // regions or outside CHERIoT mode is dropped.
  assign trbe_valid_d = trbe_valid_q ? !trbe_ready :
                        reg2hw.trbe_start.qe && reg2hw.trbe_start.q &&
                        (reg2hw.trbe_num_caps.q != '0) &&
                        trbe_in_range && prim_mubi_pkg::mubi4_test_true_strict(cheriot_ena_i);

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_trbe_valid_store
    if (!rst_ni) begin
      trbe_valid_q <= 1'b0;
    end else begin
      trbe_valid_q <= trbe_valid_d;
    end
  end

  // A start that is ignored is flagged until software clears the flag.
  assign trbe_start_err = reg2hw.trbe_start.qe && reg2hw.trbe_start.q &&
                          ((reg2hw.trbe_num_caps.q == '0) || !trbe_in_range ||
                           !prim_mubi_pkg::mubi4_test_true_strict(cheriot_ena_i));

  assign trbe_active                     = trbe_valid_q || trbe_busy;
  assign hw2reg.trbe_status.busy.de      = 1'b1;
  assign hw2reg.trbe_status.busy.d       = trbe_active;
  assign hw2reg.trbe_status.start_err.de = trbe_start_err_q;
  assign hw2reg.trbe_status.start_err.d  = 1'b1;
  // A fault of the RMW filter during a sweep may have hit one of the engine's tag operations, so it
  // counts as well.
  assign trbe_sweep_err = trbe_mover_err     || trbe_revbm_intg_err || trbe_revbm_data_intg_err ||
                          trbe_revbm_dev_err ||
                          (trbe_active && (rmw_data_intg_err || rmw_rsp_intg_err || rmw_dev_err));
  assign hw2reg.trbe_status.sweep_err.de = trbe_sweep_err_q;
  assign hw2reg.trbe_status.sweep_err.d  = 1'b1;
  assign hw2reg.trbe_regwen.d            = !trbe_active;

  // A sweep is done once the engine is no longer active. The error flags are set a cycle after
  // their cause.
  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_trbe_active_store
    if (!rst_ni) begin
      trbe_active_q    <= 1'b0;
      trbe_start_err_q <= 1'b0;
      trbe_sweep_err_q <= 1'b0;
    end else begin
      trbe_active_q    <= trbe_active;
      trbe_start_err_q <= trbe_start_err;
      trbe_sweep_err_q <= trbe_sweep_err;
    end
  end

  assign trbe_done = trbe_active_q && !trbe_active;

  // Epoch counter
  assign trbe_failed_en = trbe_sweep_err || trbe_done;
  assign trbe_failed_d  = !trbe_done;
  assign trbe_epoch_en  = trbe_done && !trbe_failed_q && !trbe_sweep_err;
  assign trbe_epoch_d   = trbe_epoch_q + 1'b1;

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_trbe_failed_store
    if (!rst_ni) begin
      trbe_failed_q <= 1'b0;
    end else begin
      if (trbe_failed_en) begin
        trbe_failed_q <= trbe_failed_d;
      end
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin : proc_trbe_epoch_store
    if (!rst_ni) begin
      trbe_epoch_q <= '0;
    end else begin
      if (trbe_epoch_en) begin
        trbe_epoch_q <= trbe_epoch_d;
      end
    end
  end

  // A read in the cycle the engine becomes inactive already sees the sweep counted, so the epoch
  // goes straight from odd to the next even value.
  assign hw2reg.trbe_epoch.count.d  = trbe_epoch_en ? trbe_epoch_d : trbe_epoch_q;
  assign hw2reg.trbe_epoch.active.d = trbe_active;

  prim_intr_hw #(
    .Width(1)
  ) u_intr_trbe_done (
    .clk_i,
    .rst_ni,
    .event_intr_i          (trbe_done),
    .reg2hw_intr_enable_q_i(reg2hw.intr_enable.q),
    .reg2hw_intr_test_q_i  (reg2hw.intr_test.q),
    .reg2hw_intr_test_qe_i (reg2hw.intr_test.qe),
    .reg2hw_intr_state_q_i (reg2hw.intr_state.q),
    .hw2reg_intr_state_de_o(hw2reg.intr_state.de),
    .hw2reg_intr_state_d_o (hw2reg.intr_state.d),
    .intr_o                (intr_trbe_done_o)
  );

  // SEC_CM: BUS.INTEGRITY
  cheriot_trbe #(
    .addr_t             (addr_t),
    .MainSramBaseAddr   (MainSramBaseAddr),
    .MainSramTopAddr    (MainSramTopAddr),
    .NvmBaseAddr        (NvmBaseAddr),
    .NvmTopAddr         (NvmTopAddr),
    .MetaMainSramTagBase(MetaMainSramTagBase),
    .MetaNvmTagBase     (MetaNvmTagBase),
    .RevBitmapSizeBytes (MemSizeRevbm),
    .RevBitmapBaseAddr  (MetaRevBmBase),
    .MaxInflight        (TrbeInflight),
    .NumSnoop           (NumSnoop)
  ) u_cheriot_trbe (
    .clk_i,
    .rst_ni,
    .cheriot_ena_i,
    .start_addr_i           (trbe_start_addr),
    .num_words_i            (trbe_num_words),
    .valid_i                (trbe_valid_q),
    .ready_o                (trbe_ready),
    .busy_o                 (trbe_busy),
    .snoop_valid_i          (trbe_snoop_valid),
    .snoop_addr_i           (trbe_snoop_addr),
    .clear_valid_o          (trbe_clear_valid),
    .clear_done_o           (trbe_clear_done),
    .clear_addr_o           (trbe_clear_addr),
    .revbm_tl_o             (trbe_revbm_tl_h2d),
    .revbm_tl_i             (trbe_revbm_tl_d2h),
    .tl_m_o                 (tag_mux_in_tl_h2d[32'd1]),
    .tag_m_o                (tag_mux_in_tag_h2d[32'd1]),
    .bit_sel_m_o            (tag_mux_in_bit_sel[32'd1]),
    .tl_m_i                 (tag_mux_in_tl_d2h[32'd1]),
    .tag_m_i                (tag_mux_in_tag_d2h[32'd1]),
    .tl_h_o                 (trbe_tl_h_o),
    .tl_h_i                 (trbe_tl_h_i),
    .mover_err_o            (trbe_mover_err),
    .revbm_data_intg_error_o(trbe_revbm_data_intg_err),
    .revbm_rsp_intg_error_o (trbe_revbm_intg_err),
    .revbm_device_error_o   (trbe_revbm_dev_err)
  );

  assign cheriot_fatal_error.trbe_mover_error     = trbe_mover_err;
  assign cheriot_fatal_error.trbe_revbm_intg      = trbe_revbm_intg_err;
  assign cheriot_fatal_error.trbe_revbm_data_intg = trbe_revbm_data_intg_err;
  assign cheriot_fatal_error.trbe_revbm_error     = trbe_revbm_dev_err;


  //////////////////
  // Alert Sender //
  //////////////////

  assign alert_test = reg2hw.alert_test.q & reg2hw.alert_test.qe;

  prim_alert_sender #(
    .AsyncOn(AlertAsyncOn[0]),
    .SkewCycles(AlertSkewCycles),
    .IsFatal(1'b1)
  ) u_prim_alert_sender_fatal_fault (
    .clk_i,
    .rst_ni,
    .alert_test_i (alert_test),
    .alert_req_i  (|cheriot_fatal_error),
    .alert_ack_o  (),
    .alert_state_o(),
    .alert_rx_i   (alert_rx_i[0]),
    .alert_tx_o   (alert_tx_o[0])
  );


  ////////////////
  // Assertions //
  ////////////////

  // Device ports: handshake signals are always known, the payload only while it is valid.
  `ASSERT_KNOWN(CoredTlDAReadyKnown_A, cored_tl_d_o.a_ready)
  `ASSERT_KNOWN(CoredTlDDValidKnown_A, cored_tl_d_o.d_valid)
  `ASSERT_KNOWN_IF(CoredTlDPayloadKnown_A, cored_tl_d_o, cored_tl_d_o.d_valid)
  `ASSERT_KNOWN(CoredTagD2hKnown_A, cored_tag_d2h_o)

  `ASSERT_KNOWN(CoreRevBmAReadyKnown_A, corerevbm_tl_o.a_ready)
  `ASSERT_KNOWN(CoreRevBmDValidKnown_A, corerevbm_tl_o.d_valid)
  `ASSERT_KNOWN_IF(CoreRevBmPayloadKnown_A, corerevbm_tl_o, corerevbm_tl_o.d_valid)

  `ASSERT_KNOWN(RevBmTlDAReadyKnown_A, revbm_tl_d_o.a_ready)
  `ASSERT_KNOWN(RevBmTlDDValidKnown_A, revbm_tl_d_o.d_valid)
  `ASSERT_KNOWN_IF(RevBmTlDPayloadKnown_A, revbm_tl_d_o, revbm_tl_d_o.d_valid)

  // Host ports: handshake signals are always known, the payload only while the request is valid.
  `ASSERT_KNOWN(CoredTlHAValidKnown_A, cored_tl_h_o.a_valid)
  `ASSERT_KNOWN(CoredTlHDReadyKnown_A, cored_tl_h_o.d_ready)
  `ASSERT_KNOWN_IF(CoredTlHPayloadKnown_A, cored_tl_h_o, cored_tl_h_o.a_valid)

  `ASSERT_KNOWN(TrbeTlHAValidKnown_A, trbe_tl_h_o.a_valid)
  `ASSERT_KNOWN(TrbeTlHDReadyKnown_A, trbe_tl_h_o.d_ready)
  `ASSERT_KNOWN_IF(TrbeTlHPayloadKnown_A, trbe_tl_h_o, trbe_tl_h_o.a_valid)

  `ASSERT_KNOWN(MetaSramAValidKnown_A, meta_sram_tl_o.a_valid)
  `ASSERT_KNOWN(MetaSramDReadyKnown_A, meta_sram_tl_o.d_ready)
  `ASSERT_KNOWN_IF(MetaSramPayloadKnown_A, meta_sram_tl_o, meta_sram_tl_o.a_valid)

  `ASSERT_KNOWN(RegsTlDAReadyKnown_A, regs_tl_d_o.a_ready)
  `ASSERT_KNOWN(RegsTlDDValidKnown_A, regs_tl_d_o.d_valid)
  `ASSERT_KNOWN_IF(RegsTlDPayloadKnown_A, regs_tl_d_o, regs_tl_d_o.d_valid)

  `ASSERT_KNOWN(AlertsKnown_A, alert_tx_o)
  `ASSERT_KNOWN(IntrTrbeDoneKnown_A, intr_trbe_done_o)

  // The engine reads the sweep from the registers until it accepts it.
  `ASSERT(TrbeReqStable_A, trbe_valid_q && !trbe_ready |=>
                           trbe_valid_q && $stable(trbe_start_addr) && $stable(trbe_num_words))
  `ASSERT(TrbeReqNonZero_A, trbe_valid_q |-> trbe_num_words != '0)
  // A sweep only starts in CHERIoT mode.
  `ASSERT(TrbeReqCheriotMode_A,
          $rose(trbe_valid_q) |-> $past(prim_mubi_pkg::mubi4_test_true_strict(cheriot_ena_i)))
  // A sweep stays inside the tagged region it starts in.
  `ASSERT(TrbeReqInRange_A, trbe_valid_q |->
          (trbe_in_sram &&
           35'(trbe_start_addr) + (35'(trbe_num_words) << 2) <= 35'(MainSramTopAddr)) ||
          (trbe_in_nvm &&
           35'(trbe_start_addr) + (35'(trbe_num_words) << 2) <= 35'(NvmTopAddr)))

  // A stale tag clear only reaches the RMW filter as a read of the tag word.
  `ASSERT(TrbeStaleClearSquashed_A, trbe_clear_at_rmw && trbe_clear_stale_q |->
                                    rmw_tl_h2d.a_opcode == tlul_pkg::Get)
  // The stale mark does not change while its clear waits at the RMW filter.
  `ASSERT(TrbeStaleStableAtRmw_A, trbe_clear_at_rmw && !rmw_tl_d2h.a_ready |=>
                                  $stable(trbe_clear_stale_q))

  // The socket holds a clear at the RMW filter until the filter takes it, so no core write can
  // reach the RMW filter before it.
  `ASSERT(TrbeClearHeldAtRmw_A, trbe_clear_at_rmw && !rmw_tl_d2h.a_ready |=>
                                trbe_clear_at_rmw && $stable(rmw_sock_tl_h2d.a_address))

  // The core has no more transactions outstanding than its tag filter admits, and every answer
  // belongs to a transaction.
  `ASSERT(CoreOutstandingBounded_A, core_req_done |-> !u_prim_fifo_sync_cnt_core_wr.full_o ||
                                                      core_rsp_done)
  `ASSERT(CoreRspHasReq_A, core_rsp_done |-> !u_prim_fifo_sync_cnt_core_wr.empty_o)

  // The snoop watches a core write from its presentation, so the core must not take a presented
  // request back: a retracted write would still have marked a clear stale and so kept a revoked
  // capability tagged. The core's host adapter holds its requests.
  `ASSUME(CoredReqHeld_M, cored_tl_d_i.a_valid && !cored_tl_d_o.a_ready |=>
          cored_tl_d_i.a_valid && $stable(cored_tl_d_i.a_address) &&
          $stable(cored_tl_d_i.a_opcode))
  `ASSERT_KNOWN(CheriotEnaKnown_A, cheriot_ena_i)

  // The epoch counts a sweep when it is done, and only a sweep without an error.
  `ASSERT(TrbeEpochCountsCleanSweeps_A, trbe_done |=>
          (trbe_epoch_q == $past(trbe_epoch_q) +
                           TrbeEpochW'($past(!trbe_failed_q && !trbe_sweep_err))))
  `ASSERT(TrbeEpochStable_A, !trbe_done |=> $stable(trbe_epoch_q))
  // The epoch software reads only moves by one: odd at a start, the next even value at the end
  // of a sweep without an error, back to the previous even value at the end of one with an error.
  `ASSERT(TrbeEpochStep_A, ##1 1'b1 |->
          (hw2reg.trbe_epoch == $past(hw2reg.trbe_epoch)) ||
          (hw2reg.trbe_epoch == $past(hw2reg.trbe_epoch) + 32'd1) ||
          ($past(hw2reg.trbe_epoch.active.d) && !hw2reg.trbe_epoch.active.d &&
           (hw2reg.trbe_epoch == $past(hw2reg.trbe_epoch) - 32'd1)))

  // Both marks of a clear are dropped with it, so none leaks into the next clear.
  `ASSERT(TrbeClearMarksIdle_A, !trbe_clear_valid |-> !trbe_clear_rmw_q && !trbe_clear_stale_q)

`ifdef INC_ASSERT
  // The tracker frees its entries in order: each core answer carries the source ID of the oldest
  // transaction.
  logic [top_pkg::TL_AIW-1:0] core_wr_src_q[CoreOutstanding];

  for (genvar i = 0; i < CoreOutstanding; i++) begin : gen_core_wr_src
    logic src_push;
    assign src_push = core_req_done && (core_wptr == CorePtrW'(unsigned'(i)));

    always_ff @(posedge clk_i or negedge rst_ni) begin : proc_core_wr_src_store
      if (!rst_ni) begin
        core_wr_src_q[i] <= '0;
      end else begin
        if (src_push) begin
          core_wr_src_q[i] <= cored_tl_d_i.a_source;
        end
      end
    end
  end

  `ASSERT(CoreRspInOrder_A, core_rsp_done |-> cored_tl_d_o.d_source == core_wr_src_q[core_rptr])
`endif

  // The engine only updates tags, it never writes to memory.
  `ASSERT(TrbeTlHReadOnly_A, trbe_tl_h_o.a_valid |-> trbe_tl_h_o.a_opcode == tlul_pkg::Get)

  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegsWeOnehotCheck_A,
      u_reg_regs, alert_tx_o[0])

  // Check address configurations
  `ASSERT_INIT(MainSramSizeMultipleOfCapabilityWord_A,
      (MainSramTopAddr - MainSramBaseAddr) % CapabilityBytePerWord == 0)
  `ASSERT_INIT(MainSramSizeMultipleOfRevocationWord_A,
      (MainSramTopAddr - MainSramBaseAddr) % RevocationBytePerWord == 0)
  `ASSERT_INIT(MainSramRangeCapabilityAligned_A,
      MainSramBaseAddr[CapOffsetW-1:0] == '0 && MainSramTopAddr[CapOffsetW-1:0] == '0 &&
      MainSramBaseAddr < MainSramTopAddr)
  `ASSERT_INIT(NvmSizeMultipleOfCapabilityWord_A,
      (NvmTopAddr - NvmBaseAddr) % CapabilityBytePerWord == 0)
  `ASSERT_INIT(NvmRangeCapabilityAligned_A,
      NvmBaseAddr[CapOffsetW-1:0] == '0 && NvmTopAddr[CapOffsetW-1:0] == '0 &&
      NvmBaseAddr < NvmTopAddr)
  // The tagged regions do not overlap, so a sweep starts in at most one of them.
  `ASSERT_INIT(TaggedRegionsDoNotOverlap_A,
      MainSramTopAddr <= NvmBaseAddr || NvmTopAddr <= MainSramBaseAddr)
  `ASSERT_INIT(MetaSramBaseAddrWordAligned_A, MetaSramBaseAddr[1:0] == 2'b00)
  // A sweep's word count, twice TRBE_NUM_CAPS, fits an address.
  `ASSERT_INIT(TrbeNumWordsFitAddr_A, TrbeNumCapsW + 32'd1 <= $bits(addr_t))
  // The revocation bitmap window declared at the top level must match the size derived from
  // the main SRAM region.
  `ASSERT_INIT(RevBmWindowMatchesDerivedSize_A, MemSizeRevbm == RevBmSizeByte)
  // The meta regions must not overlap
  `ASSERT_INIT(MetaRegionsDoNotOverlap_A,
      MetaRevBmBase < MetaNvmTagBase &&
      MetaNvmTagBase < MetaMainSramTagBase &&
      MetaMainSramTagBase < MetaTop)

endmodule
