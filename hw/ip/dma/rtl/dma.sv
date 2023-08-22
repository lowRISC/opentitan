// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module dma
  import tlul_pkg::*;
  import dma_pkg::*;
  import dma_reg_pkg::*;
#(
    parameter logic [NumAlerts-1:0] AlertAsyncOn         = {NumAlerts{1'b1}},
    parameter bit                   EnableDataIntgGen    = 1'b1,
    parameter logic [RsvdWidth-1:0] TlUserRsvd           = '0,
    parameter int                   NumLsioTriggers      = dma_pkg::NUM_LSIO_TRIGGERS,
    parameter int unsigned PlicLsioPlic[NumLsioTriggers] = '{
      32'h1234567,
      32'h1234567,
      32'h1234567,
      32'h1234567
    },
    parameter logic [SYS_RACL_WIDTH-1:0] SysRacl         = '0,
    parameter integer                  OtAgentId         = 0
) (
  input logic                                       clk_i,
  input logic                                       rst_ni,
  input logic                                       test_en_i,
  // DMA interrupts and incoming LSIO triggers
  output  logic                                     intr_dma_done_o,
  output  logic                                     intr_dma_error_o,
  output  logic                                     intr_dma_memory_buffer_limit_o,
  input   logic [(NumLsioTriggers-1):0]             lsio_trigger_i,
  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,
  // Device port
  input   tlul_pkg::tl_h2d_t                        tl_dev_i,
  output  tlul_pkg::tl_d2h_t                        tl_dev_o,
  // Facing CTN
  input   tlul_pkg::tl_d2h_t                        tl_ctn_i,
  output  tlul_pkg::tl_h2d_t                        tl_ctn_o,
  // Host port
  input   tlul_pkg::tl_d2h_t                        tl_host_i,
  output  tlul_pkg::tl_h2d_t                        tl_host_o,
  // System port
  input  dma_pkg::sys_rsp_t                         sys_i,
  output dma_pkg::sys_req_t                         sys_o
);
  import prim_mubi_pkg::*;

  dma_reg2hw_t reg2hw;
  dma_hw2reg_t hw2reg;

  localparam int unsigned TRANSFER_BYTES_WIDTH = $bits(reg2hw.total_data_size.q);

  // Signals for both TL interfaces
  logic                       dma_host_tlul_req_valid,    dma_ctn_tlul_req_valid;
  logic [top_pkg::TL_AW-1:0]  dma_host_tlul_req_addr,     dma_ctn_tlul_req_addr;
  logic                       dma_host_tlul_req_we,       dma_ctn_tlul_req_we;
  logic [top_pkg::TL_DW-1:0]  dma_host_tlul_req_wdata,    dma_ctn_tlul_req_wdata;
  logic [top_pkg::TL_DBW-1:0] dma_host_tlul_req_be,       dma_ctn_tlul_req_be;
  logic                       dma_host_tlul_gnt,          dma_ctn_tlul_gnt;
  logic                       dma_host_tlul_rsp_valid,    dma_ctn_tlul_rsp_valid;
  logic [top_pkg::TL_DW-1:0]  dma_host_tlul_rsp_data,     dma_ctn_tlul_rsp_data;
  logic                       dma_host_tlul_rsp_err,      dma_ctn_tlul_rsp_err;
  logic                       dma_host_tlul_rsp_intg_err, dma_ctn_tlul_rsp_intg_err;

  logic                       capture_return_data, capture_host_return_data,
                              capture_ctn_return_data, capture_sys_return_data;
  logic [top_pkg::TL_DW-1:0]  read_return_data_q, read_return_data_d;
  logic [SYS_ADDR_WIDTH-1:0]  new_source_addr, new_destination_addr;

  logic dma_state_error;
  dma_ctrl_state_e ctrl_state_q, ctrl_state_d;

  logic [DmaErrLast-1:0] next_error;
  logic bad_src_addr;
  logic bad_dst_addr;
  logic bad_opcode;
  logic bad_size;
  logic bad_base_limit;
  logic bad_go_config;
  logic bad_asid;
  logic config_error;

  logic read_rsp_error;

  logic cfg_handshake_en;
  logic cfg_fifo_auto_increment_en;
  logic cfg_memory_buffer_auto_increment_en;
  logic cfg_data_direction;
  logic cfg_abort_en;

  logic [SYS_METADATA_WIDTH-1:0] src_metadata;
  assign src_metadata = SYS_METADATA_WIDTH'(1'b1) << OtAgentId;

  logic sw_reg_wr, sw_reg_wr1, sw_reg_wr2;
  assign sw_reg_wr = reg2hw.source_address_lo.qe                           ||
                     reg2hw.source_address_hi.qe                           ||
                     reg2hw.destination_address_lo.qe                      ||
                     reg2hw.destination_address_hi.qe                      ||
                     reg2hw.address_space_id.source_asid.qe                ||
                     reg2hw.address_space_id.destination_asid.qe           ||
                     reg2hw.total_data_size.qe                             ||
                     reg2hw.transfer_width.qe                              ||
                     reg2hw.destination_address_limit_lo.qe                ||
                     reg2hw.destination_address_limit_hi.qe                ||
                     reg2hw.destination_address_almost_limit_lo.qe         ||
                     reg2hw.destination_address_almost_limit_hi.qe         ||
                     reg2hw.control.opcode.qe                              ||
                     reg2hw.control.hardware_handshake_enable.qe           ||
                     reg2hw.control.memory_buffer_auto_increment_enable.qe ||
                     reg2hw.control.fifo_auto_increment_enable.qe          ||
                     reg2hw.control.data_direction.qe                      ||
                     reg2hw.control.go.qe                                  ||
                     reg2hw.status.busy.qe                                 ||
                     reg2hw.status.done.qe                                 ||
                     reg2hw.status.aborted.qe                              ||
                     reg2hw.status.error.qe                                ||
                     reg2hw.status.error_code.qe;
  prim_flop #(
    .Width(1)
  ) aff_reg_wr1 (
    .clk_i ( clk_i      ),
    .rst_ni( rst_ni     ),
    .d_i   ( sw_reg_wr  ),
    .q_o   ( sw_reg_wr1 )
  );
  prim_flop #(
    .Width(1)
  ) aff_reg_wr2 (
    .clk_i ( clk_i      ),
    .rst_ni( rst_ni     ),
    .d_i   ( sw_reg_wr1 ),
    .q_o   ( sw_reg_wr2 )
  );

  // Stretch out CR writes to make sure new value can propogate through logic
  logic sw_reg_wr_extended;
  assign sw_reg_wr_extended = sw_reg_wr || sw_reg_wr1 || sw_reg_wr2;

  logic gated_clk_en, gated_clk;
  assign gated_clk_en = reg2hw.control.go.q       ||
                        (ctrl_state_q != DmaIdle) ||
                        sw_reg_wr_extended;

  prim_clock_gating dma_clk_gate (
    .clk_i    ( clk_i        ),
    .en_i     ( gated_clk_en ),
    .test_en_i( test_en_i    ),     ///< Test On to turn off the clock gating during test
    .clk_o    ( gated_clk    )
  );

  logic reg_intg_error;
  // SEC_CM: BUS.INTEGRITY
  // SEC_CM: RANGE_UNLOCK.CONFIG.REGWEN_MUBI
  dma_reg_top u_dma_reg (
    .clk_i     ( clk_i          ),
    .rst_ni    ( rst_ni         ),
    .tl_i      ( tl_dev_i       ),
    .tl_o      ( tl_dev_o       ),
    .reg2hw    ( reg2hw         ),
    .hw2reg    ( hw2reg         ),
    .intg_err_o( reg_intg_error )
  );

  // Alerts
  logic [NumAlerts-1:0] alert_test, alerts;
  assign alert_test = {reg2hw.alert_test.q & reg2hw.alert_test.qe};
  assign alerts[0]  = reg_intg_error              ||
                      dma_host_tlul_rsp_intg_err  ||
                      dma_ctn_tlul_rsp_intg_err   ||
                      dma_state_error;

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(1'b1)
    ) u_prim_alert_sender (
      .clk_i,
      .rst_ni,
      .alert_test_i (alert_test[i]),
      .alert_req_i  (alerts[0]),
      .alert_ack_o  (),
      .alert_state_o(),
      .alert_rx_i   (alert_rx_i[i]),
      .alert_tx_o   (alert_tx_o[i])
    );
  end

  // Adapter from the DMA to Host
  tlul_adapter_host #(
    .EnableDataIntgGen(EnableDataIntgGen)
  ) u_dma_host_tlul_host (
    .clk_i          ( gated_clk                        ),
    .rst_ni         ( rst_ni                           ),
    // do not make a request unless there is room for the response
    .req_i          ( dma_host_tlul_req_valid          ),
    .gnt_o          ( dma_host_tlul_gnt                ),
    .addr_i         ( dma_host_tlul_req_addr           ),
    .we_i           ( dma_host_tlul_req_we             ),
    .wdata_i        ( dma_host_tlul_req_wdata          ),
    .wdata_intg_i   ( TL_A_USER_DEFAULT.data_intg      ),
    .be_i           ( dma_host_tlul_req_be             ),
    .instr_type_i   ( MuBi4False                       ),
    .user_rsvd_i    ( TlUserRsvd                       ),
    .valid_o        ( dma_host_tlul_rsp_valid          ),
    .rdata_o        ( dma_host_tlul_rsp_data           ),
    .rdata_intg_o   (                                  ),
    .err_o          ( dma_host_tlul_rsp_err            ),
    .intg_err_o     ( dma_host_tlul_rsp_intg_err       ),
    .tl_o           ( tl_host_o                        ),
    .tl_i           ( tl_host_i                        )
  );

  // Adapter from the DMA to the ctn
  tlul_adapter_host #(
    .EnableDataIntgGen(EnableDataIntgGen)
  ) u_dma_ctn_tlul_host (
    .clk_i          ( gated_clk                        ),
    .rst_ni         ( rst_ni                           ),
    // do not make a request unless there is room for the response
    .req_i          ( dma_ctn_tlul_req_valid           ),
    .gnt_o          ( dma_ctn_tlul_gnt                 ),
    .addr_i         ( dma_ctn_tlul_req_addr            ),
    .we_i           ( dma_ctn_tlul_req_we              ),
    .wdata_i        ( dma_ctn_tlul_req_wdata           ),
    .wdata_intg_i   ( TL_A_USER_DEFAULT.data_intg      ),
    .be_i           ( dma_ctn_tlul_req_be              ),
    .instr_type_i   ( MuBi4False                       ),
    .user_rsvd_i    ( TlUserRsvd                       ),
    .valid_o        ( dma_ctn_tlul_rsp_valid           ),
    .rdata_o        ( dma_ctn_tlul_rsp_data            ),
    .rdata_intg_o   (                                  ),
    .err_o          ( dma_ctn_tlul_rsp_err             ),
    .intg_err_o     ( dma_ctn_tlul_rsp_intg_err        ),
    .tl_o           ( tl_ctn_o                         ),
    .tl_i           ( tl_ctn_i                         )
  );

  logic [top_pkg::TL_AW-1:0]  plic_clear_addr;
  logic [NumLsioTriggers-1:0] lsio_trigger;

  always_comb begin
    lsio_trigger = '0;
    plic_clear_addr = '0;

    for (int i = 0; i < NumLsioTriggers; i++) begin
      lsio_trigger[i] = lsio_trigger_i[i] && reg2hw.handshake_interrupt_enable.q[i];
      if (lsio_trigger[i]) begin
        plic_clear_addr = PlicLsioPlic[i];
      end
    end
  end

  // Following cast is only temporary until FSM becomes sparesly encoded
  // to avoid conversion errors between dma_ctrl_state_e <-> logic
  logic [$bits(dma_ctrl_state_e)-1:0] ctrl_state_logic;
  assign ctrl_state_q = dma_ctrl_state_e'(ctrl_state_logic);

  prim_flop #(
    .Width($bits(dma_ctrl_state_e)),
    .ResetValue(DmaIdle)
  ) aff_ctrl_state_q (
    .clk_i ( gated_clk        ),
    .rst_ni( rst_ni           ),
    .d_i   ( ctrl_state_d     ),
    .q_o   ( ctrl_state_logic )
  );

  logic [TRANSFER_BYTES_WIDTH-1:0] transfer_byte_q, transfer_byte_d;
  logic [TRANSFER_BYTES_WIDTH-1:0] remaining_bytes;
  logic                            capture_transfer_byte;
  prim_generic_flop_en #(
    .Width(TRANSFER_BYTES_WIDTH)
  ) aff_transfer_byte (
    .clk_i  ( gated_clk             ),
    .rst_ni ( rst_ni                ),
    .en_i   ( capture_transfer_byte ),
    .d_i    ( transfer_byte_d       ),
    .q_o    ( transfer_byte_q       )
  );

  logic       capture_transfer_width;
  logic [2:0] transfer_width_q, transfer_width_d;
  prim_generic_flop_en #(
    .Width(3)
  ) aff_transfer_width (
    .clk_i ( gated_clk              ),
    .rst_ni( rst_ni                 ),
    .en_i  ( capture_transfer_width ),
    .d_i   ( transfer_width_d       ),
    .q_o   ( transfer_width_q       )
  );

  logic                      capture_addr;
  logic [SYS_ADDR_WIDTH-1:0] src_addr_q, src_addr_d;
  logic [SYS_ADDR_WIDTH-1:0] dst_addr_q, dst_addr_d;
  prim_generic_flop_en #(
    .Width(SYS_ADDR_WIDTH)
  ) aff_src_addr (
    .clk_i ( gated_clk    ),
    .rst_ni( rst_ni       ),
    .en_i  ( capture_addr ),
    .d_i   ( src_addr_d   ),
    .q_o   ( src_addr_q   )
  );

  prim_generic_flop_en #(
    .Width(SYS_ADDR_WIDTH)
  ) aff_dst_addr (
    .clk_i ( gated_clk    ),
    .rst_ni( rst_ni       ),
    .en_i  ( capture_addr ),
    .d_i   ( dst_addr_d   ),
    .q_o   ( dst_addr_q   )
  );

  logic                       capture_be;
  logic [top_pkg::TL_DBW-1:0] req_src_be_q, req_src_be_d;
  logic [top_pkg::TL_DBW-1:0] req_dst_be_q, req_dst_be_d;
  prim_generic_flop_en #(
    .Width(top_pkg::TL_DBW)
  ) aff_req_src_be (
    .clk_i ( gated_clk    ),
    .rst_ni( rst_ni       ),
    .en_i  ( capture_be   ),
    .d_i   ( req_src_be_d ),
    .q_o   ( req_src_be_q )
  );

  prim_generic_flop_en #(
    .Width(top_pkg::TL_DBW)
  ) aff_req_dst_be (
    .clk_i ( gated_clk    ),
    .rst_ni( rst_ni       ),
    .en_i  ( capture_be   ),
    .d_i   ( req_dst_be_d ),
    .q_o   ( req_dst_be_q )
  );

  always_comb begin
    ctrl_state_d = ctrl_state_q;

    capture_transfer_byte  = 1'b0;
    transfer_byte_d        = transfer_byte_q;
    capture_transfer_width = 1'b0;
    transfer_width_d       = '0;

    next_error     = '0;
    bad_src_addr   = 1'b0;
    bad_dst_addr   = 1'b0;
    bad_opcode     = 1'b0;
    bad_size       = 1'b0;
    bad_base_limit = 1'b0;
    bad_go_config  = 1'b0;
    bad_asid       = 1'b0;
    config_error   = 1'b0;

    capture_addr = 1'b0;
    src_addr_d   = '0;
    dst_addr_d   = '0;

    capture_be   = '0;
    req_src_be_d = '0;
    req_dst_be_d = '0;

    dma_host_tlul_req_valid  = 1'b0;
    dma_host_tlul_req_addr   =   '0;
    dma_host_tlul_req_we     = 1'b0;
    dma_host_tlul_req_wdata  =   '0;
    dma_host_tlul_req_be     =   '0;

    dma_ctn_tlul_req_valid   = 1'b0;
    dma_ctn_tlul_req_addr    =   '0;
    dma_ctn_tlul_req_we      = 1'b0;
    dma_ctn_tlul_req_wdata   =   '0;
    dma_ctn_tlul_req_be      =   '0;

    sys_o.vld_vec            = '0;
    sys_o.metadata_vec       = '0;
    sys_o.opcode_vec         = { SysOpcWrite, SysOpcRead };
    sys_o.iova_vec           = '0;
    sys_o.racl_vec           = '0;
    sys_o.write_data         = '0;
    sys_o.write_be           = '0;
    sys_o.read_be            = '0;

    capture_host_return_data = 1'b0;
    capture_ctn_return_data  = 1'b0;
    capture_sys_return_data  = 1'b0;

    read_rsp_error  = 1'b0;
    dma_state_error = 1'b0;

    unique case (ctrl_state_q)
      DmaIdle: begin
        transfer_byte_d       = '0;
        capture_transfer_byte = 1'b1;
        // Wait for go bit to be set to proceed with data movement
        if (reg2hw.control.go.q) begin
          // if not handshake start transfer
          if (!cfg_handshake_en) begin
            ctrl_state_d = DmaAddrSetup;
          end else if (cfg_handshake_en && |lsio_trigger) begin // if handshake wait for interrupt
            ctrl_state_d = DmaClearPlic;
          end
        end
      end

      DmaClearPlic: begin
        dma_ctn_tlul_req_valid = 1'b1;
        dma_ctn_tlul_req_addr  = plic_clear_addr;  // TLUL 4B aligned
        dma_ctn_tlul_req_we    = 1'b1;
        dma_ctn_tlul_req_wdata = '0;
        dma_ctn_tlul_req_be    = {top_pkg::TL_DBW{1'b1}};

        if (dma_ctn_tlul_gnt) begin
          ctrl_state_d = DmaWaitClearPlicResponse;
        end
      end

      DmaWaitClearPlicResponse: begin
        // Writes also get a resp valid, but no data, need to wait for this to not
        // overrun TLUL adapter
        if (dma_ctn_tlul_rsp_valid) begin
          if (cfg_abort_en) begin
            ctrl_state_d = DmaIdle;
          end else begin
            ctrl_state_d = DmaAddrSetup;
          end
        end
      end

      DmaAddrSetup: begin
        capture_transfer_width = 1'b1;
        capture_addr           = 1'b1;
        capture_be             = 1'b1;

        // Value 2 (3-bytes represents an invalid config that leads to an error)
        unique case (reg2hw.transfer_width.q)
          2'b00:   transfer_width_d = 3'b001; // 1 byte
          2'b01:   transfer_width_d = 3'b010; // 2 bytes
          default: transfer_width_d = 3'b100; // 4 bytes
        endcase

        if ((transfer_byte_q == '0) ||
            (cfg_handshake_en     &&
            (!cfg_data_direction) &&
            (!cfg_fifo_auto_increment_en))) begin
          src_addr_d = {reg2hw.source_address_hi.q, reg2hw.source_address_lo.q};
        end else begin
          src_addr_d = src_addr_q + SYS_ADDR_WIDTH'(transfer_width_d);
        end

        if ((transfer_byte_q == '0) ||
            (cfg_handshake_en    &&
            (cfg_data_direction) &&
            (!cfg_fifo_auto_increment_en))) begin
          dst_addr_d = {reg2hw.destination_address_hi.q, reg2hw.destination_address_lo.q};
        end else begin
          dst_addr_d = dst_addr_q + SYS_ADDR_WIDTH'(transfer_width_d);
        end

        unique case (transfer_width_d)
          3'b001: begin
            req_dst_be_d = top_pkg::TL_DBW'('b0001) << dst_addr_d[1:0];
            req_src_be_d = top_pkg::TL_DBW'('b0001) << src_addr_d[1:0];
          end
          3'b010: begin
            if (remaining_bytes >= TRANSFER_BYTES_WIDTH'(transfer_width_d)) begin
              req_dst_be_d = top_pkg::TL_DBW'('b0011) << dst_addr_d[1:0];
              req_src_be_d = top_pkg::TL_DBW'('b0011) << src_addr_d[1:0];
            end else begin
              req_dst_be_d = top_pkg::TL_DBW'('b0001) << dst_addr_d[1:0];
              req_src_be_d = top_pkg::TL_DBW'('b0001) << src_addr_d[1:0];
            end
          end
          3'b100: begin
            if (remaining_bytes >= TRANSFER_BYTES_WIDTH'(transfer_width_d)) begin
              req_dst_be_d = {top_pkg::TL_DBW{1'b1}};
            end else begin
              unique case (remaining_bytes)
                TRANSFER_BYTES_WIDTH'('h1): req_dst_be_d = top_pkg::TL_DBW'('b0001);
                TRANSFER_BYTES_WIDTH'('h2): req_dst_be_d = top_pkg::TL_DBW'('b0011);
                TRANSFER_BYTES_WIDTH'('h3): req_dst_be_d = top_pkg::TL_DBW'('b0111);
                default:                    req_dst_be_d = top_pkg::TL_DBW'('b1111);
              endcase
            end

            req_src_be_d = req_dst_be_d;  // in the case of 4B src should always = dst
          end
          default: begin
            req_dst_be_d = top_pkg::TL_DBW'('b0000);
            req_src_be_d = top_pkg::TL_DBW'('b0000);
          end
        endcase

        // Error checking. An invalid configuration triggers one or more errors
        // and does not start the DMA transfer
        if ((reg2hw.total_data_size.q == '0) ||         // No 3-byte transfer width
            (reg2hw.transfer_width.q == 2'b10))  begin  // No empty transactions
          bad_size = 1'b1;
        end

        if (!(reg2hw.control.opcode.q inside {OpcCopy,
                                              OpcSha256,
                                              OpcSha384,
                                              OpcSha512})) begin
          bad_opcode = 1'b1;
        end

        // Ensure that ASIDs have valid values
        // SEC_CM: ASID.INTERSIG.MUBI
        if (!(reg2hw.address_space_id.source_asid.q inside {OtInternalAddr,
                                                            SocControlAddr,
                                                            SocSystemAddr,
                                                            OtExtFlashAddr})) begin
          bad_asid = 1'b1;
        end
        if (!(reg2hw.address_space_id.destination_asid.q inside {OtInternalAddr,
                                                                 SocControlAddr,
                                                                 SocSystemAddr,
                                                                 OtExtFlashAddr})) begin
          bad_asid = 1'b1;
        end

        if (reg2hw.enabled_memory_range_limit.q < reg2hw.enabled_memory_range_base.q) begin
          bad_base_limit = 1'b1;
        end

        // In 4-byte transfers, source and destination address must be 4-byte aligned
        if (reg2hw.transfer_width.q == 2'b11 && (|reg2hw.source_address_lo.q[1:0])) begin
          bad_src_addr = 1'b1;
        end
        if (reg2hw.transfer_width.q == 2'b11 && (|reg2hw.destination_address_lo.q[1:0])) begin
          bad_dst_addr = 1'b1;
        end

        // In 2-byte transfers, source and destination address must be 2-byte aligned
        if (reg2hw.transfer_width.q == 2'b01 && reg2hw.source_address_lo.q[0]) begin
          bad_src_addr = 1'b1;
        end
        if (reg2hw.transfer_width.q == 2'b01 && reg2hw.destination_address_lo.q[0]) begin
          bad_dst_addr = 1'b1;
        end

        // If data from the SOC system bus, the control bus, or the external flash is transferred to
        // the OT internal memory, we must check if the destination address range falls into the DMA
        // enabled memory region.
        if (((reg2hw.address_space_id.source_asid.q == SocControlAddr) ||
             (reg2hw.address_space_id.source_asid.q == SocSystemAddr)  ||
             (reg2hw.address_space_id.source_asid.q == OtExtFlashAddr)) &&
             (reg2hw.address_space_id.destination_asid.q == OtInternalAddr) &&
             // Out-of-bound check
             ((reg2hw.destination_address_lo.q > reg2hw.enabled_memory_range_limit.q) ||
              (reg2hw.destination_address_lo.q < reg2hw.enabled_memory_range_base.q)  ||
              ((SYS_ADDR_WIDTH'(reg2hw.destination_address_lo.q) +
                SYS_ADDR_WIDTH'(reg2hw.total_data_size.q)) >
                SYS_ADDR_WIDTH'(reg2hw.enabled_memory_range_limit.q)))) begin
            bad_dst_addr = 1'b1;
        end

        // If data from the OT internal memory is transferred  to the SOC system bus, the control
        // bus, or the external flash, we must check if the source address range falls into the DMA
        // enabled memory region.
        if (((reg2hw.address_space_id.destination_asid.q == SocControlAddr) ||
             (reg2hw.address_space_id.destination_asid.q == SocSystemAddr)  ||
             (reg2hw.address_space_id.destination_asid.q == OtExtFlashAddr)) &&
             (reg2hw.address_space_id.source_asid.q == OtInternalAddr) &&
              // Out-of-bound check
              ((reg2hw.source_address_lo.q > reg2hw.enabled_memory_range_limit.q) ||
               (reg2hw.source_address_lo.q < reg2hw.enabled_memory_range_base.q)  ||
               ((SYS_ADDR_WIDTH'(reg2hw.source_address_lo.q) +
                SYS_ADDR_WIDTH'(reg2hw.total_data_size.q)) >
                SYS_ADDR_WIDTH'(reg2hw.enabled_memory_range_limit.q)))) begin
          bad_src_addr = 1'b1;
        end

        // If the source ASID is the SOC control port, the OT internal port, or the external flash,
        //  we are accessing a 32-bit address space. Thus the upper bits of the source address must
        // be zero
        if (((reg2hw.address_space_id.source_asid.q == SocControlAddr) ||
             (reg2hw.address_space_id.source_asid.q == OtExtFlashAddr) ||
             (reg2hw.address_space_id.source_asid.q == OtInternalAddr)) &&
            (|reg2hw.source_address_hi.q)) begin
          bad_src_addr = 1'b1;
        end

        // If the desitination ASID is the SOC control port, the OT internal port or the external
        // flash, we are accessing a 32-bit address space. Thus the upper bits of the destination
        // address must be zero
        if (((reg2hw.address_space_id.destination_asid.q == SocControlAddr) ||
             (reg2hw.address_space_id.destination_asid.q == OtExtFlashAddr) ||
             (reg2hw.address_space_id.destination_asid.q == OtInternalAddr)) &&
            (|reg2hw.destination_address_hi.q)) begin
          bad_dst_addr = 1'b1;
        end

        if (mubi4_test_true_loose(mubi4_t'(reg2hw.range_unlock_regwen.q))) begin
          bad_go_config = 1'b1;
        end

        config_error = bad_src_addr   ||
                       bad_dst_addr   ||
                       bad_size       ||
                       bad_base_limit ||
                       bad_opcode     ||
                       bad_go_config  ||
                       bad_asid;

        if (config_error) begin
          next_error[DmaSourceAddrErr]      = bad_src_addr;
          next_error[DmaDestinationAddrErr] = bad_dst_addr;
          next_error[DmaOpcodeErr]          = bad_opcode;
          next_error[DmaSizeErr]            = bad_size;
          next_error[DmaBaseLimitErr]       = bad_base_limit;
          next_error[DmaGoConfigErr]        = bad_go_config;
          next_error[DmaAsidErr]            = bad_asid;

          ctrl_state_d = DmaError;
        end else if (cfg_abort_en) begin
          ctrl_state_d = DmaIdle;
        end else if ((reg2hw.address_space_id.source_asid.q == SocControlAddr) ||
                     (reg2hw.address_space_id.source_asid.q == OtExtFlashAddr)) begin
          ctrl_state_d = DmaSendCtnRead;
        end else if (reg2hw.address_space_id.source_asid.q == SocSystemAddr) begin
          ctrl_state_d = DmaSendSysRead;
        end else begin
          ctrl_state_d = DmaSendHostRead;
        end
      end

      DmaSendHostRead: begin
        dma_host_tlul_req_valid = 1'b1;
        dma_host_tlul_req_addr  = {src_addr_q[top_pkg::TL_AW-1:2], 2'b0}; // TLUL 4B aligned
        dma_host_tlul_req_be    = req_src_be_q;

        if (dma_host_tlul_gnt) begin
          ctrl_state_d = DmaWaitHostReadResponse;
        end else if (cfg_abort_en) begin
          ctrl_state_d = DmaIdle;
        end
      end

      DmaWaitHostReadResponse: begin
        read_rsp_error           = dma_host_tlul_rsp_err || dma_host_tlul_rsp_intg_err;
        capture_host_return_data = dma_host_tlul_rsp_valid && (!read_rsp_error);

        if (dma_host_tlul_rsp_valid) begin
          if (read_rsp_error) begin
            next_error[DmaCompletionErr] = 1'b1;

            ctrl_state_d = DmaError;
          end else if (cfg_abort_en) begin
            ctrl_state_d = DmaIdle;
          end else begin
            unique case (reg2hw.address_space_id.destination_asid.q)
              SocControlAddr: ctrl_state_d = DmaSendCtnWrite;
              OtExtFlashAddr: ctrl_state_d = DmaSendCtnWrite;
              SocSystemAddr:  ctrl_state_d = DmaSendSysWrite;
              OtInternalAddr: ctrl_state_d = DmaSendHostWrite;
              default: begin
                next_error[DmaAsidErr] = 1'b1;
                ctrl_state_d = DmaError;
              end
            endcase
          end
        end
      end

      DmaSendCtnRead: begin
        dma_ctn_tlul_req_valid = 1'b1;
        dma_ctn_tlul_req_addr  = {src_addr_q[top_pkg::TL_AW-1:2], 2'b0}; // TLUL 4B aligned
        dma_ctn_tlul_req_be    = req_src_be_q;

        if (dma_ctn_tlul_gnt) begin
          ctrl_state_d = DmaWaitCtnReadResponse;
        end else if (cfg_abort_en) begin
          ctrl_state_d = DmaIdle;
        end
      end

      DmaWaitCtnReadResponse: begin
        read_rsp_error           = dma_ctn_tlul_rsp_err || dma_ctn_tlul_rsp_intg_err;
        capture_ctn_return_data = dma_ctn_tlul_rsp_valid && (!read_rsp_error);

        if (dma_ctn_tlul_rsp_valid) begin
          if (read_rsp_error) begin
            next_error[DmaCompletionErr] = 1'b1;

            ctrl_state_d = DmaError;
          end else if (cfg_abort_en) begin
            ctrl_state_d = DmaIdle;
          end else begin
            unique case (reg2hw.address_space_id.destination_asid.q)
              SocControlAddr: ctrl_state_d = DmaSendCtnWrite;
              OtExtFlashAddr: ctrl_state_d = DmaSendCtnWrite;
              SocSystemAddr:  ctrl_state_d = DmaSendSysWrite;
              OtInternalAddr: ctrl_state_d = DmaSendHostWrite;
              default: begin
                next_error[DmaAsidErr] = 1'b1;
                ctrl_state_d = DmaError;
              end
            endcase
          end
        end
      end

      DmaSendSysRead: begin
        sys_o.vld_vec     [SysCmdRead] = 1'b1;
        sys_o.metadata_vec[SysCmdRead] = src_metadata;
        sys_o.opcode_vec  [SysCmdRead] = SysOpcRead;
        sys_o.iova_vec    [SysCmdRead] = {src_addr_q[(SYS_ADDR_WIDTH-1):2], 2'b0};
        sys_o.racl_vec    [SysCmdRead] = SysRacl[SYS_RACL_WIDTH-1:0];
        sys_o.read_be                  = req_src_be_q;

        if (sys_i.grant_vec[SysCmdRead]) begin
          ctrl_state_d = DmaWaitSysReadResponse;
        end else if (cfg_abort_en) begin
          ctrl_state_d = DmaIdle;
        end
      end

      DmaWaitSysReadResponse: begin
        read_rsp_error          = sys_i.read_data_vld && sys_i.error_vld;
        capture_sys_return_data = sys_i.read_data_vld && (!sys_i.error_vld);

        if (sys_i.read_data_vld) begin
          if (read_rsp_error) begin
            next_error[DmaCompletionErr] = 1'b1;

            ctrl_state_d = DmaError;
          end else if (cfg_abort_en) begin
            ctrl_state_d = DmaIdle;
          end else begin
            unique case (reg2hw.address_space_id.destination_asid.q)
              SocControlAddr: ctrl_state_d = DmaSendCtnWrite;
              OtExtFlashAddr: ctrl_state_d = DmaSendCtnWrite;
              SocSystemAddr:  ctrl_state_d = DmaSendSysWrite;
              OtInternalAddr: ctrl_state_d = DmaSendHostWrite;
              default: begin
                next_error[DmaAsidErr] = 1'b1;
                ctrl_state_d = DmaError;
              end
            endcase
          end
        end
      end

      DmaSendHostWrite: begin
        dma_host_tlul_req_valid = 1'b1;
        dma_host_tlul_req_addr  = {dst_addr_q[top_pkg::TL_AW-1:2], 2'b0};  // TLUL 4B aligned
        dma_host_tlul_req_we    = 1'b1;
        dma_host_tlul_req_wdata = read_return_data_q;
        dma_host_tlul_req_be    = req_dst_be_q;

        if (dma_host_tlul_gnt) begin
          ctrl_state_d = DmaWaitHostWriteResponse;
        end else if (cfg_abort_en) begin
          ctrl_state_d = DmaIdle;
        end
      end

      DmaWaitHostWriteResponse: begin
        // writes also get a resp valid, but no data, need to wait for this to not
        // overrun tlul adapter
        if (dma_host_tlul_rsp_valid) begin
          transfer_byte_d       = transfer_byte_q + TRANSFER_BYTES_WIDTH'(transfer_width_q);
          capture_transfer_byte = 1'b1;

          if (cfg_abort_en) begin
            ctrl_state_d = DmaIdle;
          end else if (remaining_bytes <= TRANSFER_BYTES_WIDTH'(transfer_width_q)) begin
            ctrl_state_d = DmaIdle;
          end else begin
            ctrl_state_d = DmaAddrSetup;
          end
        end
      end

      DmaSendCtnWrite: begin
        dma_ctn_tlul_req_valid = 1'b1;
        dma_ctn_tlul_req_addr  = {dst_addr_q[top_pkg::TL_AW-1:2], 2'b0};  // TLUL 4B aligned
        dma_ctn_tlul_req_we    = 1'b1;
        dma_ctn_tlul_req_wdata = read_return_data_q;
        dma_ctn_tlul_req_be    = req_dst_be_q;

        if (dma_ctn_tlul_gnt) begin
          ctrl_state_d = DmaWaitCtnWriteResponse;
        end else if (cfg_abort_en) begin
          ctrl_state_d = DmaIdle;
        end
      end

      DmaWaitCtnWriteResponse: begin
        // writes also get a resp valid, but no data, need to wait for this to not
        // overrun tlul adapter
        if (dma_ctn_tlul_rsp_valid) begin
          transfer_byte_d       = transfer_byte_q + TRANSFER_BYTES_WIDTH'(transfer_width_q);
          capture_transfer_byte = 1'b1;

          if (cfg_abort_en) begin
            ctrl_state_d = DmaIdle;
          end else if (remaining_bytes <= TRANSFER_BYTES_WIDTH'(transfer_width_q)) begin
            ctrl_state_d = DmaIdle;
          end else begin
            ctrl_state_d = DmaAddrSetup;
          end
        end
      end

      DmaSendSysWrite: begin
        sys_o.vld_vec     [SysCmdWrite] = 1'b1;
        sys_o.metadata_vec[SysCmdWrite] = src_metadata;
        sys_o.opcode_vec  [SysCmdWrite] = SysOpcWrite;
        sys_o.iova_vec    [SysCmdWrite] = {dst_addr_q[(SYS_ADDR_WIDTH-1):2], 2'b0};
        sys_o.racl_vec    [SysCmdWrite] = SysRacl[SysOpcWrite-1:0];

        sys_o.write_data = read_return_data_q;
        sys_o.write_be   = req_dst_be_q;

        if (sys_i.grant_vec[SysCmdWrite]) begin
          transfer_byte_d       = transfer_byte_q + TRANSFER_BYTES_WIDTH'(transfer_width_q);
          capture_transfer_byte = 1'b1;

          if (remaining_bytes <= TRANSFER_BYTES_WIDTH'(transfer_width_q)) begin
            ctrl_state_d = DmaIdle;
          end else begin
            ctrl_state_d = DmaAddrSetup;
          end
        end else if (cfg_abort_en) begin
          ctrl_state_d = DmaIdle;
        end
      end

      DmaError: begin
        // wait here until error is cleared
        if (!reg2hw.status.error.q) begin
          ctrl_state_d = DmaIdle;
        end
      end

      default: begin
        // Should not be reachable
        dma_state_error = 1'b1;
      end
    endcase
  end

  always_comb begin
    read_return_data_d = '0;
    if (capture_host_return_data) read_return_data_d = dma_host_tlul_rsp_data;
    if (capture_ctn_return_data)  read_return_data_d = dma_ctn_tlul_rsp_data;
    if (capture_sys_return_data)  read_return_data_d = sys_i.read_data;
  end

  assign capture_return_data = capture_host_return_data ||
                               capture_ctn_return_data  ||
                               capture_sys_return_data;
  prim_generic_flop_en #(
    .Width(top_pkg::TL_DW)
  ) aff_read_return_data (
    .clk_i ( gated_clk             ),
    .rst_ni( rst_ni                ),
    .en_i  ( capture_return_data   ),
    .d_i   ( read_return_data_d    ),
    .q_o   ( read_return_data_q    )
  );

  logic test_done_interrupt;
  logic test_error_interrupt;
  logic test_memory_buffer_limit_interrupt;
  logic send_memory_buffer_limit_interrupt;
  logic data_move_state, data_move_state_valid;
  logic update_destination_addr_reg, update_source_addr_reg;

  assign test_done_interrupt  = reg2hw.intr_test.dma_done.q  && reg2hw.intr_test.dma_done.qe;
  assign test_error_interrupt = reg2hw.intr_test.dma_error.q && reg2hw.intr_test.dma_error.qe;
  assign test_memory_buffer_limit_interrupt =
    reg2hw.intr_test.dma_memory_buffer_limit.q &&
    reg2hw.intr_test.dma_memory_buffer_limit.qe;

  // Signal interrupt controller whenever an enabled interrupt info bit is set
  assign intr_dma_done_o  = reg2hw.intr_state.dma_done.q  && reg2hw.intr_enable.dma_done.q;
  assign intr_dma_error_o = reg2hw.intr_state.dma_error.q && reg2hw.intr_enable.dma_error.q;
  assign intr_dma_memory_buffer_limit_o = reg2hw.intr_state.dma_memory_buffer_limit.q &&
                                          reg2hw.intr_enable.dma_memory_buffer_limit.q;

  // Calculate remaining amount of data
  assign remaining_bytes = reg2hw.total_data_size.q - transfer_byte_q;

  assign data_move_state_valid =
    (dma_host_tlul_req_valid && (ctrl_state_q == DmaSendHostWrite)) ||
    (dma_ctn_tlul_req_valid  && (ctrl_state_q == DmaSendCtnWrite))  ||
    ((sys_o.vld_vec[SysCmdWrite]    &&
      sys_i.grant_vec[SysCmdWrite]) &&
     (ctrl_state_q == DmaSendSysWrite));

  assign data_move_state = (ctrl_state_q == DmaSendHostWrite)         ||
                           (ctrl_state_q == DmaWaitHostWriteResponse) ||
                           (ctrl_state_q == DmaSendCtnWrite)          ||
                           (ctrl_state_q == DmaWaitCtnWriteResponse)  ||
                           (ctrl_state_q == DmaSendSysWrite);

  // Destination limit logic, only want to trigger for single cycle when data has moved
  assign send_memory_buffer_limit_interrupt =
    data_move_state_valid               &&
    cfg_handshake_en                    &&
    cfg_memory_buffer_auto_increment_en &&
    !cfg_data_direction                 &&
    ((dst_addr_q >= {reg2hw.destination_address_limit_hi.q,
                     reg2hw.destination_address_limit_lo.q})       ||
     (dst_addr_q >= {reg2hw.destination_address_almost_limit_hi.q,
                     reg2hw.destination_address_almost_limit_lo.q}));

  assign new_destination_addr = cfg_data_direction ?
    ({reg2hw.destination_address_hi.q, reg2hw.destination_address_lo.q} +
     SYS_ADDR_WIDTH'(transfer_width_q)) :
    ({reg2hw.destination_address_hi.q, reg2hw.destination_address_lo.q} +
     SYS_ADDR_WIDTH'(reg2hw.total_data_size.q));

  assign new_source_addr = cfg_data_direction ?
    ({reg2hw.source_address_hi.q, reg2hw.source_address_lo.q} +
      SYS_ADDR_WIDTH'(reg2hw.total_data_size.q)) :
    ({reg2hw.source_address_hi.q, reg2hw.source_address_lo.q} +
      SYS_ADDR_WIDTH'(transfer_width_q));

  always_comb begin
    hw2reg = '0;

    // If we are in hardware handshake mode with auto-increment increment the corresponding address
    // when finishing a DMA operation when transitioning from a data move state to the idle state
    update_destination_addr_reg = 1'b0;
    update_source_addr_reg      = 1'b0;
    if (cfg_handshake_en && cfg_memory_buffer_auto_increment_en &&
        data_move_state && (ctrl_state_d == DmaIdle)) begin
      if (cfg_data_direction) begin
        update_source_addr_reg = 1'b1;
      end else begin
        update_destination_addr_reg = 1'b1;
      end
    end

    hw2reg.destination_address_hi.de = update_destination_addr_reg;
    hw2reg.destination_address_hi.d  = new_destination_addr[63:32];

    hw2reg.destination_address_lo.de = update_destination_addr_reg;
    hw2reg.destination_address_lo.d  = new_destination_addr[31:0];

    hw2reg.source_address_hi.de = update_source_addr_reg;
    hw2reg.source_address_hi.d  = new_source_addr[63:32];

    hw2reg.source_address_lo.de = update_source_addr_reg;
    hw2reg.source_address_lo.d  = new_source_addr[31:0];

    // if all data has been transferred successfully and not in hardware
    // handshake mode, then clear the go bit
    hw2reg.control.go.de = ((!cfg_handshake_en) &&
                             data_move_state    &&
                            (ctrl_state_d == DmaIdle)) ||
                            (cfg_abort_en && (ctrl_state_d == DmaIdle));

    hw2reg.control.go.d  = 1'b0;

    // Assert wr wen on transitions from and to IDLE
    hw2reg.status.busy.de = ((ctrl_state_q  == DmaIdle) && (ctrl_state_d != DmaIdle)) ||
                            ((ctrl_state_q  != DmaIdle) && (ctrl_state_d == DmaIdle));
    // If transitioning from IDLE, set busy, otherwise clear it
    hw2reg.status.busy.d  = ((ctrl_state_q == DmaIdle) &&
                            (ctrl_state_d != DmaIdle)) ? 1'b1 : 1'b0;

    // SW must clear done bit in handshake mode
    // a transaction should not indicated done when aborted
    hw2reg.status.done.de = (!cfg_handshake_en) &&
                            (!cfg_abort_en)     &&
                             data_move_state    &&
                            (ctrl_state_d == DmaIdle);

    hw2reg.status.done.d  = 1'b1;

    hw2reg.status.error.de = (ctrl_state_d == DmaError);
    hw2reg.status.error.d  = 1'b1;

    hw2reg.status.error_code.de = (ctrl_state_d == DmaError);
    hw2reg.status.error_code.d  = next_error;

    hw2reg.status.aborted.de = cfg_abort_en && (ctrl_state_d == DmaIdle);
    hw2reg.status.aborted.d  = 1'b1;

    // interrupt management
    hw2reg.intr_state.dma_done.de = reg2hw.status.done.q | test_done_interrupt;
    hw2reg.intr_state.dma_done.d  = 1'b1;

    hw2reg.intr_state.dma_error.de = reg2hw.status.error.q | test_error_interrupt;
    hw2reg.intr_state.dma_error.d  = 1'b1;

    hw2reg.intr_state.dma_memory_buffer_limit.de = send_memory_buffer_limit_interrupt |
                                                   test_memory_buffer_limit_interrupt;
    hw2reg.intr_state.dma_memory_buffer_limit.d  = 1'b1;

    // write to clear state register, value doesn't matter
    // clearing overrides new setting, and needs to be the last thing in this always_comb
    if (reg2hw.clear_state.qe) begin
      hw2reg.status.done.de = 1'b1;
      hw2reg.status.done.d  = 1'b0;

      hw2reg.status.error.de = 1'b1;
      hw2reg.status.error.d  = 1'b0;

      hw2reg.status.error_code.de = 1'b1;
      hw2reg.status.error_code.d  = {$bits(hw2reg.status.error_code.d){1'b0}};

      hw2reg.status.aborted.de = 1'b1;
      hw2reg.status.aborted.d  = 1'b0;

      hw2reg.intr_state.dma_done.de = 1'b1;
      hw2reg.intr_state.dma_done.d  = 1'b0;

      hw2reg.intr_state.dma_error.de = 1'b1;
      hw2reg.intr_state.dma_error.d  = 1'b0;

      hw2reg.intr_state.dma_memory_buffer_limit.de = 1'b1;
      hw2reg.intr_state.dma_memory_buffer_limit.d  = 1'b0;
    end
  end

  always_comb begin
    cfg_handshake_en                    = reg2hw.control.hardware_handshake_enable.q;
    cfg_data_direction                  = reg2hw.control.data_direction.q;
    cfg_fifo_auto_increment_en          = reg2hw.control.fifo_auto_increment_enable.q;
    cfg_memory_buffer_auto_increment_en = reg2hw.control.memory_buffer_auto_increment_enable.q;
    cfg_abort_en                        = reg2hw.control.abort.q;
  end

  // All outputs should be known value after reset
  `ASSERT_KNOWN(AlertsKnown_A, alert_tx_o)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_dma_reg, alert_tx_o[0])

  // Handshake interrupt enable register must be expanded if there are more than 32 handshake
  // trigger wires
  `ASSERT_NEVER(LimitHandshakeTriggerWires_A, NumLsioTriggers > 32)

  // The RTL code assumes the BE signal is 4-bit wide
  `ASSERT_NEVER(BeLengthMustBe4_A, top_pkg::TL_DBW != 4)

  // There should be no register writes after GO bit is set
  `ASSERT_NEVER(NoRegWritesAfterGo_A, reg2hw.control.go && sw_reg_wr)

  // The DMA enabled memory should not be changed after lock
  `ASSERT_NEVER(NoDmaEnabledMemoryChangeAfterLock_A,
                prim_mubi_pkg::mubi4_test_false_loose(
                  prim_mubi_pkg::mubi4_t'(reg2hw.range_unlock_regwen.q)) &&
                  (reg2hw.enabled_memory_range_base.qe ||
                  reg2hw.enabled_memory_range_limit.qe))
endmodule
