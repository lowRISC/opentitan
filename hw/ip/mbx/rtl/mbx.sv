// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module mbx
  import tlul_pkg::*;
  import mbx_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
  parameter int unsigned CfgSramAddrWidth      = 32,
  parameter int unsigned CfgSramDataWidth      = 32,
  parameter int unsigned NextExtDoeOffset      = 12'h800,
  // PCIe capabilities
  parameter bit DoeIrqSupport                  = 1'b1
) (
  input  logic                                      clk_i,
  input  logic                                      rst_ni,
  // Comportable interrupt to the OT
  output logic                                      intr_mbx_ready_o,
  // Custom interrupt to the system requester
  output logic                                      doe_intr_support_o,
  output logic                                      doe_intr_en_o,
  output logic                                      doe_intr_o,
  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,
  // Device port facing OT-host
  input   tlul_pkg::tl_h2d_t                        tl_host_i,
  output  tlul_pkg::tl_d2h_t                        tl_host_o,
  // Device port facing CTN Xbar
  input   tlul_pkg::tl_h2d_t                        tl_sys_i,
  output  tlul_pkg::tl_d2h_t                        tl_sys_o,
  // Host port to access private SRAM
  input   tlul_pkg::tl_d2h_t                        tl_sram_i,
  output  tlul_pkg::tl_h2d_t                        tl_sram_o
);
  logic [CfgSramAddrWidth-1:0] ib_write_ptr;
  logic [CfgSramAddrWidth-1:0] ob_read_ptr;

  // External write signals for control and status register
  logic hostif_control_abort_set;
  logic hostif_status_busy_clear;
  logic hostif_status_error_set, hostif_status_error_clear;
  logic hostif_status_async_msg_status_set;
  // External read signals for control and status register
  logic hostif_status_busy, hostif_status_error;
  logic hostif_status_async_msg_status, hostif_status_ready;

  logic [CfgSramAddrWidth-1:0] ibmbx_hostif_sram_write_ptr;
  logic [CfgSramDataWidth-1:0] ibmbx_write_data;
  logic [CfgSramAddrWidth-1:0] obmbx_hostif_sram_read_ptr;
  logic [CfgSramDataWidth-1:0] obmbx_hostif_sram_read_resp;

  logic hostif_address_range_valid;
  logic [CfgSramAddrWidth-1:0] hostif_ib_base, hostif_ib_limit;
  logic [CfgSramAddrWidth-1:0] hostif_ob_base, hostif_ob_limit;

  logic hostif_write_ob_object_size, hostif_read_ob_object_size;
  logic [10:0] hostif_ob_object_size_wdata, hostif_ob_object_size_rdata;

  logic sysif_status_doe_intr_status, sysif_status_doe_intr_status_set;
  logic sysif_write_control_abort, hostif_event_intr;
  logic sysif_intg_err;

  mbx_hostif #(
    .AlertAsyncOn    ( AlertAsyncOn     ),
    .CfgSramAddrWidth( CfgSramAddrWidth )
  ) u_hostif (
    .clk_i                               ( clk_i                              ),
    .rst_ni                              ( rst_ni                             ),
    // Device port to the host side
    .tl_host_i                           ( tl_host_i                          ),
    .tl_host_o                           ( tl_host_o                          ),
    .intg_err_i                          ( sysif_intg_err                     ),
    .event_intr_i                        ( hostif_event_intr                  ),
    .irq_o                               ( intr_mbx_ready_o                   ),
    .alert_rx_i                          ( alert_rx_i                         ),
    .alert_tx_o                          ( alert_tx_o                         ),
    // Access to the control register
    .hostif_control_abort_set_o          ( hostif_control_abort_set           ),
    // Access to the status register
    .hostif_status_busy_clear_o          ( hostif_status_busy_clear           ),
    .hostif_status_doe_intr_status_set_o ( sysif_status_doe_intr_status_set   ),
    .hostif_status_error_set_o           ( hostif_status_error_set            ),
    .hostif_status_error_clear_o         ( hostif_status_error_clear          ),
    .hostif_status_async_msg_status_set_o( hostif_status_async_msg_status_set ),
    .hostif_status_busy_i                ( hostif_status_busy                 ),
    .hostif_status_doe_intr_status_i     ( sysif_status_doe_intr_status     ),
    .hostif_status_error_i               ( hostif_status_error                ),
    .hostif_status_async_msg_status_i    ( hostif_status_async_msg_status     ),
    .hostif_status_ready_i               ( hostif_status_ready                ),
    // Access to the IB/OB RD/WR Pointers
    .hostif_ib_write_ptr_i               ( ibmbx_hostif_sram_write_ptr        ),
    .hostif_ob_read_ptr_i                ( obmbx_hostif_sram_read_ptr         ),
    // Access to the memory region registers
    .hostif_address_range_valid_o        ( hostif_address_range_valid         ),
    .hostif_ib_base_o                    ( hostif_ib_base                     ),
    .hostif_ib_limit_o                   ( hostif_ib_limit                    ),
    .hostif_ob_base_o                    ( hostif_ob_base                     ),
    .hostif_ob_limit_o                   ( hostif_ob_limit                    ),
    // Read/Write access for the OB DW Count register
    .hostif_write_ob_object_size_o      ( hostif_write_ob_object_size         ),
    .hostif_ob_object_size_o            ( hostif_ob_object_size_wdata         ),
    .hostif_ob_object_size_i            ( hostif_ob_object_size_rdata         ),
    .hostif_read_ob_object_size_i       ( hostif_read_ob_object_size          ),
    // Control inputs coming from the system registers interface
    .sysif_write_control_abort_i         ( sysif_write_control_abort          )
  );

  logic ibmbx_pending, obmbx_pending;
  logic ibmbx_status_busy_valid, ibmbx_status_busy;
  logic obmbx_status_ready_valid, obmbx_status_ready;

  logic sysif_control_go_set, sysif_control_abort_set, sysif_control_async_msg_en;

  logic sysif_status_intr_support, sysif_status_intr_en;
  logic sysif_status_async_msg_status_set, sysif_status_async_msg_status;

  logic sysif_write_data_write_valid;
  logic [CfgSramDataWidth-1:0] sysif_write_data, sysif_read_data;
  logic sysif_read_data_read_valid, sysif_read_data_write_valid;

  mbx_sysif #(
    .CfgSramDataWidth ( CfgSramDataWidth ),
    .NextExtDoeOffset ( NextExtDoeOffset ),
    .DoeIrqSupport    ( DoeIrqSupport    )
  ) u_sysif (
    .clk_i                               ( clk_i                              ),
    .rst_ni                              ( rst_ni                             ),
    .tl_sys_i                            ( tl_sys_i                           ),
    .tl_sys_o                            ( tl_sys_o                           ),
    .intg_err_o                          ( sysif_intg_err                     ),
    // System interrupt support
    .doe_intr_support_o                  ( doe_intr_support_o                 ),
    .doe_intr_en_o                       ( doe_intr_en_o                      ),
    .doe_intr_o                          ( doe_intr_o                         ),
    // Access to the control register
    .sysif_control_abort_set_o           ( sysif_control_abort_set            ),
    .sysif_control_async_msg_en_o        ( sysif_control_async_msg_en),
    .sysif_control_go_set_o              ( sysif_control_go_set               ),
    // Access to the status register
    .sysif_status_busy_valid_i           ( ibmbx_status_busy_valid            ),
    .sysif_status_busy_i                 ( ibmbx_status_busy                  ),
    .sysif_status_doe_intr_status_set_i  ( sysif_status_doe_intr_status_set   ),
    .sysif_status_doe_intr_status_o      ( sysif_status_doe_intr_status       ),
    .sysif_status_error_set_i            ( hostif_status_error_set            ),
    .sysif_status_error_clear_i          ( hostif_status_error_clear          ),
    .sysif_status_async_msg_status_o     ( sysif_status_async_msg_status      ),
    .sysif_status_async_msg_status_set_i ( sysif_status_async_msg_status_set  ),
    .sysif_status_ready_valid_i          ( obmbx_status_ready_valid           ),
    .sysif_status_ready_i                ( obmbx_status_ready                 ),
    // Control lines for backpressuring the bus
    .ibmbx_pending_i                     ( ibmbx_pending                      ),
    .obmbx_pending_i                     ( obmbx_pending                      ),
    // Data interface for inbound and outbound mailbox
    .write_data_write_valid_o            ( sysif_write_data_write_valid       ),
    .write_data_o                        ( sysif_write_data                   ),
    .read_data_i                         ( sysif_read_data                    ),
    .read_data_read_valid_o              ( sysif_read_data_read_valid         ),
    .read_data_write_valid_o             ( sysif_read_data_write_valid        )
  );

endmodule
