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
  parameter int unsigned CfgSramDataWidth      = 32
) (
  input  logic                                      clk_i,
  input  logic                                      rst_ni,
  output logic                                      intr_mbx_ready_o,
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
  logic hostif_set_control_abort;
  logic hostif_clear_status_busy;
  logic hostif_set_status_error, hostif_clear_status_error;
  logic hostif_set_status_async_msg_status;
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
  logic [11:0] hostif_ob_object_size_wdata, hostif_ob_object_size_rdata;

  logic sysif_write_control_abort, hostif_event_intr;

  mbx_hostif #(
    .AlertAsyncOn    ( AlertAsyncOn     ),
    .CfgSramAddrWidth( CfgSramAddrWidth )
  ) u_hostif (
    .clk_i                               ( clk_i                              ),
    .rst_ni                              ( rst_ni                             ),
    // Device port to the host side
    .tl_host_i                           ( tl_host_i                          ),
    .tl_host_o                           ( tl_host_o                          ),
    .event_intr_i                        ( hostif_event_intr                  ),
    .irq_o                               ( irq_o                              ),
    .alert_rx_i                          ( alert_rx_i                         ),
    .alert_tx_o                          ( alert_tx_o                         ),
    // Access to the control register
    .hostif_set_control_abort_o          ( hostif_set_control_abort           ),
    // Access to the status register
    .hostif_clear_status_busy_o          ( hostif_clear_status_busy           ),
    .hostif_set_status_error_o           ( hostif_set_status_error            ),
    .hostif_clear_status_error_o         ( hostif_clear_status_error          ),
    .hostif_set_status_async_msg_status_o( hostif_set_status_async_msg_status ),
    .hostif_status_busy_i                ( hostif_status_busy                 ),
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


endmodule
