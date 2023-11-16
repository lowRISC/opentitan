// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module mbx_hostif
  import mbx_reg_pkg::*;
#(
    parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}},
    parameter int unsigned CfgSramAddrWidth      = 32,
    parameter int unsigned CfgSramDataWidth      = 32,
    parameter int unsigned CfgObjectSizeWidth    = 11
) (
  input  logic                          clk_i,
  input  logic                          rst_ni,
  // Device port to the host side
  input  tlul_pkg::tl_h2d_t             tl_host_i,
  output tlul_pkg::tl_d2h_t             tl_host_o,
  // Generated interrupt event
  input  logic                          event_intr_ready_i,
  input  logic                          event_intr_abort_i,
  input  logic                          event_intr_error_i,
  output logic                          intr_ready_o,
  output logic                          intr_abort_o,
  output logic                          intr_error_o,
  // External errors
  input  logic                          intg_err_i,
  input  logic                          sram_err_i,
  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,
  // Access to the control register
  // Writing a 1 to control.abort register clears the abort condition
  output logic                          hostif_control_abort_clear_o,
  output logic                          hostif_control_error_set_o,
  input  logic                          hostif_control_error_i,
  output logic                          hostif_control_async_msg_set_o,
  output logic                          hostif_control_async_msg_clear_o,
  // Access to the status register
  input  logic                          hostif_status_busy_i,
  input  logic                          hostif_status_sys_intr_en_i,
  input  logic                          hostif_status_sys_async_en_i,
  input  logic                          hostif_status_sys_intr_state_i,
  // Access to the IB/OB RD/WR pointers
  input  logic [CfgSramAddrWidth-1:0]   hostif_imbx_write_ptr_i,
  input  logic [CfgSramAddrWidth-1:0]   hostif_ombx_read_ptr_i,
  // Base/Limit for in/outbound mailbox
  output logic                          hostif_address_range_valid_write_o,
  output logic                          hostif_address_range_valid_o,
  output logic [CfgSramAddrWidth-1:0]   hostif_imbx_base_o,
  output logic [CfgSramAddrWidth-1:0]   hostif_imbx_limit_o,
  output logic [CfgSramAddrWidth-1:0]   hostif_ombx_base_o,
  output logic [CfgSramAddrWidth-1:0]   hostif_ombx_limit_o,
  // Read/Write access for the object size register
  output logic                          hostif_ombx_object_size_write_o,
  output logic [CfgObjectSizeWidth-1:0] hostif_ombx_object_size_o,
  input  logic                          hostif_ombx_object_size_update_i,
  input  logic [CfgObjectSizeWidth-1:0] hostif_ombx_object_size_i,
  // Alias of the interrupt address and data registers from the SYS interface
  input  logic [CfgSramAddrWidth-1:0]   sysif_intr_msg_addr_i,
  input  logic [CfgSramDataWidth-1:0]   sysif_intr_msg_data_i,
  // Control inputs coming from the system registers interface
  input  logic                          sysif_control_abort_set_i
);
  mbx_reg_pkg::mbx_core_reg2hw_t reg2hw;
  mbx_reg_pkg::mbx_core_hw2reg_t hw2reg;

  //////////////////////////////////////////////////////////////////////////////
  // Assertions
  //////////////////////////////////////////////////////////////////////////////
  logic tlul_intg_err;
  logic [NumAlerts-1:0] alert_test, alerts;

  assign alert_test = {
    reg2hw.alert_test.recov_fault.q & reg2hw.alert_test.recov_fault.qe,
    reg2hw.alert_test.fatal_fault.q & reg2hw.alert_test.fatal_fault.qe
  };

  assign alerts[0] = tlul_intg_err | intg_err_i;
  assign alerts[1] = sram_err_i;

  localparam logic [NumAlerts-1:0] IsFatal = {1'b0, 1'b1};
  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn ( AlertAsyncOn[i] ),
      .IsFatal ( IsFatal[i]      )
    ) u_prim_alert_sender (
    .clk_i          ( clk_i         ),
    .rst_ni         ( rst_ni        ),
      .alert_test_i ( alert_test[i] ),
      .alert_req_i  ( alerts[i]     ),
      .alert_ack_o  (               ),
      .alert_state_o(               ),
      .alert_rx_i   ( alert_rx_i[i] ),
      .alert_tx_o   ( alert_tx_o[i] )
    );
  end

  // SEC_CM: BUS.INTEGRITY
  // SEC_CM: ADDRESS_RANGE.CONFIG.REGWEN_MUBI
  mbx_core_reg_top u_regs(
    .clk_i      ( clk_i         ),
    .rst_ni     ( rst_ni        ),
    .tl_i       ( tl_host_i     ),
    .tl_o       ( tl_host_o     ),
    .reg2hw     ( reg2hw        ),
    .hw2reg     ( hw2reg        ),
    .intg_err_o ( tlul_intg_err ),
    .devmode_i  ( 1'b1          )
  );

  // Instantiate interrupt hardware primitives for ready and abort IRQ
  prim_intr_hw #(.Width(1)) u_intr_ready (
    .clk_i                  ( clk_i                          ),
    .rst_ni                 ( rst_ni                         ),
    .event_intr_i           ( event_intr_ready_i             ),
    .reg2hw_intr_enable_q_i ( reg2hw.intr_enable.mbx_ready.q ),
    .reg2hw_intr_test_q_i   ( reg2hw.intr_test.mbx_ready.q   ),
    .reg2hw_intr_test_qe_i  ( reg2hw.intr_test.mbx_ready.qe  ),
    .reg2hw_intr_state_q_i  ( reg2hw.intr_state.mbx_ready.q  ),
    .hw2reg_intr_state_de_o ( hw2reg.intr_state.mbx_ready.de ),
    .hw2reg_intr_state_d_o  ( hw2reg.intr_state.mbx_ready.d  ),
    .intr_o                 ( intr_ready_o                   )
  );

  prim_intr_hw #(.Width(1)) u_intr_abort (
    .clk_i                  ( clk_i                          ),
    .rst_ni                 ( rst_ni                         ),
    .event_intr_i           ( event_intr_abort_i             ),
    .reg2hw_intr_enable_q_i ( reg2hw.intr_enable.mbx_abort.q ),
    .reg2hw_intr_test_q_i   ( reg2hw.intr_test.mbx_abort.q   ),
    .reg2hw_intr_test_qe_i  ( reg2hw.intr_test.mbx_abort.qe  ),
    .reg2hw_intr_state_q_i  ( reg2hw.intr_state.mbx_abort.q  ),
    .hw2reg_intr_state_de_o ( hw2reg.intr_state.mbx_abort.de ),
    .hw2reg_intr_state_d_o  ( hw2reg.intr_state.mbx_abort.d  ),
    .intr_o                 ( intr_abort_o                   )
  );

  prim_intr_hw #(.Width(1)) u_intr_error (
    .clk_i                  ( clk_i                          ),
    .rst_ni                 ( rst_ni                         ),
    .event_intr_i           ( event_intr_error_i             ),
    .reg2hw_intr_enable_q_i ( reg2hw.intr_enable.mbx_error.q ),
    .reg2hw_intr_test_q_i   ( reg2hw.intr_test.mbx_error.q   ),
    .reg2hw_intr_test_qe_i  ( reg2hw.intr_test.mbx_error.qe  ),
    .reg2hw_intr_state_q_i  ( reg2hw.intr_state.mbx_error.q  ),
    .hw2reg_intr_state_de_o ( hw2reg.intr_state.mbx_error.de ),
    .hw2reg_intr_state_d_o  ( hw2reg.intr_state.mbx_error.d  ),
    .intr_o                 ( intr_error_o                   )
  );

  // Control Register
  logic abort_d, abort_q;

  // Abort computation from system and host interface
  always_comb begin
    abort_d = abort_q;

    if (sysif_control_abort_set_i) begin
      abort_d = 1'b1;
    end else if (hostif_control_abort_clear_o) begin
      abort_d = 1'b0;
    end
  end

  prim_flop #(
    .Width(1)
  ) u_abort (
    .clk_i ( clk_i   ),
    .rst_ni( rst_ni  ),
    .d_i   ( abort_d ),
    .q_o   ( abort_q )
  );

  // Writing a 1 to control.abort means clearing the abort condition
  assign hostif_control_abort_clear_o = reg2hw.control.abort.qe & reg2hw.control.abort.q;
  assign hw2reg.control.abort.d       = abort_q;

  assign hostif_control_error_set_o = reg2hw.control.error.qe & reg2hw.control.error.q;
  assign hw2reg.control.error.d     = hostif_control_error_i;

  assign hostif_control_async_msg_set_o = reg2hw.control.sys_async_msg.qe &
                                          reg2hw.control.sys_async_msg.q;
  assign hostif_control_async_msg_clear_o = reg2hw.control.sys_async_msg.qe &
                                            ~reg2hw.control.sys_async_msg.q;

  // Status Register
  // It is implemented as hwext and implemented in a different hierarchy and only providing an
  // alias. Thus manually assigning the external signals

  // External read logic
  assign hw2reg.status.busy.d             = hostif_status_busy_i;
  assign hw2reg.status.sys_intr_state.d   = hostif_status_sys_intr_state_i;
  assign hw2reg.status.sys_intr_enable.d  = hostif_status_sys_intr_en_i;
  assign hw2reg.status.sys_async_enable.d = hostif_status_sys_async_en_i;

  // Address config valid
  assign hostif_address_range_valid_write_o = reg2hw.address_range_valid.qe;
  assign hostif_address_range_valid_o       = reg2hw.address_range_valid.q;

  // Inbound Mailbox Base/Limit Register
  assign  hostif_imbx_base_o  = { reg2hw.inbound_base_address.q, {2{1'b0}} };
  assign  hostif_imbx_limit_o = { reg2hw.inbound_limit_address.q, {2{1'b0}} };

  // Outbound Mailbox Base/Limit Register
  assign  hostif_ombx_base_o  = { reg2hw.outbound_base_address.q, {2{1'b0}} };
  assign  hostif_ombx_limit_o = { reg2hw.outbound_limit_address.q, {2{1'b0}} };

  // Read/Write pointers
  assign  hw2reg.inbound_write_ptr.d = hostif_imbx_write_ptr_i[CfgSramAddrWidth-1:2];
  assign  hw2reg.outbound_read_ptr.d = hostif_ombx_read_ptr_i[CfgSramAddrWidth-1:2];

  // Outbound object size Register
  // External read logic
  assign  hw2reg.outbound_object_size.d   = hostif_ombx_object_size_i;
  assign  hw2reg.outbound_object_size.de  = hostif_ombx_object_size_update_i;
  // External write logic
  assign  hostif_ombx_object_size_write_o = reg2hw.outbound_object_size.qe;
  assign  hostif_ombx_object_size_o       = reg2hw.outbound_object_size.q;

  // Alias of the IRQ addr and data register from the sys interface (RO)
  assign hw2reg.doe_intr_msg_addr.d  = sysif_intr_msg_addr_i;
  assign hw2reg.doe_intr_msg_data.d  = sysif_intr_msg_data_i;

  // Assertions
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A,
                                                 u_regs,
                                                 alert_tx_o[0])
endmodule
