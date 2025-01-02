// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module ${module_instance_name} import ${module_instance_name}_reg_pkg::*; #(
  parameter logic [NumAlerts-1:0] AlertAsyncOn      = {NumAlerts{1'b1}},
  parameter int unsigned          NumSubscribingIps = 1
) (
  input  logic                                                 clk_i,
  input  logic                                                 rst_ni,
% if enable_shadow_reg:
  input logic                                                  rst_shadowed_ni,
% endif
  // Bus Interface (device)
  input  tlul_pkg::tl_h2d_t                                    tl_i,
  output tlul_pkg::tl_d2h_t                                    tl_o,
  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0]            alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0]            alert_tx_o,
  // Output policy vector for distribution
  output top_racl_pkg::racl_policy_vec_t                       policies_o,
  // RACL violation information.
  input logic            [NumSubscribingIps-1:0]               racl_error_i,
  input top_racl_pkg::racl_error_log_t [NumSubscribingIps-1:0] racl_error_log_i
);
  ${module_instance_name}_reg2hw_t reg2hw;
  ${module_instance_name}_hw2reg_t hw2reg;

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Register Interface
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic reg_intg_error;
% if enable_shadow_reg:
  logic shadowed_storage_err, shadowed_update_err;
% endif

  // SEC_CM: BUS.INTEGRITY
% if enable_shadow_reg:
  // SEC_CM: RACL_POLICY.CONFIG.SHADOW
% endif
  ${module_instance_name}_reg_top u_racl_ctrl_reg (
    .clk_i                  ( clk_i                ),
    .rst_ni                 ( rst_ni               ),
% if enable_shadow_reg:
    .rst_shadowed_ni        ( rst_shadowed_ni      ),
% endif
    .tl_i                   ( tl_i                 ),
    .tl_o                   ( tl_o                 ),
    .reg2hw                 ( reg2hw               ),
    .hw2reg                 ( hw2reg               ),
% if enable_shadow_reg:
    .shadowed_storage_err_o ( shadowed_storage_err ),
    .shadowed_update_err_o  ( shadowed_update_err  ),
% endif
    .intg_err_o             ( reg_intg_error       )
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Alert Management
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic [NumAlerts-1:0] alert_test, alert;

% if enable_shadow_reg:
  localparam logic [NumAlerts-1:0] IsFatal = {1'b1, 1'b0};

  assign alert[0]  = shadowed_update_err;
  assign alert[1]  = reg_intg_error | shadowed_storage_err;

  assign alert_test = {
    reg2hw.alert_test.fatal_fault.q &
    reg2hw.alert_test.fatal_fault.qe,
    reg2hw.alert_test.recov_ctrl_update_err.q &
    reg2hw.alert_test.recov_ctrl_update_err.qe
  };
% else:
  localparam logic [NumAlerts-1:0] IsFatal = {1'b1};

  assign alert[0]  = reg_intg_error;

  assign alert_test = {
    reg2hw.alert_test.fatal_fault.q &
    reg2hw.alert_test.fatal_fault.qe
  };
% endif

  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn ( AlertAsyncOn[i] ),
      .IsFatal ( IsFatal[i]      )
    ) u_prim_alert_sender (
      .clk_i         ( clk_i         ),
      .rst_ni        ( rst_ni        ),
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alert[i]      ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Policy broadcasting
  //////////////////////////////////////////////////////////////////////////////////////////////////

% for policy in policies:
  top_racl_pkg::racl_policy_t policy_${policy['name'].lower()};
% endfor

  // Assign register policy values to policy structs
% for policy in policies:
  assign policy_${policy['name'].lower()}.read_perm = reg2hw.policy_${policy['name'].lower()}${"_shadowed" if enable_shadow_reg else ""}.read_perm.q;
  assign policy_${policy['name'].lower()}.write_perm = reg2hw.policy_${policy['name'].lower()}${"_shadowed" if enable_shadow_reg else ""}.write_perm.q;

% endfor
  // Broadcast all policies via policy vector
  assign policies_o = {
% for policy in policies:
    policy_${policy['name'].lower()}${',' if not loop.last else ''}
% endfor
  };

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Error handling
  //////////////////////////////////////////////////////////////////////////////////////////////////
  //////////////////////////////////////////////////////////////////////////////

  // A RACL error can only happen for one IP at a time in one RACL domain. Therefore, it is
  // safe to OR all RACL error bits together and no arbitration is needed. This is true also
  // for the corresponding RACL role or Write/Read information.
  logic racl_error;
  assign racl_error = |racl_error_i;

  top_racl_pkg::racl_role_t racl_error_role;
  top_racl_pkg::ctn_uid_t racl_error_ctn_uid;
  logic racl_error_write_read;

  // Reduce all incoming error vectors to a single role and write/read bit.
  // Only a single IP can have a RACL error at one time.
  always_comb begin
    racl_error_role       = '0;
    racl_error_ctn_uid    = '0;
    racl_error_write_read = 1'b0;
    for (int i = 0; i < NumSubscribingIps; i++) begin
      racl_error_role       |= racl_error_log_i[i].racl_role;
      racl_error_ctn_uid    |= racl_error_log_i[i].ctn_uid;
      racl_error_write_read |= racl_error_log_i[i].write_read;
    end
  end

  logic first_error;
  assign first_error = ~reg2hw.error_log.valid.q & racl_error;

  // Writing 1 to the error valid bit clears the log again
  logic clear_log;
  assign clear_log = reg2hw.error_log.valid.q & reg2hw.error_log.valid.qe;

  assign hw2reg.error_log.valid.d  = ~clear_log;
  assign hw2reg.error_log.valid.de = racl_error | clear_log;

  // Overflow is raised when error is valid and a new error is coming in
  assign hw2reg.error_log.overflow.d  = ~clear_log;
  assign hw2reg.error_log.overflow.de = (reg2hw.error_log.valid.q & racl_error) | clear_log;

  assign hw2reg.error_log.write_read.d  = clear_log ? '0 : racl_error_write_read;
  assign hw2reg.error_log.write_read.de = first_error | clear_log;

  assign hw2reg.error_log.role.d  = clear_log ? '0 : racl_error_role;
  assign hw2reg.error_log.role.de = first_error | clear_log;

  assign hw2reg.error_log.ctn_uid.d  = clear_log ? '0 : racl_error_ctn_uid;
  assign hw2reg.error_log.ctn_uid.de = first_error | clear_log;

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Assertions
  //////////////////////////////////////////////////////////////////////////////////////////////////

  // All outputs should be known value after reset
  `ASSERT_KNOWN(AlertsKnown_A, alert_tx_o)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_racl_ctrl_reg,
                                                 alert_tx_o[0])
endmodule
