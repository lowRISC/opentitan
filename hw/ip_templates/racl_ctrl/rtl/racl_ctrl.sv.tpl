// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module ${module_instance_name} import ${module_instance_name}_reg_pkg::*; #(
  parameter logic [NumAlerts-1:0] AlertAsyncOn              = {NumAlerts{1'b1}},
  parameter int unsigned          NumSubscribingIps         = 1,
  parameter int unsigned          NumExternalSubscribingIps = 1,
  parameter bit                   RaclErrorRsp              = 1'b1
) (
  input  logic                                                         clk_i,
  input  logic                                                         rst_ni,
% if enable_shadow_reg:
  input logic                                                          rst_shadowed_ni,
% endif
  // Bus Interface (device)
  input  tlul_pkg::tl_h2d_t                                            tl_i,
  output tlul_pkg::tl_d2h_t                                            tl_o,
  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0]                    alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0]                    alert_tx_o,
  // Output policy vector for distribution
  output top_racl_pkg::racl_policy_vec_t                               racl_policies_o,
  // RACL violation information.
  input top_racl_pkg::racl_error_log_t [NumSubscribingIps-1:0]         racl_error_i,
  // External RACL violation information (from top-level)
  input top_racl_pkg::racl_error_log_t [NumExternalSubscribingIps-1:0] racl_error_external_i
);
  import top_racl_pkg::*;

  ${module_instance_name}_reg2hw_t reg2hw;
  ${module_instance_name}_hw2reg_t hw2reg;

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Register Interface
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic reg_intg_error;
% if enable_shadow_reg:
  logic shadowed_storage_err, shadowed_update_err;
% endif
  racl_error_log_t racl_ctrl_racl_error;

  // SEC_CM: BUS.INTEGRITY
% if enable_shadow_reg:
  // SEC_CM: RACL_POLICY.CONFIG.SHADOW
% endif
  ${module_instance_name}_reg_top #(
    .EnableRacl   ( 1'b1         ),
    .RaclErrorRsp ( RaclErrorRsp )
  ) u_racl_ctrl_reg (
    .clk_i                  ( clk_i                    ),
    .rst_ni                 ( rst_ni                   ),
% if enable_shadow_reg:
    .rst_shadowed_ni        ( rst_shadowed_ni          ),
% endif
    .tl_i                   ( tl_i                     ),
    .tl_o                   ( tl_o                     ),
    .reg2hw                 ( reg2hw                   ),
    .hw2reg                 ( hw2reg                   ),
% if enable_shadow_reg:
    .shadowed_storage_err_o ( shadowed_storage_err     ),
    .shadowed_update_err_o  ( shadowed_update_err      ),
% endif
    .racl_error_o           ( racl_ctrl_racl_error     ),
    .intg_err_o             ( reg_intg_error           )
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
  racl_policy_t policy_${policy['name'].lower()};
% endfor

  // Assign register policy values to policy structs
% for policy in policies:
  assign policy_${policy['name'].lower()}.read_perm = reg2hw.policy_${policy['name'].lower()}${"_shadowed" if enable_shadow_reg else ""}.read_perm.q;
  assign policy_${policy['name'].lower()}.write_perm = reg2hw.policy_${policy['name'].lower()}${"_shadowed" if enable_shadow_reg else ""}.write_perm.q;

% endfor
  // Broadcast all policies via policy vector
  assign racl_policies_o = {
% for policy in list(reversed(policies)):
    policy_${policy['name'].lower()}${',' if not loop.last else ''}
% endfor
  };

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Error handling
  //////////////////////////////////////////////////////////////////////////////////////////////////

  // The total number of RACL error sources
  localparam int unsigned NumAllIps = NumSubscribingIps + NumExternalSubscribingIps + 1;

  // Concatenate the two incoming RACL error vectors for common handling
  racl_error_log_t combined_racl_error[NumAllIps];

  // Combine the internal and external RACL log to a single valid vector (for assertion) and a
  // combined error vector for common handling in the logging logic.
  always_comb begin
    for (int unsigned i = 0; i < NumSubscribingIps; i++) begin
      combined_racl_error[i] = racl_error_i[i];
    end

    for (int unsigned i = NumSubscribingIps;
         i < NumSubscribingIps + NumExternalSubscribingIps; i++) begin
      combined_racl_error[i] = racl_error_external_i[i - NumSubscribingIps];
    end

    // Last element is the internal RACL error of the own reg_top
    combined_racl_error[NumAllIps-1] = racl_ctrl_racl_error;
  end

  // Arbitrate between all simultaneously valid error log requests.
  racl_error_log_t racl_error_arb;
  prim_racl_error_arb #(
    .N ( NumAllIps )
  ) u_prim_err_arb (
    .clk_i,
    .rst_ni,
    .error_log_i ( combined_racl_error ),
    .error_log_o ( racl_error_arb      )
  );

  // On the first error, we log the address and other information
  logic first_error;
  assign first_error = ~reg2hw.error_log.valid.q & racl_error_arb.valid;

  // Writing 1 to the error valid bit clears the log again
  logic clear_log;
  assign clear_log = reg2hw.error_log.valid.q & reg2hw.error_log.valid.qe;

  assign hw2reg.error_log.valid.d  = ~clear_log;
  assign hw2reg.error_log.valid.de = racl_error_arb.valid | clear_log;

  // Overflow is raised when error is valid and a new error is coming in or more than one
  // error is coming in at the same time
  assign hw2reg.error_log.overflow.d  = ~clear_log;
  assign hw2reg.error_log.overflow.de = (reg2hw.error_log.valid.q & racl_error_arb.valid) |
                                        racl_error_arb.overflow                           |
                                        clear_log;

  assign hw2reg.error_log.read_access.d  = clear_log ? '0 : racl_error_arb.read_access;
  assign hw2reg.error_log.read_access.de = first_error | clear_log;

  assign hw2reg.error_log.role.d  = clear_log ? '0 : racl_error_arb.racl_role;
  assign hw2reg.error_log.role.de = first_error | clear_log;

  assign hw2reg.error_log.ctn_uid.d  = clear_log ? '0 : racl_error_arb.ctn_uid;
  assign hw2reg.error_log.ctn_uid.de = first_error | clear_log;

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Assertions
  //////////////////////////////////////////////////////////////////////////////////////////////////

  // All outputs should be known value after reset
  `ASSERT_KNOWN(AlertsKnown_A, alert_tx_o)

  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)

  `ASSERT_KNOWN(RaclErrorKnown_A, racl_policies_o)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_racl_ctrl_reg,
                                                 alert_tx_o[0])
endmodule
