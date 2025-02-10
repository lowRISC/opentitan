// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module racl_ctrl import racl_ctrl_reg_pkg::*; #(
  parameter logic [NumAlerts-1:0] AlertAsyncOn              = {NumAlerts{1'b1}},
  parameter int unsigned          NumSubscribingIps         = 1,
  parameter int unsigned          NumExternalSubscribingIps = 1,
  parameter bit                   RaclErrorRsp              = 1'b1
) (
  input  logic                                                         clk_i,
  input  logic                                                         rst_ni,
  input logic                                                          rst_shadowed_ni,
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

  racl_ctrl_reg2hw_t reg2hw;
  racl_ctrl_hw2reg_t hw2reg;

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Register Interface
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic reg_intg_error;
  logic shadowed_storage_err, shadowed_update_err;
  racl_error_log_t racl_ctrl_racl_error;

  // SEC_CM: BUS.INTEGRITY
  // SEC_CM: RACL_POLICY.CONFIG.SHADOW
  racl_ctrl_reg_top #(
    .EnableRacl   ( 1'b1         ),
    .RaclErrorRsp ( RaclErrorRsp )
  ) u_racl_ctrl_reg (
    .clk_i                  ( clk_i                    ),
    .rst_ni                 ( rst_ni                   ),
    .rst_shadowed_ni        ( rst_shadowed_ni          ),
    .tl_i                   ( tl_i                     ),
    .tl_o                   ( tl_o                     ),
    .reg2hw                 ( reg2hw                   ),
    .hw2reg                 ( hw2reg                   ),
    .shadowed_storage_err_o ( shadowed_storage_err     ),
    .shadowed_update_err_o  ( shadowed_update_err      ),
    .racl_error_o           ( racl_ctrl_racl_error     ),
    .intg_err_o             ( reg_intg_error           )
  );

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Alert Management
  //////////////////////////////////////////////////////////////////////////////////////////////////
  logic [NumAlerts-1:0] alert_test, alert;

  localparam logic [NumAlerts-1:0] IsFatal = {1'b1, 1'b0};

  assign alert[0]  = shadowed_update_err;
  assign alert[1]  = reg_intg_error | shadowed_storage_err;

  assign alert_test = {
    reg2hw.alert_test.fatal_fault.q &
    reg2hw.alert_test.fatal_fault.qe,
    reg2hw.alert_test.recov_ctrl_update_err.q &
    reg2hw.alert_test.recov_ctrl_update_err.qe
  };

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

  racl_policy_t policy_all_rd_wr;
  racl_policy_t policy_rot_private;
  racl_policy_t policy_soc_rot;

  // Assign register policy values to policy structs
  assign policy_all_rd_wr.read_perm = reg2hw.policy_all_rd_wr_shadowed.read_perm.q;
  assign policy_all_rd_wr.write_perm = reg2hw.policy_all_rd_wr_shadowed.write_perm.q;

  assign policy_rot_private.read_perm = reg2hw.policy_rot_private_shadowed.read_perm.q;
  assign policy_rot_private.write_perm = reg2hw.policy_rot_private_shadowed.write_perm.q;

  assign policy_soc_rot.read_perm = reg2hw.policy_soc_rot_shadowed.read_perm.q;
  assign policy_soc_rot.write_perm = reg2hw.policy_soc_rot_shadowed.write_perm.q;

  // Broadcast all policies via policy vector
  assign racl_policies_o = {
    policy_soc_rot,
    policy_rot_private,
    policy_all_rd_wr
  };

  //////////////////////////////////////////////////////////////////////////////////////////////////
  // Error handling
  //////////////////////////////////////////////////////////////////////////////////////////////////

  // Concatenate the two incoming RACL error vectors for common handling
  logic [NumSubscribingIps+NumExternalSubscribingIps:0]            combined_racl_error_valid;
  racl_error_log_t [NumSubscribingIps+NumExternalSubscribingIps:0] combined_racl_error;

  // Combine the internal and external RACL log to a single valid vector (for assertion) and a
  // combined error vector for common handling in the logging logic.
  always_comb begin
    for (int unsigned i = 0; i < NumSubscribingIps; i++) begin
      combined_racl_error_valid[i] = racl_error_i[i].valid;
      combined_racl_error[i]       = racl_error_i[i];
    end

    for (int unsigned i = NumSubscribingIps;
         i < NumSubscribingIps + NumExternalSubscribingIps; i++) begin
      combined_racl_error_valid[i] = racl_error_external_i[i - NumSubscribingIps].valid;
      combined_racl_error[i]       = racl_error_external_i[i - NumSubscribingIps];
    end

    // Last element is the internal RACL error of the own reg_top
    combined_racl_error_valid[NumSubscribingIps+NumExternalSubscribingIps] =
      racl_ctrl_racl_error.valid;
    combined_racl_error      [NumSubscribingIps+NumExternalSubscribingIps] = racl_ctrl_racl_error;
  end

  // A RACL error can only happen for one IP at a time in one RACL domain. Therefore, it is
  // safe to OR all RACL error bits together and no arbitration is needed. This is true also
  // for the corresponding RACL role or Write/Read information.
  `ASSERT(OneHotRaclError_A, $onehot0(combined_racl_error_valid))

  // Reduce all incoming error vectors to a single role and write/read bit.
  // Only a single IP can have a RACL error at one time.
  racl_error_log_t racl_error_arb;
  assign racl_error_arb = |combined_racl_error;

  logic first_error;
  assign first_error = ~reg2hw.error_log.valid.q & racl_error;

  // Writing 1 to the error valid bit clears the log again
  logic clear_log;
  assign clear_log = reg2hw.error_log.valid.q & reg2hw.error_log.valid.qe;

  assign hw2reg.error_log.valid.d  = ~clear_log;
  assign hw2reg.error_log.valid.de = racl_error_arb.valid | clear_log;

  // Overflow is raised when error is valid and a new error is coming in
  assign hw2reg.error_log.overflow.d  = ~clear_log;
  assign hw2reg.error_log.overflow.de = (reg2hw.error_log.valid.q & racl_error_arb.valid) |
                                        clear_log;

  assign hw2reg.error_log.read_access.d  = clear_log ? '0 : racl_error_arb.read_access;
  assign hw2reg.error_log.read_access.de = first_error | clear_log;

  assign hw2reg.error_log.role.d  = clear_log ? '0 : racl_error_arb.role;
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
