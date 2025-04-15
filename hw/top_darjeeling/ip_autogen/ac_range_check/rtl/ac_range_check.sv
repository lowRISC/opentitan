// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module ac_range_check
  import tlul_pkg::*;
  import ac_range_check_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0]           AlertAsyncOn              = {NumAlerts{1'b1}},
  parameter bit                             RangeCheckErrorRsp        = 1'b1,
  parameter bit                             EnableRacl                = 1'b0,
  parameter bit                             RaclErrorRsp              = EnableRacl,
  parameter top_racl_pkg::racl_policy_sel_t RaclPolicySelVec[NumRegs] = '{NumRegs{0}}
) (
  input  logic                                      clk_i,
  input  logic                                      rst_ni,
  input  logic                                      rst_shadowed_ni,
  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,
  // RACL interface
  input  top_racl_pkg::racl_policy_vec_t            racl_policies_i,
  output top_racl_pkg::racl_error_log_t             racl_error_o,
  // Access range check interrupts
  output logic                                      intr_deny_cnt_reached_o,
  // Bus interface
  input  tlul_pkg::tl_h2d_t                         tl_i,
  output tlul_pkg::tl_d2h_t                         tl_o,
  // Inter module signals
  input prim_mubi_pkg::mubi8_t                      range_check_overwrite_i,
  // Incoming TLUL interface
  input  tlul_pkg::tl_h2d_t                         ctn_tl_h2d_i,
  output tlul_pkg::tl_d2h_t                         ctn_tl_d2h_o,
  // Filtered outgoing TLUL interface to the target if request is not squashed
  output tlul_pkg::tl_h2d_t                         ctn_filtered_tl_h2d_o,
  input  tlul_pkg::tl_d2h_t                         ctn_filtered_tl_d2h_i
);
  ac_range_check_reg2hw_t reg2hw;
  ac_range_check_hw2reg_t hw2reg;

  //////////////////////////////////////////////////////////////////////////////
  // Register Interface
  //////////////////////////////////////////////////////////////////////////////
  logic reg_intg_error, shadowed_storage_err, shadowed_update_err;
  // SEC_CM: BUS.INTEGRITY
  ac_range_check_reg_top #(
    .EnableRacl(EnableRacl),
    .RaclErrorRsp(RaclErrorRsp),
    .RaclPolicySelVec(RaclPolicySelVec)
  ) u_ac_range_check_reg (
    .clk_i                  ( clk_i                ),
    .rst_ni                 ( rst_ni               ),
    .rst_shadowed_ni        ( rst_shadowed_ni      ),
    .tl_i                   ( tl_i                 ),
    .tl_o                   ( tl_o                 ),
    .reg2hw                 ( reg2hw               ),
    .hw2reg                 ( hw2reg               ),
    .racl_policies_i        ( racl_policies_i      ),
    .racl_error_o           ( racl_error_o         ),
    .shadowed_storage_err_o ( shadowed_storage_err ),
    .shadowed_update_err_o  ( shadowed_update_err  ),
    .intg_err_o             ( reg_intg_error       )
  );

  //////////////////////////////////////////////////////////////////////////////
  // Alerts
  //////////////////////////////////////////////////////////////////////////////
  logic [NumAlerts-1:0] alert_test, alert;
  logic deny_cnt_error;

  assign alert[0]  = shadowed_update_err;
  assign alert[1]  = reg_intg_error | shadowed_storage_err | deny_cnt_error;

  assign alert_test = {
    reg2hw.alert_test.fatal_fault.q &
    reg2hw.alert_test.fatal_fault.qe,
    reg2hw.alert_test.recov_ctrl_update_err.q &
    reg2hw.alert_test.recov_ctrl_update_err.qe
  };

  localparam logic [NumAlerts-1:0] IsFatal = {1'b1, 1'b0};
  for (genvar i = 0; i < NumAlerts; i++) begin : gen_alert_tx
    prim_alert_sender #(
      .AsyncOn(AlertAsyncOn[i]),
      .IsFatal(IsFatal[i])
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

  assign hw2reg.alert_status.shadowed_storage_err.d = 1'b1;
  assign hw2reg.alert_status.shadowed_storage_err.de = shadowed_storage_err;
  assign hw2reg.alert_status.shadowed_update_err.d = 1'b1;
  assign hw2reg.alert_status.shadowed_update_err.de = shadowed_update_err;
  assign hw2reg.alert_status.reg_intg_err.d = 1'b1;
  assign hw2reg.alert_status.reg_intg_err.de = reg_intg_error;
  assign hw2reg.alert_status.counter_err.d = 1'b1;
  assign hw2reg.alert_status.counter_err.de = deny_cnt_error;

  //////////////////////////////////////////////////////////////////////////////
  // Range Check Logic
  //////////////////////////////////////////////////////////////////////////////

  logic [NumRanges-1:0] addr_hit;
  logic [NumRanges-1:0] r_deny_mask, w_deny_mask, x_deny_mask, deny_mask;
  logic [NumRanges-1:0] r_grant_mask, w_grant_mask, x_grant_mask, grant_mask;
  logic [NumRanges-1:0] log_enable_mask;
  logic [NumRanges-1:0] racl_read_hit, racl_write_hit;

  // Retrieve RACL role from user bits and one-hot encode that for the comparison bitmap
  top_racl_pkg::racl_role_vec_t racl_role_vec;
  top_racl_pkg::racl_role_t racl_role;
  assign racl_role = top_racl_pkg::tlul_extract_racl_role_bits(ctn_tl_h2d_i.a_user.rsvd);

  prim_onehot_enc #(
    .OneHotWidth( $bits(top_racl_pkg::racl_role_vec_t) )
  ) u_racl_role_encode (
    .in_i ( racl_role     ),
    .en_i ( 1'b1          ),
    .out_o( racl_role_vec )
  );

  // Figure out whether the access is an instruction fetch ("execute") or not. Note that the
  // following two signals are *not* complementary strictly speaking: if `instr_type` isn't a valid
  // MuBi value, neither of them will be true, hence the access will not be granted at all.
  logic no_exec_access, exec_access;
  assign no_exec_access = prim_mubi_pkg::mubi4_test_false_strict(
                            prim_mubi_pkg::mubi4_t'(ctn_tl_h2d_i.a_user.instr_type));
  assign exec_access    = prim_mubi_pkg::mubi4_test_true_strict(
                            prim_mubi_pkg::mubi4_t'(ctn_tl_h2d_i.a_user.instr_type));

  // Figure out whether the access is a read, write, or execute.
  logic read_access, write_access, execute_access;
  assign read_access    = (ctn_tl_h2d_i.a_opcode == Get) & no_exec_access;
  assign write_access   = (ctn_tl_h2d_i.a_opcode == PutFullData) |
                          (ctn_tl_h2d_i.a_opcode == PutPartialData);
  assign execute_access = (ctn_tl_h2d_i.a_opcode == Get) & exec_access;

  for (genvar i = 0; i < NumRanges; i++) begin : gen_range_checks
    // Extend base, limit, and mask to 32 bits
    logic [31:0] base_ext, limit_ext;
    logic tor_hit;

    assign base_ext  = {reg2hw.range_base[i].q, 2'b00};
    assign limit_ext = {reg2hw.range_limit[i].q, 2'b00};

    assign tor_hit   = (ctn_tl_h2d_i.a_address >= base_ext) &
                       (ctn_tl_h2d_i.a_address < limit_ext);

    // Request hits an enabled range and comparison logic
    assign addr_hit[i] = prim_mubi_pkg::mubi4_test_true_loose(
                           prim_mubi_pkg::mubi4_t'(reg2hw.range_attr[i].enable.q)) & tor_hit;

    // Perform RACL checks - check if the incoming role matches with the configured policy
    assign racl_read_hit [i] = |(racl_role_vec & reg2hw.range_racl_policy_shadowed[i].read_perm.q);
    assign racl_write_hit[i] = |(racl_role_vec & reg2hw.range_racl_policy_shadowed[i].write_perm.q);

    // Decode the multi-bit access fields for convenient access
    logic perm_read_access, perm_write_access, perm_execute_access;
    assign perm_read_access = prim_mubi_pkg::mubi4_test_true_strict(
                                prim_mubi_pkg::mubi4_t'(reg2hw.range_attr[i].read_access.q)) &
                                racl_read_hit[i];
    assign perm_write_access = prim_mubi_pkg::mubi4_test_true_strict(
                                 prim_mubi_pkg::mubi4_t'(reg2hw.range_attr[i].write_access.q)) &
                                 racl_write_hit[i];
    assign perm_execute_access = prim_mubi_pkg::mubi4_test_true_strict(
                                   prim_mubi_pkg::mubi4_t'(reg2hw.range_attr[i].execute_access.q)) &
                                   racl_read_hit[i];

    // A range grants a request if the request address hits and the type of the access (R/W/X) is
    // permitted by that range. In the grant masks and the deny masks (see below), the range with
    // index 0 is at the MSB, giving it the highest priority in the greater-than comparison to
    // decide between grant and denial.
    assign r_grant_mask[NumRanges-1-i] = addr_hit[i] & read_access & perm_read_access;
    assign w_grant_mask[NumRanges-1-i] = addr_hit[i] & write_access & perm_write_access;
    assign x_grant_mask[NumRanges-1-i] = addr_hit[i] & execute_access & perm_execute_access;

    // A range denies a request if the request address hits and the type of the access (R/W/X) is
    // *not* permitted by that range.
    assign r_deny_mask[NumRanges-1-i] = addr_hit[i] & read_access & ~perm_read_access;
    assign w_deny_mask[NumRanges-1-i] = addr_hit[i] & write_access & ~perm_write_access;
    assign x_deny_mask[NumRanges-1-i] = addr_hit[i] & execute_access & ~perm_execute_access;

    // Use log_enable_mask to mask logging. Note, this mask is not reversed as we use the index
    // that caused to the denial to read from that mask and don't use it as a comparison.
    assign log_enable_mask[i] = prim_mubi_pkg::mubi4_test_true_strict(
      prim_mubi_pkg::mubi4_t'(reg2hw.range_attr[i].log_denied_access.q));
  end

  // The overall grant and deny mask is simply the OR combination of the access-type-specific masks.
  assign grant_mask = r_grant_mask | w_grant_mask | x_grant_mask;
  assign deny_mask  = r_deny_mask  | w_deny_mask  | x_deny_mask;

  // Based on the deny mask, we compute the leading bit in the mask. The index of the leading
  // bit determines the index of the range that denied the request. As `prim_leading_one_ppc` starts
  // its search for the "leading" bit at the LSB, `deny_mask` needs to be reversed to compute the
  // index. The result is then directly the index of the SW-configured range, due to how
  // `grant_mask` and `deny_mask` get built (see above).
  logic [NumRanges-1:0] deny_mask_reversed;
  assign deny_mask_reversed = {<<{deny_mask}};

  localparam int unsigned NumRangesWidth = prim_util_pkg::vbits(NumRanges);
  logic [NumRangesWidth-1:0] deny_index;
  prim_leading_one_ppc #(
    .N ( NumRanges )
  ) u_leading_one (
    .in_i          ( deny_mask_reversed ),
    .leading_one_o (                    ),
    .ppc_out_o     (                    ),
    .idx_o         ( deny_index         )
  );

  // A request gets granted if and only if
  // (1) the request is valid and
  // (2.1) at least one range matches and among the matching ranges the one with the highest
  //       priority grants the request or
  // (2.2) range checks are bypassed.
  logic range_check_grant;
  assign range_check_grant = ctn_tl_h2d_i.a_valid & (
                               (|addr_hit & (grant_mask > deny_mask)) |
                               prim_mubi_pkg::mubi8_test_true_strict(range_check_overwrite_i)
                             );

  // A request gets denied if and only if it is valid and doesn't get granted.
  logic range_check_fail;
  assign range_check_fail = ctn_tl_h2d_i.a_valid & ~range_check_grant;

  //////////////////////////////////////////////////////////////////////////////
  // TLUL Loopback for failing accesses
  //////////////////////////////////////////////////////////////////////////////

  tlul_request_loopback #(
    .ErrorRsp( RangeCheckErrorRsp )
  ) u_req_loopback (
    .clk_i         ( clk_i                 ),
    .rst_ni        ( rst_ni                ),
    .squash_req_i  ( range_check_fail      ),
    // Incoming request
    .tl_h2d_i      ( ctn_tl_h2d_i          ),
    .tl_d2h_o      ( ctn_tl_d2h_o          ),
    // Outgoing request/rsp if not squashed
    .tl_h2d_o      ( ctn_filtered_tl_h2d_o ),
    .tl_d2h_i      ( ctn_filtered_tl_d2h_i )
  );

  //////////////////////////////////////////////////////////////////////////////
  // Range Check Deny Counting Logic
  //////////////////////////////////////////////////////////////////////////////

  logic [DenyCountWidth-1:0] deny_cnt;
  logic deny_cnt_incr;

  // Only increment the deny counter if logging is globally enabled and for the particular range
  assign deny_cnt_incr = reg2hw.log_config.log_enable.q &
                         log_enable_mask[deny_index]    &
                         range_check_fail;
  // Determine if we are doing the first log. This one is special, since it also needs to log
  // diagnostics data
  logic log_first_deny;
  assign log_first_deny = deny_cnt_incr & (deny_cnt == 0);

  // Clear log information when clearing the interrupt or when clearing the log manually via the
  // writing of a 1 to the log_clear bit.
  logic intr_state_cleared, clear_log;
  assign clear_log = intr_state_cleared |
                     (reg2hw.log_config.log_clear.qe & reg2hw.log_config.log_clear.q);

  prim_count #(
    .Width(DenyCountWidth)
  ) u_deny_count (
    .clk_i              ( clk_i              ),
    .rst_ni             ( rst_ni             ),
    .clr_i              ( clear_log          ),
    .set_i              ( 1'b0               ),
    .set_cnt_i          ( '0                 ),
    .incr_en_i          ( deny_cnt_incr      ),
    .decr_en_i          ( 1'b0               ),
    .step_i             ( DenyCountWidth'(1) ),
    .commit_i           ( 1'b1               ),
    .cnt_o              ( deny_cnt           ),
    .cnt_after_commit_o (                    ),
    .err_o              ( deny_cnt_error     )
  );

  // Log count is transparently mirrored. Clearing happens on the counter.
  assign hw2reg.log_status.deny_cnt.de = 1'b1;
  assign hw2reg.log_status.deny_cnt.d  = deny_cnt;

  assign hw2reg.log_status.denied_read_access.de = log_first_deny | clear_log;
  assign hw2reg.log_status.denied_read_access.d  = log_first_deny ? read_access : 1'b0;

  assign hw2reg.log_status.denied_write_access.de = log_first_deny | clear_log;
  assign hw2reg.log_status.denied_write_access.d  = log_first_deny ? write_access : 1'b0;

  assign hw2reg.log_status.denied_execute_access.de = log_first_deny | clear_log;
  assign hw2reg.log_status.denied_execute_access.d  = log_first_deny ? execute_access : 1'b0;

  // Request is denied because no range was matching at all
  assign hw2reg.log_status.denied_no_match.de = log_first_deny | clear_log;
  assign hw2reg.log_status.denied_no_match.d = log_first_deny ? ~(|addr_hit) : 1'b0;

  // Log if denied range lacks a valid READ RACL hit
  assign hw2reg.log_status.denied_racl_read.de = log_first_deny | clear_log;
  assign hw2reg.log_status.denied_racl_read.d  =
    log_first_deny ? ((read_access | execute_access) & ~racl_read_hit[deny_index]) : '0;

  // Log if denied range lacks a valid WRITE RACL hit
  assign hw2reg.log_status.denied_racl_write.de = log_first_deny | clear_log;
  assign hw2reg.log_status.denied_racl_write.d  =
    log_first_deny ? (write_access & ~racl_write_hit[deny_index]) : '0;

  assign hw2reg.log_status.denied_source_role.de = log_first_deny | clear_log;
  assign hw2reg.log_status.denied_source_role.d  = log_first_deny ? racl_role : '0;

  assign hw2reg.log_status.denied_ctn_uid.de = log_first_deny | clear_log;
  assign hw2reg.log_status.denied_ctn_uid.d  =
      log_first_deny ? top_racl_pkg::tlul_extract_ctn_uid_bits(ctn_tl_h2d_i.a_user.rsvd)
                     : '0;

  assign hw2reg.log_status.deny_range_index.de = log_first_deny | clear_log;
  assign hw2reg.log_status.deny_range_index.d  = log_first_deny ? deny_index : 0;

  assign hw2reg.log_address.de = log_first_deny | clear_log;
  assign hw2reg.log_address.d  = log_first_deny ? ctn_tl_h2d_i.a_address : '0;

  //////////////////////////////////////////////////////////////////////////////
  // Interrupt Notification Logic
  //////////////////////////////////////////////////////////////////////////////

  logic deny_cnt_threshold_reached_d, deny_cnt_threshold_reached_event;

  // Create a threshold event when the deny counter reaches the configured threshold
  assign deny_cnt_threshold_reached_d = deny_cnt > reg2hw.log_config.deny_cnt_threshold.q;
  prim_edge_detector u_edge_threshold_reached (
    .clk_i             ( clk_i                            ),
    .rst_ni            ( rst_ni                           ),
    .d_i               ( deny_cnt_threshold_reached_d     ),
    .q_sync_o          (                                  ),
    .q_posedge_pulse_o ( deny_cnt_threshold_reached_event ),
    .q_negedge_pulse_o (                                  )
  );

  prim_edge_detector u_edge_intr_state (
    .clk_i             ( clk_i               ),
    .rst_ni            ( rst_ni              ),
    .d_i               ( reg2hw.intr_state.q ),
    .q_sync_o          (                     ),
    .q_posedge_pulse_o (                     ),
    .q_negedge_pulse_o ( intr_state_cleared  )
  );

  prim_intr_hw #(
    .Width(1)
  ) u_intr_range_check_deny (
    .clk_i                  ( clk_i                            ),
    .rst_ni                 ( rst_ni                           ),
    .event_intr_i           ( deny_cnt_threshold_reached_event ),
    .reg2hw_intr_enable_q_i ( reg2hw.intr_enable.q             ),
    .reg2hw_intr_test_q_i   ( reg2hw.intr_test.q               ),
    .reg2hw_intr_test_qe_i  ( reg2hw.intr_test.qe              ),
    .reg2hw_intr_state_q_i  ( reg2hw.intr_state.q              ),
    .hw2reg_intr_state_de_o ( hw2reg.intr_state.de             ),
    .hw2reg_intr_state_d_o  ( hw2reg.intr_state.d              ),
    .intr_o                 ( intr_deny_cnt_reached_o          )
  );

  //////////////////////////////////////////////////////////////////////////////
  // Unused Signals
  //////////////////////////////////////////////////////////////////////////////
  logic unused_signals;
  assign unused_signals = ^log_enable_mask;

  //////////////////////////////////////////////////////////////////////////////
  // Assertions
  //////////////////////////////////////////////////////////////////////////////

  // All outputs should have known values after reset
  `ASSERT_KNOWN(AlertsKnown_A, alert_tx_o)
  `ASSERT_KNOWN(DenyCntIrqKnown_A, intr_deny_cnt_reached_o)

  `ASSERT_KNOWN_IF(TlODKnown_A, tl_o, tl_o.d_valid)
  `ASSERT_KNOWN(TlOAReadyKnown_A, tl_o.a_ready)

  `ASSERT_KNOWN_IF(TlCtnODKnown_A, ctn_tl_d2h_o, ctn_tl_d2h_o.d_valid)
  `ASSERT_KNOWN(TlCtnOAReadyKnown_A, ctn_tl_d2h_o.a_ready)
  `ASSERT_KNOWN_IF(TlCtnFilteredOAKnown_A, ctn_filtered_tl_h2d_o, ctn_filtered_tl_h2d_o.a_valid)
  `ASSERT_KNOWN(TlCtnFilteredODReadyKnown_A, ctn_filtered_tl_h2d_o.d_ready)

  `ASSERT_KNOWN_IF(RaclErrorOKnown_A, racl_error_o, racl_error_o.valid)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_ac_range_check_reg,
                                                 alert_tx_o[0])
  // Deny Counter error
  `ASSERT_PRIM_COUNT_ERROR_TRIGGER_ALERT(DenyCountCheck_A, u_deny_count,
                                         alert_tx_o[1])

endmodule
