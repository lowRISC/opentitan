// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module ${module_instance_name}
  import tlul_pkg::*;
  import ${module_instance_name}_reg_pkg::*;
#(
  parameter logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}}
) (
  input  logic                                      clk_i,
  input  logic                                      rst_ni,
  input  logic                                      rst_shadowed_ni,
  // Alerts
  input  prim_alert_pkg::alert_rx_t [NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [NumAlerts-1:0] alert_tx_o,
  // Access range check interrupts
  output logic                                      intr_deny_cnt_reached_o,
  // Inter module signals
  input prim_mubi_pkg::mubi8_t                      range_check_overwrite_i,
  // Incoming TLUL interface
  input  tlul_pkg::tl_h2d_t                         ctn_tl_h2d_i,
  output tlul_pkg::tl_d2h_t                         ctn_tl_d2h_o,
  // Filtered outgoing TLUL interface to the target if request is not squashed
  output tlul_pkg::tl_h2d_t                         ctn_filtered_tl_h2d_o,
  input  tlul_pkg::tl_d2h_t                         ctn_filtered_tl_d2h_i
);
  ${module_instance_name}_reg2hw_t reg2hw;
  ${module_instance_name}_hw2reg_t hw2reg;

  //////////////////////////////////////////////////////////////////////////////
  // Register Interface
  //////////////////////////////////////////////////////////////////////////////
  logic reg_intg_error, shadowed_storage_err, shadowed_update_err;
  // SEC_CM: BUS.INTEGRITY
  ${module_instance_name}_reg_top u_ac_range_check_reg (
    .clk_i                  ( clk_i                ),
    .rst_ni                 ( rst_ni               ),
    .rst_shadowed_ni        ( rst_shadowed_ni      ),
    .tl_i                   ( tl_i                 ),
    .tl_o                   ( tl_o                 ),
    .reg2hw                 ( reg2hw               ),
    .hw2reg                 ( hw2reg               ),
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
      .IsFatal(i)
    ) u_prim_alert_sender (
      .clk_i         ( clk_i         ),
      .rst_ni        ( rst_ni        ),
      .alert_test_i  ( alert_test[i] ),
      .alert_req_i   ( alerts[i]     ),
      .alert_ack_o   (               ),
      .alert_state_o (               ),
      .alert_rx_i    ( alert_rx_i[i] ),
      .alert_tx_o    ( alert_tx_o[i] )
    );
  end

  //////////////////////////////////////////////////////////////////////////////
  // Range Check Logic
  //////////////////////////////////////////////////////////////////////////////

  logic [NumRanges-1:0] addr_hit, deny_mask, read_mask, write_mask, execute_mask, log_enable_mask;

  // TODO(#25454): RACL checks get implemented once RACL is in
  for (int i = 0; i < NumRanges; i++) begin : gen_range_checks
    // Extend base, limit, and mask to 32-bit
    logic [31:0] base_ext, limit_ext;
    logic tor_hit;

    assign base_ext  = {reg2hw.range_base[i].q, 2'b00};
    assign limit_ext = {reg2hw.range_limit[i].q, 2'b00};

    assign tor_hit   = (ctn_tl_h2d_i.a_address >= base_ext) &
                       (ctn_tl_h2d_i.a_address < limit_ext);

    // Request hits an enabled range and comparison logic
    assign addr_hit[i] = prim_mubi_pkg::mubi4_test_true_loose(reg2hw.range_perm[i].enable.q) &
                         tor_hit;

    // Decode the multi-bit access fields for convinient access
    logic perm_read_access, perm_write_access, perm_execute_access;
    assign perm_read_access =
      prim_mubi_pkg::mubi4_test_true_strict(reg2hw.range_perm[i].read_access.q);
    assign perm_write_access =
      prim_mubi_pkg::mubi4_test_true_strict(reg2hw.range_perm[i].write_access.q);
    assign perm_execute_access =
      prim_mubi_pkg::mubi4_test_true_strict(reg2hw.range_perm[i].execute_access.q);

    // Access is denied if no read_, write_, or execute access is set in the permission mask
    // The permission masks need to be reversed to allow for the right priority order.
    // Range 0 has the highest priority and is the MSB in the mask.
    assign deny_mask[NumRanges - 1 - i] =
      addr_hit[i] & ~(perm_read_access | perm_write_access | perm_execute_access);

    // Determine the read, write, and execute mask. Store a hit in their index
    assign read_mask[NumRanges - 1 - i]    = addr_hit[i] & perm_read_access;
    assign write_mask[NumRanges - 1 - i]   = addr_hit[i] & perm_write_access;
    assign execute_mask[NumRanges - 1 - i] = addr_hit[i] & perm_execute_access;
  end

  // Fiddle out bits to determine if its an execute request or not
  assign no_exec_access, exec_access;
  assign no_exec_access = prim_mubi_pkg::mubi4_test_false_strict(ctn_tl_h2d_i.a_user.instr_type);
  assign exec_access    = prim_mubi_pkg::mubi4_test_true_strict(ctn_tl_h2d_i.a_user.instr_type);

  // Fiddle out what access we are performing
  logic read_access, write_access, execute_access;
  assign read_access = (ctn_tl_h2d_i.a_opcode == Get) & no_exec_access;
  assign write_access = ((ctn_tl_h2d_i.a_opcode == PutFullData) |
                         (ctn_tl_h2d_i.a_opcode == PutPartialData));
  assign execute_acess = (ctn_tl_h2d_i.a_opcode == Get) & exec_access;

  // Priority comparison. If the deny mask is larger than the read, write, or execute mask, there
  // was an address match with a higher priority for the range to be denied
  logic read_allowed, write_allowed, execute_allowed;
  assign read_allowed    = read_access   & (read_mask    > deny_mask);
  assign write_allowed   = write_access  & (write_mask   > deny_mask);
  assign execute_allowed = execute_acess & (execute_mask > deny_mask);

  // The access fails if nothing is allowed and no overwrite is present
  logic range_check_fail;
  assign range_check_fail =
    ctn_tl_h2d_i.a_valid & ~(|{read_allowed, write_allowed, execute_allowed,
                               prim_mubi_pkg::mubi8_test_true_strict(range_check_overwrite_i)});

  //////////////////////////////////////////////////////////////////////////////
  // TLUL Loopback for failing accesses
  //////////////////////////////////////////////////////////////////////////////

  tlul_request_loopback u_req_loopback (
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
  logic deny_cnt_incr, deny_cnt_clr;

  // Only increment the deny counter if logging is enabled
  assign deny_cnt_incr = reg2hw.log_config.log_enable.q & range_check_fail;
  // Determine if we are doing the first log. This one is special, since it also needs to log
  // diagnostics data
  assign log_first_deny = deny_cnt_incr & (deny_cnt == 0);

  // Clear log information when clearing the interrupt or when clearing the log manually via the
  // the log_clear bit.
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
  assign hw2reg.log_status.deny_count.de = 1'b1;
  assign hw2reg.log_status.deny_count.d  = deny_cnt;

  assign hw2reg.log_status.denied_read_access.de = log_first_deny | clear_log;
  assign hw2reg.log_status.denied_read_access.d  = log_first_deny ? read_access : 1'b0;

  assign hw2reg.log_status.denied_write_access.de = log_first_deny | clear_log;
  assign hw2reg.log_status.denied_write_access.d  = log_first_deny ? write_access : 1'b0;

  assign hw2reg.log_status.denied_execute_access.de = log_first_deny | clear_log;
  assign hw2reg.log_status.denied_execute_access.d  = log_first_deny ? execute_access : 1'b0;

  // Request is denied because no range was matching at all
  assign hw2reg.log_status.denied_no_match.de = log_first_deny | clear_log;
  assign hw2reg.log_status.denied_no_match.d = ~(|addr_hit);

  // TODO(#25454): RACL status gets implemented once RACL is in
  assign hw2reg.log_status.denied_racl_read.de = log_first_deny | clear_log;
  assign hw2reg.log_status.denied_racl_read.d  = '0;

  // TODO(#25454): RACL status gets implemented once RACL is in
  assign hw2reg.log_status.denied_racl_write.de = log_first_deny | clear_log;
  assign hw2reg.log_status.denied_racl_write.d  = '0;

  // TODO(#25454): RACL status gets implemented once RACL is in
  assign hw2reg.log_status.denied_source_role.de = log_first_deny | clear_log;
  assign hw2reg.log_status.denied_source_role.d  = '0;

  // TODO(#25456): Need to determine the index that caused the denial
  assign hw2reg.log_status.deny_range_index.de = log_first_deny | clear_log;
  assign hw2reg.log_status.deny_range_index.d  = log_first_deny ? 0 : 0;

  assign hw2reg.log_address.de = log_first_deny | clear_log;
  assign hw2reg.log_address.d  = log_first_deny ? ctn_tl_h2d_i.a_address : '0;

  //////////////////////////////////////////////////////////////////////////////
  // Interrupt Notification Logic
  //////////////////////////////////////////////////////////////////////////////

  logic deny_cnt_threshold_reached_d, deny_threshold_reached_event;

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
    .clk_i                  ( clk_i                        ),
    .rst_ni                 ( rst_ni                       ),
    .event_intr_i           ( deny_threshold_reached_event ),
    .reg2hw_intr_enable_q_i ( reg2hw.intr_enable.q         ),
    .reg2hw_intr_test_q_i   ( reg2hw.intr_test.q           ),
    .reg2hw_intr_test_qe_i  ( reg2hw.intr_test.qe          ),
    .reg2hw_intr_state_q_i  ( reg2hw.intr_state.q          ),
    .hw2reg_intr_state_de_o ( hw2reg.intr_state.de         ),
    .hw2reg_intr_state_d_o  ( hw2reg.intr_state.d          ),
    .intr_o                 ( intr_deny_cnt_reached_o      )
  );

  //////////////////////////////////////////////////////////////////////////////
  // Assertions
  //////////////////////////////////////////////////////////////////////////////

  // All outputs should be known value after reset
  `ASSERT_KNOWN(AlertsKnown_A, alert_tx_o)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_ac_range_check_reg,
                                                 alert_tx_o[0])

endmodule
