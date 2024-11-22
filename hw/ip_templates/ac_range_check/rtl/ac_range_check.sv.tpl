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

  assign alert[0]  = shadowed_update_err;
  assign alert[1]  = reg_intg_error | shadowed_storage_err;

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

  logic [NumRanges-1:0] deny_mask, read_mask, write_mask, execute_mask, log_enable_mask;

  // TODO(#25454): RACL checks get implemented once RACL is in
  for (int i = 0; i < NumRanges; i++) begin : gen_range_checks
    // Extend base, limit, and mask to 32-bit
    logic [31:0] base_ext, limit_ext;
    logic addr_hit, tor_hit;

    assign base_ext  = {reg2hw.range_base[i].q, 2'b00};
    assign limit_ext = {reg2hw.range_limit[i].q, 2'b00};

    assign tor_hit   = (ctn_tl_h2d_i.a_address >= base_ext) &
                       (ctn_tl_h2d_i.a_address < limit_ext);

    // Request hits an enabled range and comparison logic
    assign addr_hit = prim_mubi_pkg::mubi4_test_true_loose(reg2hw.range_perm[i].enable.q) &
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
      addr_hit & ~(perm_read_access | perm_write_access | perm_execute_access);

    // Determine the read, write, and execute mask. Store a hit in their index
    assign read_mask[NumRanges - 1 - i]    = addr_hit & perm_read_access;
    assign write_mask[NumRanges - 1 - i]   = addr_hit & perm_write_access;
    assign execute_mask[NumRanges - 1 - i] = addr_hit & perm_execute_access;
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
  // Assertions
  //////////////////////////////////////////////////////////////////////////////

  // All outputs should be known value after reset
  `ASSERT_KNOWN(AlertsKnown_A, alert_tx_o)

  // Alert assertions for reg_we onehot check
  `ASSERT_PRIM_REG_WE_ONEHOT_ERROR_TRIGGER_ALERT(RegWeOnehotCheck_A, u_ac_range_check_reg,
                                                 alert_tx_o[0])

endmodule
