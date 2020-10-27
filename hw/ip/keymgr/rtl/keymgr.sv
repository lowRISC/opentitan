// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Key manager top level
//

`include "prim_assert.sv"

module keymgr import keymgr_pkg::*; #(
  parameter logic AlertAsyncOn = 1'b1
) (
  input clk_i,
  input rst_ni,

  // Bus Interface
  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  // key interface to crypto modules
  output hw_key_req_t aes_key_o,
  output hw_key_req_t hmac_key_o,
  output hw_key_req_t kmac_key_o,

  // data interface to/from crypto modules
  output kmac_data_req_t kmac_data_o,
  input kmac_data_rsp_t kmac_data_i,

  // the following signals should eventually be wrapped into structs from other modules
  input lc_data_t lc_i,
  input otp_data_t otp_i,
  input flash_ctrl_pkg::keymgr_flash_t flash_i,

  // interrupts and alerts
  output logic intr_op_done_o,
  output logic intr_err_o,
  input  prim_alert_pkg::alert_rx_t [keymgr_reg_pkg::NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [keymgr_reg_pkg::NumAlerts-1:0] alert_tx_o
);

  import keymgr_reg_pkg::*;

  `ASSERT_INIT(AdvDataWidth_A, AdvDataWidth <= KDFMaxWidth)
  `ASSERT_INIT(IdDataWidth_A,  IdDataWidth  <= KDFMaxWidth)
  `ASSERT_INIT(GenDataWidth_A, GenDataWidth <= KDFMaxWidth)
  `ASSERT_INIT(OutputKeyDiff_A, HardOutputKey != SoftOutputKey)

  // Register module
  keymgr_reg2hw_t reg2hw;
  keymgr_hw2reg_t hw2reg;

  keymgr_reg_top u_reg (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o,
    .reg2hw,
    .hw2reg,
    .devmode_i  (1'b1) // connect to real devmode signal in the future
  );


  /////////////////////////////////////
  //  LFSR
  /////////////////////////////////////

  // A farily large lfsr is used here as entropy in multiple places.
  // - populate the default working state
  // - generate random inputs when a bad input is selected
  //
  // The first case is sensitive, and thus the working state is constructed
  // through multiple rounds of the Lfsr
  // The second case is less sensitive and is applied directly.  If the inputs
  // have more bits than the lfsr output, the lfsr value is simply replicated

  logic [63:0] lfsr;
  logic lfsr_en;

  prim_lfsr #(
    .LfsrDw(64),
    .StateOutDw(64)
  ) u_lfsr (
    .clk_i,
    .rst_ni,
    .lfsr_en_i(lfsr_en),
    .seed_en_i(1'b0),
    .seed_i('0),
    .entropy_i('0), // TBD, this should be hooked up to an entropy distribution pkg
    .state_o(lfsr)
  );

  /////////////////////////////////////
  //  Key Manager Control
  /////////////////////////////////////

  keymgr_stage_e stage_sel;
  keymgr_gen_out_e key_sel;
  logic adv_en, id_en, gen_en;
  logic load_key;
  logic [Shares-1:0][KeyWidth-1:0] kmac_key;
  logic op_done;
  logic init_done;
  logic data_valid;
  logic kmac_done;
  logic kmac_input_invalid;
  logic kmac_cmd_err;
  logic kmac_fsm_err;
  logic [Shares-1:0][KeyWidth-1:0] kmac_data;
  logic [ErrLastPos-1:0] err_code;

  keymgr_ctrl u_ctrl (
    .clk_i,
    .rst_ni,
    .keymgr_en_i(lc_i.keymgr_en),
    .prng_en_o(lfsr_en),
    .entropy_i(lfsr[63:32]),  // TBD, recommend directly interfacing with DRBG for keymgr_ctrl
    .init_i(reg2hw.control.init.q),
    .init_done_o(init_done),
    .op_i(keymgr_ops_e'(reg2hw.control.operation.q)),
    .op_start_i(reg2hw.control.start.q),
    .op_done_o(op_done),
    .status_o(hw2reg.op_status.d),
    .error_o(err_code),
    .data_valid_o(data_valid),
    .working_state_o(hw2reg.working_state.d),
    .root_key_i(otp_i.root_key),
    .hw_sel_o(key_sel),
    .stage_sel_o(stage_sel),
    .load_key_o(load_key),
    .adv_en_o(adv_en),
    .id_en_o(id_en),
    .gen_en_o(gen_en),
    .key_o(kmac_key),
    .kmac_done_i(kmac_done),
    .kmac_input_invalid_i(kmac_input_invalid),
    .kmac_fsm_err_i(kmac_fsm_err),
    .kmac_cmd_err_i(kmac_cmd_err),
    .kmac_data_i(kmac_data)
  );

  assign hw2reg.control.start.d  = '0;
  assign hw2reg.control.start.de = op_done;
  assign hw2reg.control.init.d  = '0;
  assign hw2reg.control.init.de = init_done;
  // as long as operation is ongoing, capture status
  assign hw2reg.op_status.de = reg2hw.control.start.q;

  // working state is always visible
  assign hw2reg.working_state.de = 1'b1;

  // key manager registers cannot be changed once an operation starts
  keymgr_cfg_en u_cfgen (
    .clk_i,
    .rst_ni,
    .keymgr_en_i(lc_i.keymgr_en),
    .set_i(op_done | init_done),
    .clr_i(reg2hw.control.start.q | reg2hw.control.init.q),
    .out_o(hw2reg.cfgen.d)
  );

  /////////////////////////////////////
  //  Key Manager Input Construction
  /////////////////////////////////////

  // The various arrays of inputs for each operation
  logic [2**StageWidth-1:0][AdvDataWidth-1:0] adv_matrix;
  logic [2**StageWidth-1:0][IdDataWidth-1:0] id_matrix;
  logic [GenDataWidth-1:0] gen_in;

  // The max key version for each stage
  logic [2**StageWidth-1:0][31:0] max_key_versions;

  // Number of times the lfsr output fits into the inputs
  localparam int AdvLfsrCopies = AdvDataWidth / 32;
  localparam int IdLfsrCopies = IdDataWidth / 32;
  localparam int GenLfsrCopies = GenDataWidth / 32;

  // input checking - currently only MAX version, others TBD
  logic key_version_good;

  // Advance state operation input construction
  for (genvar i = KeyMgrStages; i < 2**StageWidth; i++) begin : gen_adv_matrix_fill
    assign adv_matrix[i] = {AdvLfsrCopies{lfsr[31:0]}};
  end

  // Advance to creator_root_key
  logic [KeyWidth-1:0] creator_seed;
  assign creator_seed = flash_i.seeds[flash_ctrl_pkg::CreatorSeedIdx];
  assign adv_matrix[Creator] = AdvDataWidth'({reg2hw.rom_ext_desc,
                                              RevisionSecret,
                                              otp_i.devid,
                                              lc_i.health_state,
                                              creator_seed});

  // Advance to owner_intermediate_key
  logic [KeyWidth-1:0] owner_seed;
  assign owner_seed = flash_i.seeds[flash_ctrl_pkg::OwnerSeedIdx];
  assign adv_matrix[OwnerInt] = AdvDataWidth'({reg2hw.software_binding,owner_seed});

  // Advance to owner_key
  assign adv_matrix[Owner]   = AdvDataWidth'(reg2hw.software_binding);


  // Generate Identity operation input construction
  for (genvar i = KeyMgrStages; i < 2**StageWidth; i++) begin : gen_id_matrix_fill
    assign id_matrix[i] = {IdLfsrCopies{lfsr[31:0]}};
  end

  assign id_matrix[Creator]  = CreatorIdentityKey;
  assign id_matrix[OwnerInt] = OwnerIntIdentityKey;
  assign id_matrix[Owner]    = OwnerIdentityKey;


  // Generate output operation input construction
  logic [KeyWidth-1:0] output_key;

  assign output_key = (key_sel == HwKey) ? HardOutputKey : SoftOutputKey;
  assign gen_in = (stage_sel == Disable) ? {GenLfsrCopies{lfsr[31:0]}} : {reg2hw.key_version,
                                                                          reg2hw.salt,
                                                                          output_key};

  // Advance state operation input construction
  for (genvar i = KeyMgrStages; i < 2**StageWidth; i++) begin : gen_key_version_fill
    assign max_key_versions[i] = '0;
  end

  assign max_key_versions[Creator]  = reg2hw.max_creator_key_ver;
  assign max_key_versions[OwnerInt] = reg2hw.max_owner_int_key_ver;
  assign max_key_versions[Owner]    = reg2hw.max_owner_key_ver;


  // General module for checking inputs
  keymgr_input_checks u_checks (
    .max_key_versions_i(max_key_versions),
    .stage_sel_i(stage_sel),
    .key_version_i(reg2hw.key_version),
    .key_version_good_o(key_version_good)
  );


  /////////////////////////////////////
  //  KMAC Control
  /////////////////////////////////////

  logic key_version_err;
  logic [3:0] invalid_data;

  assign key_version_err = !key_version_good;

  assign invalid_data[OpAdvance]  = '0; // TBD
  assign invalid_data[OpGenId]    = '0; // TBD
  assign invalid_data[OpGenSwOut] = key_version_err; // TBD, more to come
  assign invalid_data[OpGenHwOut] = key_version_err; // TBD, more to come

  keymgr_kmac_if u_kmac_if (
    .clk_i,
    .rst_ni,
    .adv_data_i(adv_matrix[stage_sel]),
    .id_data_i(id_matrix[stage_sel]),
    .gen_data_i(gen_in),
    .inputs_invalid_i(invalid_data),
    .inputs_invalid_o(kmac_input_invalid),
    .adv_en_i(adv_en),
    .id_en_i(id_en),
    .gen_en_i(gen_en),
    .done_o(kmac_done),
    .data_o(kmac_data),
    .kmac_data_o,
    .kmac_data_i,
    .entropy_i(lfsr[31:0]),
    .fsm_error_o(kmac_fsm_err),
    .cmd_error_o(kmac_cmd_err)
  );


  /////////////////////////////////////
  //  Side load key storage
  /////////////////////////////////////
  keymgr_key_dest_e dest_sel;
  logic aes_sel, hmac_sel, kmac_sel;

  assign dest_sel = keymgr_key_dest_e'(reg2hw.control.dest_sel);
  assign aes_sel  = dest_sel == Aes  & key_sel == HwKey;
  assign hmac_sel = dest_sel == Hmac & key_sel == HwKey;
  assign kmac_sel = dest_sel == Kmac & key_sel == HwKey;

  keymgr_sideload_key u_aes_key (
    .clk_i,
    .rst_ni,
    .keymgr_en_i(lc_i.keymgr_en),
    .set_i(data_valid & aes_sel),
    .clr_i(lc_i.keymgr_en), // TBD, should add an option for software clear later
    .entropy_i(lfsr[31:0]), //TBD, recommend directly interfacign with DRBG entropy for keys
    .key_i(kmac_data),
    .key_o(aes_key_o)
  );

  keymgr_sideload_key u_hmac_key (
    .clk_i,
    .rst_ni,
    .keymgr_en_i(lc_i.keymgr_en),
    .set_i(data_valid & hmac_sel),
    .clr_i(lc_i.keymgr_en), // TBD, should add an option for software clear later
    .entropy_i(lfsr[31:0]),
    .key_i(kmac_data),
    .key_o(hmac_key_o)
  );

  keymgr_sideload_key u_kmac_key (
    .clk_i,
    .rst_ni,
    .keymgr_en_i(lc_i.keymgr_en),
    .set_i(load_key | (data_valid & kmac_sel)),
    .clr_i(~lc_i.keymgr_en), // TBD, should add an option for software clear later
    .entropy_i(lfsr[31:0]),
    .key_i(load_key ? kmac_key : kmac_data),
    .key_o(kmac_key_o)
  );

  for (genvar i = 0; i < 8; i++) begin : gen_sw_assigns
    assign hw2reg.sw_share0_output[i].d  = kmac_data[0][i*32 +: 32];
    assign hw2reg.sw_share1_output[i].d  = kmac_data[1][i*32 +: 32];
    assign hw2reg.sw_share0_output[i].de = data_valid & (key_sel == SwKey);
    assign hw2reg.sw_share1_output[i].de = data_valid & (key_sel == SwKey);
  end


  /////////////////////////////////////
  //  Alerts and Interrupts
  /////////////////////////////////////

  prim_intr_hw #(.Width(1)) u_intr_op_done (
    .clk_i,
    .rst_ni,
    .event_intr_i           (op_done),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.op_done.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.op_done.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.op_done.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.op_done.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.op_done.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.op_done.d),
    .intr_o                 (intr_op_done_o)
  );

  logic [ErrLastPos-1:0] err_code_q;
  assign hw2reg.err_code.invalid_op.d          = reg2hw.err_code.invalid_op.q  |
                                                 err_code[ErrInvalidOp];
  assign hw2reg.err_code.invalid_cmd.d         = reg2hw.err_code.invalid_cmd.q |
                                                 err_code[ErrInvalidCmd];
  assign hw2reg.err_code.invalid_kmac_input.d  = reg2hw.err_code.invalid_kmac_input.q |
                                                 err_code[ErrInvalidIn];
  assign hw2reg.err_code.invalid_kmac_data.d   = reg2hw.err_code.invalid_kmac_data.q |
                                                 err_code[ErrInvalidOut];
  assign hw2reg.err_code.invalid_op.de         = 1'b1;
  assign hw2reg.err_code.invalid_cmd.de        = 1'b1;
  assign hw2reg.err_code.invalid_kmac_input.de = 1'b1;
  assign hw2reg.err_code.invalid_kmac_data.de  = 1'b1;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      err_code_q <= '0;
    end else begin
      err_code_q <= err_code;
    end
  end

  // interrupts are only generated on changes to avoid interrupt storms
  prim_intr_hw #(.Width(1)) u_err_code (
    .clk_i,
    .rst_ni,
    // assert interrupt whenever error code is non-zero and is different
    // from its previous value
    .event_intr_i           (|err_code & (err_code != err_code_q)),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.err.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.err.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.err.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.err.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.err.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.err.d),
    .intr_o                 (intr_err_o)
  );

  // There are two types of alerts
  // - alerts for hardware errors, these could not have been generated by software.
  // - alerts for errors that may have been generated by software.

  logic fault_errs, fault_err_req_q, fault_err_req_d, fault_err_ack;
  logic op_errs, op_err_req_q, op_err_req_d, op_err_ack;

  assign fault_errs = err_code[ErrInvalidOut] | err_code[ErrInvalidCmd];
  assign fault_err_req_d = fault_errs    ? 1'b1 :
                           fault_err_ack ? 1'b0 : fault_err_req_q;

  assign op_errs = err_code[ErrInvalidOp] | err_code[ErrInvalidIn];
  assign op_err_req_d = op_errs    ? 1'b1 :
                        op_err_ack ? 1'b0 : op_err_req_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      fault_err_req_q <= '0;
      op_err_req_q <= '0;
    end else begin
      fault_err_req_q <= fault_err_req_d;
      op_err_req_q <= op_err_req_d;
    end
  end

  logic fault_alert_test;
  assign fault_alert_test = reg2hw.alert_test.fault_err.q & reg2hw.alert_test.fault_err.qe;
  prim_alert_sender #(
    .AsyncOn(AlertAsyncOn)
  ) u_fault_alert (
    .clk_i,
    .rst_ni,
    .alert_req_i(fault_err_req_q | fault_alert_test),
    .alert_ack_o(fault_err_ack),
    .alert_rx_i(alert_rx_i[0]),
    .alert_tx_o(alert_tx_o[0])
  );

  logic op_err_alert_test;
  assign op_err_alert_test = reg2hw.alert_test.operation_err.q &
                             reg2hw.alert_test.operation_err.qe;
  prim_alert_sender #(
    .AsyncOn(AlertAsyncOn)
  ) u_op_err_alert (
    .clk_i,
    .rst_ni,
    .alert_req_i(op_err_req_q | op_err_alert_test),
    .alert_ack_o(op_err_ack),
    .alert_rx_i(alert_rx_i[1]),
    .alert_tx_o(alert_tx_o[1])
  );

  /////////////////////////////////////
  //  Assertions
  /////////////////////////////////////

  // Only 1 entity should be trying to use the secret kmac key input
  `ASSERT(KmacKeyLoadExclusive_a, $onehot0({load_key, data_valid & kmac_sel}))

endmodule // keymgr
