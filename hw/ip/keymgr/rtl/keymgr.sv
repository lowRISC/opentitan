// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Key manager top level
//

`include "prim_assert.sv"

module keymgr import keymgr_pkg::*; #(
  parameter logic AlertAsyncOn                 = 1'b1,
  parameter lfsr_seed_t RndCnstLfsrSeed        = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t RndCnstLfsrPerm        = RndCnstLfsrPermDefault,
  parameter rand_perm_t RndCnstRandPerm        = RndCnstRandPermDefault,
  parameter seed_t RndCnstRevisionSeed         = RndCnstRevisionSeedDefault,
  parameter seed_t RndCnstCreatorIdentitySeed  = RndCnstCreatorIdentitySeedDefault,
  parameter seed_t RndCnstOwnerIntIdentitySeed = RndCnstOwnerIntIdentitySeedDefault,
  parameter seed_t RndCnstOwnerIdentitySeed    = RndCnstOwnerIdentitySeedDefault,
  parameter seed_t RndCnstSoftOutputSeed       = RndCnstSoftOutputSeedDefault,
  parameter seed_t RndCnstHardOutputSeed       = RndCnstHardOutputSeedDefault,
  parameter seed_t RndCnstNoneSeed             = RndCnstNoneSeedDefault,
  parameter seed_t RndCnstAesSeed              = RndCnstAesSeedDefault,
  parameter seed_t RndCnstHmacSeed             = RndCnstHmacSeedDefault,
  parameter seed_t RndCnstKmacSeed             = RndCnstKmacSeedDefault
) (
  input clk_i,
  input rst_ni,
  input clk_edn_i,
  input rst_edn_ni,

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
  input lc_ctrl_pkg::lc_tx_t lc_keymgr_en_i,
  input lc_ctrl_pkg::lc_keymgr_div_t lc_keymgr_div_i,
  input otp_ctrl_pkg::otp_keymgr_key_t otp_key_i,
  input otp_ctrl_part_pkg::otp_hw_cfg_t otp_hw_cfg_i,
  input flash_ctrl_pkg::keymgr_flash_t flash_i,

  // connection to edn
  output edn_pkg::edn_req_t edn_o,
  input edn_pkg::edn_rsp_t edn_i,

  // interrupts and alerts
  output logic intr_op_done_o,
  input  prim_alert_pkg::alert_rx_t [keymgr_reg_pkg::NumAlerts-1:0] alert_rx_i,
  output prim_alert_pkg::alert_tx_t [keymgr_reg_pkg::NumAlerts-1:0] alert_tx_o
);

  import keymgr_reg_pkg::*;

  `ASSERT_INIT(AdvDataWidth_A, AdvDataWidth <= KDFMaxWidth)
  `ASSERT_INIT(IdDataWidth_A,  IdDataWidth  <= KDFMaxWidth)
  `ASSERT_INIT(GenDataWidth_A, GenDataWidth <= KDFMaxWidth)
  `ASSERT_INIT(OutputKeyDiff_A, RndCnstHardOutputSeed != RndCnstSoftOutputSeed)

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
    .intg_err_o (),
    .devmode_i  (1'b1) // connect to real devmode signal in the future
  );


  /////////////////////////////////////
  //  Synchronize lc_ctrl control inputs
  //  Data inputs are not synchronized and assumed quasi-static
  /////////////////////////////////////
  lc_ctrl_pkg::lc_tx_t [KeyMgrEnLast-1:0] lc_keymgr_en;

  prim_lc_sync #(
    .NumCopies(int'(KeyMgrEnLast))
  ) u_lc_keymgr_en_sync (
    .clk_i,
    .rst_ni,
    .lc_en_i(lc_keymgr_en_i),
    .lc_en_o(lc_keymgr_en)
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

  logic seed_en;
  logic [LfsrWidth-1:0] seed;
  logic reseed_req;
  logic reseed_ack;

  keymgr_reseed_ctrl u_reseed_ctrl (
    .clk_i,
    .rst_ni,
    .clk_edn_i,
    .rst_edn_ni,
    .reseed_req_i(reseed_req),
    .reseed_ack_o(reseed_ack),
    .reseed_interval_i(reg2hw.reseed_interval.q),
    .edn_o,
    .edn_i,
    .seed_en_o(seed_en),
    .seed_o(seed)
  );

  logic [63:0] lfsr;
  logic ctrl_lfsr_en, data_lfsr_en, sideload_lfsr_en;

  prim_lfsr #(
    .LfsrDw(LfsrWidth),
    .StateOutDw(LfsrWidth),
    .DefaultSeed(RndCnstLfsrSeed),
    .StatePermEn(1'b1),
    .StatePerm(RndCnstLfsrPerm)
  ) u_lfsr (
    .clk_i,
    .rst_ni,
    .lfsr_en_i(ctrl_lfsr_en | data_lfsr_en | sideload_lfsr_en),
    // The seed update is skipped if there is an ongoing keymgr transaction.
    // This is not really done for any functional purpose but more to simplify
    // DV. When an invalid operation is selected, the keymgr just starts transmitting
    // whatever is at the prng output, however, this may cause a dv protocol violation
    // if a reseed happens to coincide.
    .seed_en_i(seed_en & ~reg2hw.control.start.q),
    .seed_i(seed),
    .entropy_i('0),
    .state_o(lfsr)
  );


  logic [Shares-1:0][RandWidth-1:0] ctrl_rand;
  logic [Shares-1:0][RandWidth-1:0] data_rand;

  assign ctrl_rand[0] = lfsr[63:32];
  assign ctrl_rand[1] = perm_data(lfsr[31:0], RndCnstRandPerm);

  assign data_rand[0] = lfsr[31:0];
  assign data_rand[1] = perm_data(lfsr[63:32], RndCnstRandPerm);

  /////////////////////////////////////
  //  Key Manager Control
  /////////////////////////////////////

  keymgr_stage_e stage_sel;
  keymgr_gen_out_e key_sel;
  logic adv_en, id_en, gen_en;
  logic load_key;
  logic wipe_key;
  hw_key_req_t kmac_key;
  logic op_done;
  logic init;
  logic data_valid;
  logic data_en;
  logic kmac_done;
  logic kmac_input_invalid;
  logic kmac_cmd_err;
  logic kmac_fsm_err;
  logic kmac_op_err;
  logic [Shares-1:0][KeyWidth-1:0] kmac_data;
  logic [ErrLastPos-1:0] err_code;
  logic sw_binding_unlock;

  keymgr_ctrl u_ctrl (
    .clk_i,
    .rst_ni,
    .en_i(lc_keymgr_en[KeyMgrEnCtrl] == lc_ctrl_pkg::On),
    .prng_reseed_req_o(reseed_req),
    .prng_reseed_ack_i(reseed_ack),
    .prng_en_o(ctrl_lfsr_en),
    .entropy_i(ctrl_rand),
    .op_i(keymgr_ops_e'(reg2hw.control.operation.q)),
    .op_start_i(reg2hw.control.start.q),
    .op_done_o(op_done),
    .init_o(init),
    .sw_binding_unlock_o(sw_binding_unlock),
    .status_o(hw2reg.op_status.d),
    .error_o(err_code),
    .data_en_o(data_en),
    .data_valid_o(data_valid),
    .working_state_o(hw2reg.working_state.d),
    .root_key_i(otp_key_i),
    .hw_sel_o(key_sel),
    .stage_sel_o(stage_sel),
    .load_key_o(load_key),
    .wipe_key_o(wipe_key),
    .adv_en_o(adv_en),
    .id_en_o(id_en),
    .gen_en_o(gen_en),
    .key_o(kmac_key),
    .kmac_done_i(kmac_done),
    .kmac_input_invalid_i(kmac_input_invalid),
    .kmac_fsm_err_i(kmac_fsm_err),
    .kmac_op_err_i(kmac_op_err),
    .kmac_cmd_err_i(kmac_cmd_err),
    .kmac_data_i(kmac_data)
  );

  assign hw2reg.control.start.d  = '0;
  assign hw2reg.control.start.de = op_done;
  // as long as operation is ongoing, capture status
  assign hw2reg.op_status.de = reg2hw.control.start.q;

  // working state is always visible
  assign hw2reg.working_state.de = 1'b1;

  // key manager registers cannot be changed once an operation starts
  keymgr_cfg_en #(
    .NonInitClr(1'b1) // clear has effect even when non-init
  ) u_cfgen (
    .clk_i,
    .rst_ni,
    .init_i(init),
    .en_i(lc_keymgr_en[KeyMgrEnCfgEn] == lc_ctrl_pkg::On),
    .set_i(reg2hw.control.start.q & op_done),
    .clr_i(reg2hw.control.start.q),
    .out_o(hw2reg.cfg_regwen.d)
  );


  logic sw_binding_set;
  logic sw_binding_clr;
  logic sw_binding_regwen;

  // set on a successful advance
  assign sw_binding_set = reg2hw.control.operation.q == OpAdvance &
                          sw_binding_unlock;

  // this is w0c
  assign sw_binding_clr = reg2hw.sw_binding_regwen.qe & ~reg2hw.sw_binding_regwen.q;

  // software clears the enable
  // hardware restores it upon successful advance
  keymgr_cfg_en #(
    .NonInitClr(1'b0)  // clear has no effect until init
  ) u_sw_binding_regwen (
    .clk_i,
    .rst_ni,
    .init_i(init),
    .en_i(lc_keymgr_en[KeyMgrEnSwBindingEn] == lc_ctrl_pkg::On),
    .set_i(sw_binding_set),
    .clr_i(sw_binding_clr),
    .out_o(sw_binding_regwen)
  );

  assign hw2reg.sw_binding_regwen.d = sw_binding_regwen & hw2reg.cfg_regwen.d;

  /////////////////////////////////////
  //  Key Manager Input Construction
  /////////////////////////////////////

  // The various arrays of inputs for each operation
  logic [2**StageWidth-1:0][AdvDataWidth-1:0] adv_matrix;
  logic [2**StageWidth-1:0] adv_dvalid;
  logic [2**StageWidth-1:0][IdDataWidth-1:0] id_matrix;
  logic [GenDataWidth-1:0] gen_in;

  // The max key version for each stage
  logic [2**StageWidth-1:0][31:0] max_key_versions;

  // Number of times the lfsr output fits into the inputs
  localparam int AdvLfsrCopies = AdvDataWidth / 32;
  localparam int IdLfsrCopies = IdDataWidth / 32;
  localparam int GenLfsrCopies = GenDataWidth / 32;

  // input checking
  logic creator_seed_vld;
  logic owner_seed_vld;
  logic devid_vld;
  logic health_state_vld;
  logic key_version_vld;


  // Advance state operation input construction
  for (genvar i = KeyMgrStages; i < 2**StageWidth; i++) begin : gen_adv_matrix_fill
    assign adv_matrix[i] = {AdvLfsrCopies{data_rand[0]}};
    assign adv_dvalid[i] = 1'b1;
  end

  // Advance to creator_root_key
  // The values coming from otp_ctrl / lc_ctrl are treat as quasi-static for CDC purposes
  logic [KeyWidth-1:0] creator_seed;
  assign creator_seed = flash_i.seeds[flash_ctrl_pkg::CreatorSeedIdx];
  assign adv_matrix[Creator] = AdvDataWidth'({reg2hw.sw_binding,
                                              RndCnstRevisionSeed,
                                              otp_hw_cfg_i.data.device_id,
                                              HealthStateWidth'(lc_keymgr_div_i),
                                              creator_seed});

  logic unused_otp_bits;
  assign unused_otp_bits = ^otp_hw_cfg_i;

  assign adv_dvalid[Creator] = creator_seed_vld &
                               devid_vld &
                               health_state_vld;

  // Advance to owner_intermediate_key
  logic [KeyWidth-1:0] owner_seed;
  assign owner_seed = flash_i.seeds[flash_ctrl_pkg::OwnerSeedIdx];
  assign adv_matrix[OwnerInt] = AdvDataWidth'({reg2hw.sw_binding,owner_seed});
  assign adv_dvalid[OwnerInt] = owner_seed_vld;

  // Advance to owner_key
  assign adv_matrix[Owner] = AdvDataWidth'(reg2hw.sw_binding);
  assign adv_dvalid[Owner] = 1'b1;

  // Generate Identity operation input construction
  for (genvar i = KeyMgrStages; i < 2**StageWidth; i++) begin : gen_id_matrix_fill
    assign id_matrix[i] = {IdLfsrCopies{data_rand[0]}};
  end

  assign id_matrix[Creator]  = RndCnstCreatorIdentitySeed;
  assign id_matrix[OwnerInt] = RndCnstOwnerIntIdentitySeed;
  assign id_matrix[Owner]    = RndCnstOwnerIdentitySeed;


  // Generate output operation input construction
  logic [KeyWidth-1:0] output_key;
  keymgr_key_dest_e cipher_sel;
  logic [KeyWidth-1:0] cipher_seed;

  assign cipher_sel = keymgr_key_dest_e'(reg2hw.control.dest_sel);
  assign cipher_seed = cipher_sel == Aes  ? RndCnstAesSeed :
                       cipher_sel == Hmac ? RndCnstHmacSeed :
                       cipher_sel == Kmac ? RndCnstKmacSeed : RndCnstNoneSeed;
  assign output_key = (key_sel == HwKey) ? RndCnstHardOutputSeed : RndCnstSoftOutputSeed;
  assign gen_in = (stage_sel == Disable) ? {GenLfsrCopies{lfsr[31:0]}} : {reg2hw.key_version,
                                                                          reg2hw.salt,
                                                                          cipher_seed,
                                                                          output_key};

  // Advance state operation input construction
  for (genvar i = KeyMgrStages; i < 2**StageWidth; i++) begin : gen_key_version_fill
    assign max_key_versions[i] = '0;
  end

  assign max_key_versions[Creator]  = reg2hw.max_creator_key_ver;
  assign max_key_versions[OwnerInt] = reg2hw.max_owner_int_key_ver;
  assign max_key_versions[Owner]    = reg2hw.max_owner_key_ver;


  // General module for checking inputs
  logic key_vld;
  keymgr_input_checks u_checks (
    .max_key_versions_i(max_key_versions),
    .stage_sel_i(stage_sel),
    .key_version_i(reg2hw.key_version),
    .creator_seed_i(creator_seed),
    .owner_seed_i(owner_seed),
    .key_i(kmac_key_o),
    .devid_i(otp_hw_cfg_i.data.device_id),
    .health_state_i(HealthStateWidth'(lc_keymgr_div_i)),
    .creator_seed_vld_o(creator_seed_vld),
    .owner_seed_vld_o(owner_seed_vld),
    .devid_vld_o(devid_vld),
    .health_state_vld_o(health_state_vld),
    .key_version_vld_o(key_version_vld),
    .key_vld_o(key_vld)
  );


  /////////////////////////////////////
  //  KMAC Control
  /////////////////////////////////////

  logic [3:0] invalid_data;
  assign invalid_data[OpAdvance]  = ~key_vld | ~adv_dvalid[stage_sel];
  assign invalid_data[OpGenId]    = ~key_vld;
  assign invalid_data[OpGenSwOut] = ~key_vld | ~key_version_vld;
  assign invalid_data[OpGenHwOut] = ~key_vld | ~key_version_vld;

  keymgr_kmac_if u_kmac_if (
    .clk_i,
    .rst_ni,
    .prng_en_o(data_lfsr_en),
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
    .entropy_i(data_rand),
    .fsm_error_o(kmac_fsm_err),
    .kmac_error_o(kmac_op_err),
    .cmd_error_o(kmac_cmd_err)
  );


  /////////////////////////////////////
  //  Side load key storage
  /////////////////////////////////////
  keymgr_sideload_key_ctrl u_sideload_ctrl (
    .clk_i,
    .rst_ni,
    .init_i(init),
    .entropy_i(data_rand),
    .clr_key_i(reg2hw.sideload_clear.q),
    .wipe_key_i(wipe_key),
    .dest_sel_i(cipher_sel),
    .key_sel_i(key_sel),
    .load_key_i(load_key),
    .data_en_i(data_en),
    .data_valid_i(data_valid),
    .key_i(kmac_key),
    .data_i(kmac_data),
    .prng_en_o(sideload_lfsr_en),
    .aes_key_o(aes_key_o),
    .hmac_key_o(hmac_key_o),
    .kmac_key_o(kmac_key_o)
  );

  for (genvar i = 0; i < 8; i++) begin : gen_sw_assigns
    assign hw2reg.sw_share0_output[i].d  = ~data_en | wipe_key ? data_rand[0] :
                                                                 kmac_data[0][i*32 +: 32];
    assign hw2reg.sw_share1_output[i].d  = ~data_en | wipe_key ? data_rand[1] :
                                                                 kmac_data[1][i*32 +: 32];
    assign hw2reg.sw_share0_output[i].de = wipe_key | data_valid & (key_sel == SwKey);
    assign hw2reg.sw_share1_output[i].de = wipe_key | data_valid & (key_sel == SwKey);
  end


  /////////////////////////////////////
  //  Alerts and Interrupts
  /////////////////////////////////////

  prim_intr_hw #(.Width(1)) u_intr_op_done (
    .clk_i,
    .rst_ni,
    .event_intr_i           (op_done),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.d),
    .intr_o                 (intr_op_done_o)
  );

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
  assign fault_alert_test = reg2hw.alert_test.fatal_fault_err.q &
                            reg2hw.alert_test.fatal_fault_err.qe;
  prim_alert_sender #(
    .AsyncOn(AlertAsyncOn),
    .IsFatal(1)
  ) u_fault_alert (
    .clk_i,
    .rst_ni,
    .alert_test_i(fault_alert_test),
    .alert_req_i(fault_err_req_q),
    .alert_ack_o(fault_err_ack),
    .alert_state_o(),
    .alert_rx_i(alert_rx_i[0]),
    .alert_tx_o(alert_tx_o[0])
  );

  logic op_err_alert_test;
  assign op_err_alert_test = reg2hw.alert_test.recov_operation_err.q &
                             reg2hw.alert_test.recov_operation_err.qe;
  prim_alert_sender #(
    .AsyncOn(AlertAsyncOn),
      .IsFatal(0)
  ) u_op_err_alert (
    .clk_i,
    .rst_ni,
    .alert_test_i(op_err_alert_test),
    .alert_req_i(op_err_req_q),
    .alert_ack_o(op_err_ack),
    .alert_state_o(),
    .alert_rx_i(alert_rx_i[1]),
    .alert_tx_o(alert_tx_o[1])
  );

  // known asserts
  `ASSERT_KNOWN(TlDValidKnownO_A, tl_o.d_valid)
  `ASSERT_KNOWN(TlAReadyKnownO_A, tl_o.a_ready)
  `ASSERT_KNOWN(IntrKnownO_A, intr_op_done_o)
  `ASSERT_KNOWN(AlertKnownO_A, alert_tx_o)

  // the keys are not reset to any specific values
  // TBD this may be changed depending on whether we want to support this
  // mode of operation going forward.
  `ASSERT_KNOWN(AesKeyKnownO_A,  aes_key_o.valid)
  `ASSERT_KNOWN(HmacKeyKnownO_A, hmac_key_o.valid)
  `ASSERT_KNOWN(KmacKeyKnownO_A, kmac_key_o.valid)
  `ASSERT_KNOWN(KmacDataKnownO_A, kmac_data_o)



endmodule // keymgr
