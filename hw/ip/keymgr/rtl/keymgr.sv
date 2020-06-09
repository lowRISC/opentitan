// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Key manager top level
//

`include "prim_assert.sv"

module keymgr import keymgr_pkg::*;(
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
  input flash_key_t flash_i,

  // interrupts and alerts
  output logic intr_op_done_o
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
    .devmode_i  (1'b1)
  );


  /////////////////////////////////////
  //  LFSR
  /////////////////////////////////////

  // A farily large lfsr is used here as entropy in used in multiple places.
  // - populate the default working state
  // - generate random inputs when a bad input is selected
  //
  // The first case is sensitive, and thus the working state is constructed
  // through multiple rounds of the Lfsr
  // The second case is less sensitive and is applied directly.  If the inputs
  // have more bits than the lfsr output, the lfsr value is simply replicated

  logic [63:0] lfsr;

  prim_lfsr #(
    .LfsrDw(64),
    .StateOutDw(64)
  ) i_lfsr (
    .clk_i,
    .rst_ni,
    .lfsr_en_i(1'b1),
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
  logic data_valid;
  logic kmac_done;
  logic kmac_input_invalid;
  logic [Shares-1:0][KeyWidth-1:0] kmac_data;

  keymgr_ctrl i_ctrl
    (
    .clk_i,
    .rst_ni,
    .keymgr_en_i(lc_i.keymgr_en),
    .entropy_i(lfsr[63:32]),  // TBD, recommend directly interfacing with DRBG for keymgr_ctrl
    .init_i(reg2hw.control.init.q),
    .op_i(reg2hw.control.operation.q),
    .op_start_i(reg2hw.control.start.q),
    .op_done_o(op_done),
    .status_o(hw2reg.op_status.status.d),
    .error_o(hw2reg.op_status.error.d),
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
    .kmac_data_i(kmac_data)
    );

  assign hw2reg.control.start.d  = '0;
  assign hw2reg.control.start.de = op_done;
  assign hw2reg.control.init.d  = '0;
  assign hw2reg.control.init.de = op_done;

  assign hw2reg.op_status.status.de = op_done;
  assign hw2reg.op_status.error.de = op_done;

  // working state is always visible
  assign hw2reg.working_state.de = 1'b1;

  // TBD
  // software q / qe have no impact on cfgen
  // however they exist due to a reggen script limitation, this should be addressed later
  keymgr_cfg_en i_cfgen
    (
    .clk_i,
    .rst_ni,
    .keymgr_en_i(lc_i.keymgr_en),
    .set_i(op_done),
    .clr_i(reg2hw.control.start.q),
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
  assign adv_matrix[Creator] = AdvDataWidth'({reg2hw.rom_ext_desc,
                                              RevisionSecret,
                                              otp_i.devid,
                                              lc_i.health_state,
                                              flash_i.div_key});

  // Advance to owner_intermediate_key
  assign adv_matrix[OwnerInt] = AdvDataWidth'({reg2hw.software_binding,flash_i.owner_secret});

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
  keymgr_input_checks i_checks (
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

  keymgr_kmac_if i_kmac_if
    (
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
    .cmd_error_o() // hook up into alerts later
    );


  /////////////////////////////////////
  //  Side load key storage
  /////////////////////////////////////
  keymgr_key_dest_e dest_sel;
  logic aes_sel, hmac_sel, kmac_sel;

  assign dest_sel = reg2hw.control.dest_sel;
  assign aes_sel  = dest_sel == Aes  & key_sel == HwKey;
  assign hmac_sel = dest_sel == Hmac & key_sel == HwKey;
  assign kmac_sel = dest_sel == Kmac & key_sel == HwKey;

  keymgr_sideload_key i_aes_key
    (
    .clk_i,
    .rst_ni,
    .keymgr_en_i(lc_i.keymgr_en),
    .set_i(data_valid & aes_sel),
    .clr_i(lc_i.keymgr_en), // TBD, should add an option for software clear later
    .entropy_i(lfsr[31:0]), //TBD, recommend directly interfacign with DRBG entropy for keys
    .key_i(kmac_data),
    .key_o(aes_key_o)
    );

  keymgr_sideload_key i_hmac_key
    (
    .clk_i,
    .rst_ni,
    .keymgr_en_i(lc_i.keymgr_en),
    .set_i(data_valid & hmac_sel),
    .clr_i(lc_i.keymgr_en), // TBD, should add an option for software clear later
    .entropy_i(lfsr[31:0]),
    .key_i(kmac_data),
    .key_o(hmac_key_o)
    );

  keymgr_sideload_key i_kmac_key
    (
    .clk_i,
    .rst_ni,
    .keymgr_en_i(lc_i.keymgr_en),
    .set_i(load_key | (data_valid & kmac_sel)),
    .clr_i(lc_i.keymgr_en), // TBD, should add an option for software clear later
    .entropy_i(lfsr[31:0]),
    .key_i(load_key ? kmac_key : kmac_data),
    .key_o(kmac_key_o)
    );

  for (genvar i = 0; i < 8; i++) begin : gen_sw_assigns
    assign hw2reg.sw_share0_output[i].d  = kmac_data[0][i*32 +: 32];
    assign hw2reg.sw_share1_output[i].d  = kmac_data[1][i*32 +: 32];
    assign hw2reg.sw_share0_output[i].de = data_valid & (key_sel == HwKey);
    assign hw2reg.sw_share1_output[i].de = data_valid & (key_sel == HwKey);
  end


  /////////////////////////////////////
  //  Alerts and Interrutps - TBD
  /////////////////////////////////////

  prim_intr_hw #(.Width(1)) intr_op_done (
    .event_intr_i           (op_done),
    .reg2hw_intr_enable_q_i (reg2hw.intr_enable.q),
    .reg2hw_intr_test_q_i   (reg2hw.intr_test.q),
    .reg2hw_intr_test_qe_i  (reg2hw.intr_test.qe),
    .reg2hw_intr_state_q_i  (reg2hw.intr_state.q),
    .hw2reg_intr_state_de_o (hw2reg.intr_state.de),
    .hw2reg_intr_state_d_o  (hw2reg.intr_state.d),
    .intr_o                 (intr_op_done_o)
  );


  /////////////////////////////////////
  //  Assertions
  /////////////////////////////////////

  // Only 1 entity should be trying to use the secret kmac key input
  `ASSERT(KmacKeyLoadExclusive_a, $onehot0({load_key, data_valid & kmac_sel}))

endmodule // keymgr
