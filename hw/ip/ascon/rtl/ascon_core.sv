// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Ascon core implementation

module ascon_core
  import ascon_reg_pkg::*;
  import ascon_pkg::*;
(
  input clk_i,
  input rst_ni,

  // Life cycle
  input  lc_ctrl_pkg::lc_tx_t lc_escalate_en_i,

  // Alerts
  output logic alert_recov_o,
  output logic alert_fatal_o,

  // Key Manager
  input keymgr_pkg::hw_key_req_t keymgr_key_i,

  // Bus Interface
  input  ascon_reg2hw_t reg2hw,
  output ascon_hw2reg_t hw2reg
);

  // Signals
  logic [3:0][31:0] data_share0_in_d;
  logic [3:0][31:0] data_share0_in_q;
  logic [3:0]       data_share0_in_new_d, data_share0_in_new_q;
  logic             data_share0_in_new;
  logic             data_share0_in_load;

  logic [3:0][31:0] data_share1_in_d;
  logic [3:0][31:0] data_share1_in_q;
  logic [3:0]       data_share1_in_new_d, data_share1_in_new_q;
  logic             data_share1_in_new;
  logic             data_share1_in_load;

  logic [3:0][31:0] tag_in_q;
  logic [3:0]       tag_in_new_d, tag_in_new_q;
  logic             tag_in_new;
  logic             tag_in_load;

  logic [3:0][31:0] nonce_share0_in_d;
  logic [3:0][31:0] nonce_share0_in_q;
  logic [3:0]       nonce_share0_in_new_d, nonce_share0_in_new_q;
  logic             nonce_share0_in_new;
  logic             nonce_share0_in_load;

  logic [3:0][31:0] nonce_share1_in_d;
  logic [3:0][31:0] nonce_share1_in_q;
  logic [3:0]       nonce_share1_in_new_d, nonce_share1_in_new_q;
  logic             nonce_share1_in_new;
  logic             nonce_share1_in_load;

  logic [3:0][31:0] key_share0_in_d;
  logic [3:0][31:0] key_share0_in_q;
  logic [3:0]       key_share0_in_new_d, key_share0_in_new_q;
  logic             key_share0_in_new;
  logic             key_share0_in_load;

  logic [3:0][31:0] key_share1_in_d;
  logic [3:0][31:0] key_share1_in_q;
  logic [3:0]       key_share1_in_new_d, key_share1_in_new_q;
  logic             key_share1_in_new;
  logic             key_share1_in_load;

  logic           force_data_overwrite;
  logic           manual_start_trigger;
  ascon_op_e      operation;
  ascon_variant_e ascon_variant;
  logic           sideload_key;
  logic           start, wipe;
  logic           masked_ad_input;
  logic           masked_msg_input;
  logic  [4:0]    valid_bytes;
  logic [11:0]    data_type_last;
  logic [11:0]    data_type_start;
  logic           no_ad;
  logic           no_msg;

  logic [3:0][31:0] msg_out_d;
  logic [3:0][31:0] msg_out_q;
  logic             msg_out_we;
  logic [3:0][31:0] unused_msg_out_q;
  logic [3:0]       msg_out_read_d, msg_out_read_q;
  logic             msg_out_read;

  logic [3:0][31:0] tag_out_d;
  logic [3:0][31:0] tag_out_q;
  logic             tag_out_we;
  logic [3:0][31:0] unused_tag_out_q;
  logic [3:0]       tag_out_read_d, tag_out_read_q;
  logic             tag_out_read;

  assign alert_recov_o = 1'b0;
  assign alert_fatal_o = 1'b0;

  lc_ctrl_pkg::lc_tx_t      unused_lc_escalate_en_i;
  keymgr_pkg::hw_key_req_t  unused_keymgr_key_i;

  // TODO
  assign unused_keymgr_key_i     = keymgr_key_i;
  assign unused_lc_escalate_en_i = lc_escalate_en_i;

  ///// DATA REGISTERS ///////

  // Input conversion
  for (genvar i = 0; i < 4; i++) begin : gen_reg2hw_conversion
    assign key_share0_in_d[i] = reg2hw.key_share0[i].q;
    assign key_share1_in_d[i] = reg2hw.key_share1[i].q;
    assign data_share0_in_d[i] = reg2hw.data_in_share0[i].q;
    assign data_share1_in_d[i] = reg2hw.data_in_share1[i].q;
    assign tag_in_q[i] = reg2hw.tag_in[i].q;
    assign nonce_share0_in_d[i] = reg2hw.nonce_share0[i].q;
    assign nonce_share1_in_d[i] = reg2hw.nonce_share1[i].q;
  end

  // hwext input registers
  for (genvar i = 0; i < 4; i++) begin : gen_hw_ext_input_regs
    always_ff @(posedge clk_i or negedge rst_ni) begin : input_reg_key_share0
      if (!rst_ni) begin
        key_share0_in_q[i] <= '{default: '0};
      end else if (reg2hw.key_share0[i].qe) begin
        key_share0_in_q[i] <= key_share0_in_d[i];
      end
    end
    assign hw2reg.key_share0[i].d = '0;
    //assign unused_key_share0_re[i] = hw2reg.key_share0[i].re;

    always_ff @(posedge clk_i or negedge rst_ni) begin : input_reg_key_share1
      if (!rst_ni) begin
        key_share1_in_q[i] <= '{default: '0};
      end else if (reg2hw.key_share1[i].qe) begin
        key_share1_in_q[i] <= key_share1_in_d[i];
      end
    end
    assign hw2reg.key_share1[i].d = '0;

    always_ff @(posedge clk_i or negedge rst_ni) begin : input_reg_nonce_share0
      if (!rst_ni) begin
        nonce_share0_in_q[i] <= '{default: '0};
      end else if (reg2hw.nonce_share0[i].qe) begin
        nonce_share0_in_q[i] <= nonce_share0_in_d[i];
      end
    end
    assign hw2reg.nonce_share0[i].d = '0;

    always_ff @(posedge clk_i or negedge rst_ni) begin : input_reg_nonce_share1
      if (!rst_ni) begin
        nonce_share1_in_q[i] <= '{default: '0};
      end else if (reg2hw.nonce_share1[i].qe) begin
        nonce_share1_in_q[i] <= nonce_share1_in_d[i];
      end
    end
    assign hw2reg.nonce_share1[i].d = '0;

    always_ff @(posedge clk_i or negedge rst_ni) begin : input_data_share0
      if (!rst_ni) begin
        data_share0_in_q[i] <= '{default: '0};
      end else if (reg2hw.data_in_share0[i].qe) begin
        data_share0_in_q[i] <= data_share0_in_d[i];
      end
    end
    assign hw2reg.data_in_share0[i].d = '0;

    always_ff @(posedge clk_i or negedge rst_ni) begin : input_data_share1
      if (!rst_ni) begin
        data_share1_in_q[i] <= '{default: '0};
      end else if (reg2hw.data_in_share1[i].qe) begin
        data_share1_in_q[i] <= data_share1_in_d[i];
      end
    end
    assign hw2reg.data_in_share1[i].d = '0;

  end

  // hwext output registers
  for (genvar i = 0; i < 4; i++) begin : gen_hw_ext_output_regs
    always_ff @(posedge clk_i or negedge rst_ni) begin : reg_msg_out
      if (!rst_ni) begin
        msg_out_q[i] <= '{default: '0};
      end else if (msg_out_we) begin
        msg_out_q[i] <= msg_out_d[i];
      end
    end
    assign unused_msg_out_q[i] = reg2hw.msg_out[i].q;

    always_ff @(posedge clk_i or negedge rst_ni) begin : reg_tag_out
      if (!rst_ni) begin
        tag_out_q[i] <= '{default: '0};
      end else if (tag_out_we) begin
        tag_out_q[i] <= tag_out_d[i];
      end
    end
    assign unused_tag_out_q[i] = reg2hw.tag_out[i].q;
  end

    // Output conversion
  for (genvar i = 0; i < 4; i++) begin : g_hw2_reg_conversion
    assign hw2reg.msg_out[i].d = msg_out_q[i];
    assign hw2reg.tag_out[i].d = tag_out_q[i];
  end


  // CTRL
  assign operation            = reg2hw.ctrl_shadowed.operation.q;
  assign ascon_variant        = reg2hw.ctrl_shadowed.ascon_variant.q;
  assign sideload_key         = reg2hw.ctrl_shadowed.sideload_key.q;
  assign masked_msg_input     = reg2hw.ctrl_shadowed.masked_msg_input.q;
  assign masked_ad_input      = reg2hw.ctrl_shadowed.masked_ad_input.q;

  // CTRL_AUX
  assign force_data_overwrite = reg2hw.ctrl_aux_shadowed.force_data_overwrite.q;
  assign manual_start_trigger = reg2hw.ctrl_aux_shadowed.manual_start_trigger.q;

  // BLOCK_CTRL
  assign valid_bytes          = reg2hw.block_ctrl_shadowed.valid_bytes.q;
  assign data_type_last       = reg2hw.block_ctrl_shadowed.data_type_last.q;
  assign data_type_start      = reg2hw.block_ctrl_shadowed.data_type_start.q;
  assign no_ad                = reg2hw.ctrl_shadowed.no_ad.q;
  assign no_msg               = reg2hw.ctrl_shadowed.no_msg.q;

  // TRIGGER
  assign start                = reg2hw.trigger.start.q;
  assign wipe                 = reg2hw.trigger.wipe.q;


  assign hw2reg.trigger.start.d   = 1'b0;
  assign hw2reg.trigger.start.de  = 1'b1;

  assign hw2reg.trigger.wipe.d   = 1'b0;
  assign hw2reg.trigger.wipe.de  = 1'b1;

  // TODO STATUS
  assign hw2reg.status.idle.d   = 1'b0;
  assign hw2reg.status.idle.de  = 1'b1;
  assign hw2reg.status.stall.d  = 1'b0;
  assign hw2reg.status.stall.de = 1'b1;
  assign hw2reg.status.wait_edn.d  = 1'b0;
  assign hw2reg.status.wait_edn.de = 1'b1;
  assign hw2reg.status.ascon_error.d  = 1'b0;
  assign hw2reg.status.ascon_error.de = 1'b1;
  assign hw2reg.status.alert_recov_ctrl_update_err.d  = 1'b0;
  assign hw2reg.status.alert_recov_ctrl_update_err.de = 1'b1;
  assign hw2reg.status.alert_recov_ctrl_aux_update_err.d  = 1'b0;
  assign hw2reg.status.alert_recov_ctrl_aux_update_err.de = 1'b1;
  assign hw2reg.status.alert_recov_block_ctrl_update_err.d  = 1'b0;
  assign hw2reg.status.alert_recov_block_ctrl_update_err.de = 1'b1;
  assign hw2reg.status.alert_fatal_fault.d  = 1'b0;
  assign hw2reg.status.alert_fatal_fault.de = 1'b1;

  // TODO BLOCK STATUS
  assign hw2reg.output_valid.data_type.d  = 3'b000;
  assign hw2reg.output_valid.data_type.de = 1'b1;
  assign hw2reg.output_valid.tag_comparison_valid.d  = 2'b00;
  assign hw2reg.output_valid.tag_comparison_valid.de = 1'b1;

  // TODO FSM_STATE
  assign hw2reg.fsm_state.d  = '0;
  logic [31:0] unused_fsm_state_q;
  logic        unused_fsm_state_qe;
  assign unused_fsm_state_q  = reg2hw.fsm_state.q;
  assign unused_fsm_state_qe = reg2hw.fsm_state.qe;


  // TODO FSM_STATE_REGEN

  // TODO ERROR
  assign hw2reg.error.no_key.d  = 1'b0;
  assign hw2reg.error.no_key.de = 1'b1;
  assign hw2reg.error.no_nonce.d  = 1'b0;
  assign hw2reg.error.no_nonce.de = 1'b1;
  assign hw2reg.error.wrong_order.d  = 1'b0;
  assign hw2reg.error.wrong_order.de = 1'b1;
  assign hw2reg.error.flag_input_missmatch.d  = 1'b0;
  assign hw2reg.error.flag_input_missmatch.de = 1'b1;

  //  DECTION LOGIC /////
  // Detect new key, new input, output read
  // Edge detectors are cleared by the FSM
  assign key_share0_in_new_d = key_share0_in_load ? '0 : key_share0_in_new_q |
      {reg2hw.key_share0[3].qe, reg2hw.key_share0[2].qe,
       reg2hw.key_share0[1].qe, reg2hw.key_share0[0].qe};
  assign key_share0_in_new = &key_share0_in_new_d;

  assign key_share1_in_new_d = key_share1_in_load ? '0 : key_share1_in_new_q |
      {reg2hw.key_share1[3].qe, reg2hw.key_share1[2].qe,
       reg2hw.key_share1[1].qe, reg2hw.key_share1[0].qe};
  assign key_share1_in_new = &key_share1_in_new_d;

  assign nonce_share0_in_new_d = nonce_share0_in_load ? '0 : nonce_share0_in_new_q |
      {reg2hw.nonce_share0[3].qe, reg2hw.nonce_share0[2].qe,
       reg2hw.nonce_share0[1].qe, reg2hw.nonce_share0[0].qe};
  assign nonce_share0_in_new = &nonce_share0_in_new_d;

  assign nonce_share1_in_new_d = nonce_share1_in_load ? '0 : nonce_share1_in_new_q |
      {reg2hw.nonce_share1[3].qe, reg2hw.nonce_share1[2].qe,
       reg2hw.nonce_share1[1].qe, reg2hw.nonce_share1[0].qe};
  assign nonce_share1_in_new = &nonce_share1_in_new_d;

  assign data_share0_in_new_d = data_share0_in_load ? '0 : data_share0_in_new_q |
      {reg2hw.data_in_share0[3].qe, reg2hw.data_in_share0[2].qe,
       reg2hw.data_in_share0[1].qe, reg2hw.data_in_share0[0].qe};
  assign data_share0_in_new = &data_share0_in_new_d;

  assign data_share1_in_new_d = data_share1_in_load ? '0 : data_share1_in_new_q |
      {reg2hw.data_in_share1[3].qe, reg2hw.data_in_share1[2].qe,
       reg2hw.data_in_share1[1].qe, reg2hw.data_in_share1[0].qe};
  assign data_share1_in_new = &data_share1_in_new_d;

  assign tag_in_new_d = tag_in_load ? '0 : tag_in_new_q |
      {reg2hw.tag_in[3].qe, reg2hw.tag_in[2].qe, reg2hw.tag_in[1].qe, reg2hw.tag_in[0].qe};
  assign tag_in_new = &tag_in_new_d;

  assign msg_out_read_d = msg_out_we ? '0 : msg_out_read_q |
      {reg2hw.msg_out[3].re, reg2hw.msg_out[2].re, reg2hw.msg_out[1].re, reg2hw.msg_out[0].re};
  assign msg_out_read = &msg_out_read_d;

  assign tag_out_read_d = tag_out_we ? '0 : tag_out_read_q |
      {reg2hw.tag_out[3].re, reg2hw.tag_out[2].re, reg2hw.tag_out[1].re, reg2hw.tag_out[0].re};
  assign tag_out_read = &tag_out_read_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_edge_detection
    if (!rst_ni) begin
      key_share0_in_new_q   <= '0;
      key_share1_in_new_q   <= '0;
      nonce_share0_in_new_q <= '0;
      nonce_share1_in_new_q <= '0;
      data_share0_in_new_q  <= '0;
      data_share1_in_new_q  <= '0;
      tag_in_new_q          <= '0;
      msg_out_read_q        <= '0;
      tag_out_read_q        <= '0;
    end else begin
      key_share0_in_new_q   <= key_share0_in_new_d;
      key_share1_in_new_q   <= key_share1_in_new_d;
      nonce_share0_in_new_q <= nonce_share0_in_new_d;
      nonce_share1_in_new_q <= nonce_share1_in_new_d;
      data_share0_in_new_q  <= data_share0_in_new_d;
      data_share1_in_new_q  <= data_share1_in_new_d;
      tag_in_new_q          <= tag_in_new_d;
      msg_out_read_q        <= msg_out_read_d;
      tag_out_read_q        <= tag_out_read_d;
    end
  end

  // FUNCTIONALITY

  // TODO: We don't use the edge detection
  logic unused_data_share0_in_new;
  logic unused_data_share1_in_new;
  logic unused_tag_in_new;
  logic unused_key_share0_in_new;
  logic unused_key_share1_in_new;
  logic unused_nonce_share0_in_new;
  logic unused_nonce_share1_in_new;
  logic unused_msg_out_read;
  logic unused_tag_out_read;
  logic unused_no_ad;
  logic unused_no_msg;
  assign unused_data_share0_in_new   = data_share0_in_new;
  assign unused_data_share1_in_new   = data_share1_in_new;
  assign unused_tag_in_new   = tag_in_new;
  assign unused_nonce_share0_in_new = nonce_share0_in_new;
  assign unused_nonce_share1_in_new = nonce_share1_in_new;
  assign unused_key_share0_in_new  = key_share0_in_new;
  assign unused_key_share1_in_new  = key_share1_in_new;
  assign unused_msg_out_read = msg_out_read;
  assign unused_tag_out_read = tag_out_read;
  assign unused_no_ad = no_ad;
  assign unused_no_msg = no_msg;


  // TODO: Build a very basic FSM here
  assign key_share0_in_load = 1'b0;
  assign key_share1_in_load = 1'b0;
  assign nonce_share0_in_load = 1'b0;
  assign nonce_share1_in_load = 1'b0;
  assign data_share0_in_load = 1'b0;
  assign data_share1_in_load = 1'b0;
  assign tag_in_load = 1'b0;
  assign msg_out_we  = keymgr_key_i.valid;
  assign tag_out_we  = keymgr_key_i.valid;

  // TODO: We don't use any control signals
  logic           unused_force_data_overwrite;
  logic           unused_manual_start_trigger;
  ascon_variant_e unused_ascon_variant;
  ascon_op_e      unused_operation;
  logic           unused_start;
  logic           unused_wipe;
  logic           unused_masked_msg_input;
  logic           unused_masked_ad_input;
  logic           unused_sideload_key;
  logic [4:0]     unused_valid_bytes;
  logic [11:0]    unused_data_type_start;
  logic [11:0]    unused_data_type_last;

  assign unused_force_data_overwrite = force_data_overwrite;
  assign unused_manual_start_trigger = manual_start_trigger;
  assign unused_operation            = operation;
  assign unused_ascon_variant        = ascon_variant;
  assign unused_start                = start;
  assign unused_wipe                 = wipe;
  assign unused_masked_ad_input      = masked_ad_input;
  assign unused_masked_msg_input     = masked_msg_input;
  assign unused_sideload_key         = sideload_key;
  assign unused_valid_bytes          = valid_bytes;
  assign unused_data_type_last       = data_type_last;
  assign unused_data_type_start      = data_type_start;


  // This is some dummy logic to be able to instantiate the module
  // It XORS key_in, nonce_in, and mesg_in. The result is written to msg_out
  // Tag_in is directly written to Tag_out
  // Ctrl is ignored in this very first version
  // Status and Error are set to fixed values
  // The other register are not connected.

  logic [31:0] key_in[4];
  logic [31:0] data_in[4];
  logic [31:0] nonce_in[4];
  for (genvar i = 0; i < 4; i++) begin : gen_dummy_op
    assign nonce_in[i] = nonce_share0_in_q[i] ^ nonce_share1_in_q[i];
    assign key_in[i] = key_share0_in_q[i] ^ key_share1_in_q[i];
    assign data_in[i] = data_share0_in_q[i] ^ data_share1_in_q[i];
    assign msg_out_d[i] = key_in[i] ^ nonce_in[i] ^ data_in[i];
    assign tag_out_d[i] = tag_in_q[i];
  end

  // Unused alert signals
  logic unused_alert_signals;
  assign unused_alert_signals = ^reg2hw.alert_test;

endmodule
