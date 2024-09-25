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

  // Input Errors for status register
  input logic error_recov_i,
  input logic error_fatal_i,

  // Key Manager
  input keymgr_pkg::hw_key_req_t keymgr_key_i,

  // Bus Interface
  input  ascon_reg2hw_t reg2hw,
  output ascon_hw2reg_t hw2reg,

  output prim_mubi_pkg::mubi4_t idle_o
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

  logic force_data_overwrite;
  logic manual_start_trigger;
  logic sideload_key;
  logic start, start_ok, wipe;
  logic masked_ad_input;
  logic masked_msg_input;

  logic [4:0] valid_bytes;

  prim_mubi_pkg::mubi4_t no_ad;
  prim_mubi_pkg::mubi4_t no_msg;

  data_type_in_e data_type_last;
  data_type_in_e data_type_start;

  prim_ascon_pkg::duplex_op_e      operation;
  prim_ascon_pkg::duplex_variant_e variant;

  logic [127:0]     msg_out;
  logic [3:0][31:0] msg_out_d;
  logic [3:0][31:0] msg_out_q;
  logic             msg_out_valid;
  logic             msg_out_we;
  logic [3:0][31:0] unused_msg_out_q;
  logic [3:0]       msg_out_read_d, msg_out_read_q;
  logic             msg_out_read;
  logic             msg_out_ready;

  logic [127:0]     tag_out;
  logic [3:0][31:0] tag_out_d;
  logic [3:0][31:0] tag_out_q;
  logic             tag_out_valid;
  logic             tag_out_we;
  logic [3:0][31:0] unused_tag_out_q;
  logic [3:0]       tag_out_read_d, tag_out_read_q;
  logic             tag_out_read;
  logic             tag_out_ready;


  prim_mubi_pkg::mubi4_t duplex_idle;
  assign idle_o = duplex_idle;

  logic duplex_done;

  logic ascon_error;

  logic duplex_fatal_error;
  assign alert_fatal_o = duplex_fatal_error;

  lc_ctrl_pkg::lc_tx_t      unused_lc_escalate_en_i;
  keymgr_pkg::hw_key_req_t  unused_keymgr_key_i;

  prim_mubi_pkg::mubi4_t tag_match;
  prim_mubi_pkg::mubi4_t tag_calculated;

  // TODO
  assign unused_keymgr_key_i     = keymgr_key_i;
  assign unused_lc_escalate_en_i = lc_escalate_en_i;

  // DATA REGISTERS

  for (genvar i = 0; i < NumRegsKey; i++) begin : gen_hw_ext_key_regs
    // Input conversion
    assign key_share0_in_d[i] = reg2hw.key_share0[i].q;
    assign key_share1_in_d[i] = reg2hw.key_share1[i].q;

    // hwext input key registers
    always_ff @(posedge clk_i or negedge rst_ni) begin : input_reg_key_share0
      if (!rst_ni) begin
        key_share0_in_q[i] <= '{default: '0};
      end else if (reg2hw.key_share0[i].qe) begin
        key_share0_in_q[i] <= key_share0_in_d[i];
      end
    end
    assign hw2reg.key_share0[i].d = '0;

    always_ff @(posedge clk_i or negedge rst_ni) begin : input_reg_key_share1
      if (!rst_ni) begin
        key_share1_in_q[i] <= '{default: '0};
      end else if (reg2hw.key_share1[i].qe) begin
        key_share1_in_q[i] <= key_share1_in_d[i];
      end
    end
    assign hw2reg.key_share1[i].d = '0;
  end

  for (genvar i = 0; i < NumRegsData; i++) begin : gen_hw_ext_data_regs
    // Input conversion
    assign data_share0_in_d[i] = reg2hw.data_in_share0[i].q;
    assign data_share1_in_d[i] = reg2hw.data_in_share1[i].q;

    // hwext input data registers
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

  for (genvar i = 0; i < NumRegsNonce; i++) begin : gen_hw_ext_nonce_regs
    // Input conversion
    assign nonce_share0_in_d[i] = reg2hw.nonce_share0[i].q;
    assign nonce_share1_in_d[i] = reg2hw.nonce_share1[i].q;

    // hwext input nonce registers
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
  end


  // hwext output registers
  for (genvar i = 0; i < NumRegsData; i++) begin : gen_hw_ext_data_output_regs
    always_ff @(posedge clk_i or negedge rst_ni) begin : reg_msg_out
      if (!rst_ni) begin
        msg_out_q[i] <= '{default: '0};
      end else if (msg_out_we) begin
        msg_out_q[i] <= msg_out_d[i];
      end
    end
    assign unused_msg_out_q[i] = reg2hw.msg_out[i].q;
    // Output conversion
    assign hw2reg.msg_out[i].d = msg_out_q[i];
  end

  for (genvar i = 0; i < NumRegsTag; i++) begin : gen_hw_ext_tag_output_regs
    always_ff @(posedge clk_i or negedge rst_ni) begin : reg_tag_out
      if (!rst_ni) begin
        tag_out_q[i] <= '{default: '0};
      end else if (tag_out_we) begin
        tag_out_q[i] <= tag_out_d[i];
      end
    end
    assign unused_tag_out_q[i] = reg2hw.tag_out[i].q;
    // Output conversion
    assign hw2reg.tag_out[i].d = tag_out_q[i];
  end


  // CTRL
  assign operation            = reg2hw.ctrl_shadowed.operation.q;
  assign variant              = reg2hw.ctrl_shadowed.ascon_variant.q;
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

  logic no_msg_mubi4invalid;
  logic no_ad_mubi4invalid;

  always_comb begin : sanitize_mubi_reg
  // Sanitize values written by SW
  // TODO: This should be added to the register_top/reggen-tool, as it would
  //       be better to sanitize the values before they are written to the register.
    if(prim_mubi_pkg::mubi4_test_invalid(reg2hw.ctrl_shadowed.no_ad.q)) begin
      no_ad_mubi4invalid = 1'b1;
      no_ad              = prim_mubi_pkg::MuBi4False;
    end else begin
      no_ad_mubi4invalid = 1'b0;
      no_ad              = reg2hw.ctrl_shadowed.no_ad.q;
    end

    if(prim_mubi_pkg::mubi4_test_invalid(reg2hw.ctrl_shadowed.no_msg.q)) begin
      no_msg_mubi4invalid = 1'b1;
      no_msg              = prim_mubi_pkg::MuBi4True;
    end else begin
      no_msg_mubi4invalid = 1'b0;
      no_msg              = reg2hw.ctrl_shadowed.no_msg.q;
    end
  end

  assign alert_recov_o = no_ad_mubi4invalid | no_msg_mubi4invalid;

  // TRIGGER
  assign start                = reg2hw.trigger.start.q;
  assign wipe                 = reg2hw.trigger.wipe.q;


  // TODO Trigger feedback
  assign hw2reg.trigger.start.d  = 1'b0;
  assign hw2reg.trigger.start.de = 1'b1;

  assign hw2reg.trigger.wipe.d  = 1'b0;
  assign hw2reg.trigger.wipe.de = 1'b1;

  // STATUS
  assign hw2reg.status.idle.d  = prim_mubi_pkg::mubi4_test_true_strict(duplex_idle);
  assign hw2reg.status.idle.de = 1'b1;
  assign hw2reg.status.ascon_error.d  = ascon_error;
  assign hw2reg.status.ascon_error.de = 1'b1;
  assign hw2reg.status.alert_recov_ctrl_update_err.d  = error_recov_i;
  assign hw2reg.status.alert_recov_ctrl_update_err.de = 1'b1;
  assign hw2reg.status.alert_fatal_fault.d  = error_fatal_i;
  assign hw2reg.status.alert_fatal_fault.de = 1'b1;
  // TODO STATUS
  assign hw2reg.status.stall.d  = 1'b0;
  assign hw2reg.status.stall.de = 1'b1;
  assign hw2reg.status.wait_edn.d  = 1'b0;
  assign hw2reg.status.wait_edn.de = 1'b1;

  logic  data_in_valid;
  assign data_in_valid = data_share1_in_new & data_share0_in_new;

  logic  data_in_ready;
  logic  data_in_read;
  assign data_in_read = data_in_ready & data_in_valid;
  assign data_share1_in_load = data_in_read;
  assign data_share0_in_load = data_in_read;

  logic msg_out_reg_valid;
  logic tag_out_reg_valid;

  always_ff @(posedge clk_i or negedge rst_ni) begin : track_output_status
    if (!rst_ni) begin
      msg_out_reg_valid <= 1'b0;
      tag_out_reg_valid <= 1'b0;
    end else begin
      // The output msg (PT or CT) is valid if it has been written to output register
      // This output stays valid until a new input (CT or PT) has been read from the
      // input register
      if (msg_out_we) begin
        msg_out_reg_valid <= 1'b1;
      end else if (data_in_read) begin
        msg_out_reg_valid <= 1'b0;
      end
      // The same logic applies for the tag.
      // TODO: reconsider the clear logic. Als take the tag_comparison into account
      if (tag_out_we) begin
        tag_out_reg_valid <= 1'b1;
      end else if (tag_out_read) begin
        tag_out_reg_valid <= 1'b0;
      end
    end
  end

  // TODO: directly assign hw2reg.output_valid.msg_valid and hw2reg.output_valid.tag_valid.d
  //       in the track_output_status process above.
  assign hw2reg.output_valid.msg_valid.d  = msg_out_reg_valid;
  assign hw2reg.output_valid.msg_valid.de = 1'b1;

  assign hw2reg.output_valid.tag_valid.d  = tag_out_reg_valid;
  assign hw2reg.output_valid.tag_valid.de = 1'b1;

  // FSM_STATE Debug Output
  prim_ascon_pkg::duplex_fsm_state_e duplex_fsm_state;
  assign hw2reg.fsm_state.d  = {{(32-prim_ascon_pkg::AsconDuplexFSMStateWidth){1'b0}},
                                duplex_fsm_state};

  logic [31:0] unused_fsm_state_q;
  logic        unused_fsm_state_qe;
  assign unused_fsm_state_q  = reg2hw.fsm_state.q;
  assign unused_fsm_state_qe = reg2hw.fsm_state.qe;

  // DETECTION LOGIC
  // Detect new key, new input, output read
  // Edge detectors are cleared by the FSM
  assign key_share0_in_new_d = key_share0_in_load ? '0 : key_share0_in_new_q |
      {reg2hw.key_share0[3].qe, reg2hw.key_share0[2].qe,
       reg2hw.key_share0[1].qe, reg2hw.key_share0[0].qe};
  assign key_share0_in_new = &key_share0_in_new_q;

  assign key_share1_in_new_d = key_share1_in_load ? '0 : key_share1_in_new_q |
      {reg2hw.key_share1[3].qe, reg2hw.key_share1[2].qe,
       reg2hw.key_share1[1].qe, reg2hw.key_share1[0].qe};
  assign key_share1_in_new = &key_share1_in_new_q;

  assign nonce_share0_in_new_d = nonce_share0_in_load ? '0 : nonce_share0_in_new_q |
      {reg2hw.nonce_share0[3].qe, reg2hw.nonce_share0[2].qe,
       reg2hw.nonce_share0[1].qe, reg2hw.nonce_share0[0].qe};
  assign nonce_share0_in_new = &nonce_share0_in_new_q;

  assign nonce_share1_in_new_d = nonce_share1_in_load ? '0 : nonce_share1_in_new_q |
      {reg2hw.nonce_share1[3].qe, reg2hw.nonce_share1[2].qe,
       reg2hw.nonce_share1[1].qe, reg2hw.nonce_share1[0].qe};
  assign nonce_share1_in_new = &nonce_share1_in_new_q;

  assign data_share0_in_new_d = data_share0_in_load ? '0 : data_share0_in_new_q |
      {reg2hw.data_in_share0[3].qe, reg2hw.data_in_share0[2].qe,
       reg2hw.data_in_share0[1].qe, reg2hw.data_in_share0[0].qe};
  assign data_share0_in_new = &data_share0_in_new_q;

  assign data_share1_in_new_d = data_share1_in_load ? '0 : data_share1_in_new_q |
      {reg2hw.data_in_share1[3].qe, reg2hw.data_in_share1[2].qe,
       reg2hw.data_in_share1[1].qe, reg2hw.data_in_share1[0].qe};
  assign data_share1_in_new = &data_share1_in_new_q;

  assign tag_in_new_d = tag_in_load ? '0 : tag_in_new_q |
      {reg2hw.tag_in[3].qe, reg2hw.tag_in[2].qe, reg2hw.tag_in[1].qe, reg2hw.tag_in[0].qe};
  assign tag_in_new = &tag_in_new_d;

  assign msg_out_read_d = msg_out_we ? '0 : msg_out_read_q |
      {reg2hw.msg_out[3].re, reg2hw.msg_out[2].re, reg2hw.msg_out[1].re, reg2hw.msg_out[0].re};
  assign msg_out_read = &msg_out_read_q;

  assign tag_out_read_d = tag_out_we ? '0 : tag_out_read_q |
      {reg2hw.tag_out[3].re, reg2hw.tag_out[2].re, reg2hw.tag_out[1].re, reg2hw.tag_out[0].re};
  assign tag_out_read = &tag_out_read_q;

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

  // ERROR
  logic key_error, nonce_error;
  logic no_new_key, no_new_nonce;
  assign no_new_key   = !(key_share0_in_new & key_share1_in_new);
  assign key_error    = no_new_key;
  assign no_new_nonce = !(nonce_share0_in_new & nonce_share1_in_new);
  assign nonce_error  = no_new_nonce;

  // only start if nonce and key are set
  assign start_ok = start & !(key_error | nonce_error);

  // TODO: This implementations forces a new key write for each AEAD
  //       This can be relaxed.
  assign key_share0_in_load = start_ok;
  assign key_share1_in_load = start_ok;
  assign nonce_share0_in_load = start_ok;
  assign nonce_share1_in_load = start_ok;
    // otherwise set error
  assign hw2reg.error.no_key.d  = key_error;
  assign hw2reg.error.no_key.de = start;
  assign hw2reg.error.no_nonce.d  = nonce_error;
  assign hw2reg.error.no_nonce.de = start;

  // detect error during operation
  logic flag_error;

  // the no_ad or no_msg flag was set, but there is ad or msg
  assign flag_error = (prim_mubi_pkg::mubi4_test_true_strict(no_ad) &&
                      ((data_type_start == AD_IN) || (data_type_last == AD_IN))) ||
                      (prim_mubi_pkg::mubi4_test_true_strict(no_msg) &&
                      ((data_type_start == MSG_IN) || (data_type_last == MSG_IN)));
  assign hw2reg.error.flag_input_missmatch.d  = flag_error;
  assign hw2reg.error.flag_input_missmatch.de = prim_mubi_pkg::mubi4_test_false_strict(
                                                  duplex_idle);

  // AD was provided after MSG
  logic order_error;
  logic msg_received_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_track_msg
    if (!rst_ni) begin
      msg_received_q <= 1'b0;
    end else if (duplex_done) begin
      msg_received_q <= 1'b0;
    end else if ((data_type_start == MSG_IN) || (data_type_last == MSG_IN)) begin
      msg_received_q <= 1'b1;
    end
  end

  assign order_error = msg_received_q & ((data_type_start == AD_IN) || (data_type_last == AD_IN));
  assign hw2reg.error.wrong_order.d  = order_error;
  assign hw2reg.error.wrong_order.de = prim_mubi_pkg::mubi4_test_false_strict(duplex_idle);

  assign ascon_error = key_error | nonce_error | flag_error | order_error;

  // Generate a ready signal from a read signal:
  // ready and read share mostly the same logic: A register is ready to receive new data, after
  // it has been read (logical 1'b1). A write to the register resets both the read and the ready
  // status. The difference between ready and read is the initial reset: a read register is cleared
  // to 1'b0 after reset (as it hasn't been read). A ready register must be set to 1'b1 after
  // reset, as it is ready to receive data. Therefore, we need to track the initial reset status.

  // Two different signals are needed, as the signal to the core should be called ready (as part
  // of a ready-valid-handshaking, but the register tracking the reads from SW should be read.

  logic track_reset_msg_q;
  logic track_reset_tag_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin : reg_track_reset
    if (!rst_ni) begin
      track_reset_msg_q <= 1'b1;
      track_reset_tag_q <= 1'b1;
    end else begin
      if (msg_out_we) begin
        track_reset_msg_q <= 1'b0;
      end
      if (tag_out_we) begin
        track_reset_tag_q <= 1'b0;
      end
    end
  end

  assign msg_out_ready = msg_out_read | track_reset_msg_q;
  // only write to the data out register if there is valid data and
  // the register is ready (has been read)
  assign msg_out_we = msg_out_valid & msg_out_ready;

  assign tag_out_ready = tag_out_read | track_reset_tag_q;
  // atm there is no backpreassure logic inside the duplex module for the tag register, as
  // it is assumed that a new run is only started after the previous run has been completed.
  // Nevertheless, we need the not tag_out_ready signal for the tag comparision.
  assign tag_out_we = tag_out_valid & tag_out_ready;


  // Tag comparison
  for (genvar i = 0; i < NumRegsTag; i++) begin : gen_tag_in_conversion
    assign tag_in_q[i] = reg2hw.tag_in[i].q;
  end
  assign tag_match = (tag_in_q == tag_out_q) ? prim_mubi_pkg::MuBi4True :
                                               prim_mubi_pkg::MuBi4False;

  // There is a valid tag comparision if there is
  // 1) a (new) tag in the input register
  // 2) a (new) tag in the output register. This equivalent to the output register not being
  //    ready. The output register is not ready, if there is a tag in the register.
  assign tag_calculated = (tag_in_new && !tag_out_ready) ? prim_mubi_pkg::MuBi4True :
                                                           prim_mubi_pkg::MuBi4False;

  always_comb begin : tag_recoding
    // Indicates if the tag could be successfully compared 2'b01, or not 2'b10
    // 2'b00 indicates that the tag hasn't been calculated, yet
    // 2'b11 is invalid.
    if (prim_mubi_pkg::mubi4_test_true_strict(tag_calculated)) begin
      if (prim_mubi_pkg::mubi4_test_true_strict(tag_match)) begin
        hw2reg.output_valid.tag_comparison_valid.d  = 2'b01;
      end else begin
        hw2reg.output_valid.tag_comparison_valid.d  = 2'b10;
      end
    end else begin
      hw2reg.output_valid.tag_comparison_valid.d  = 2'b00;
    end
  end

  assign hw2reg.output_valid.tag_comparison_valid.de = 1'b1;

  // Mark the input tag as invalid/used, if the output tag is read.
  // This also invalidates the tag_calculated.
  // If the tag ist not read, the start of a new AEAD-Enc/Dec also clears the flag.
  assign tag_in_load = tag_out_read | start_ok;

  // TODO: Build a very basic FSM here

  // TODO: We don't use any control signals
  logic        unused_force_data_overwrite;
  logic        unused_manual_start_trigger;
  logic        unused_wipe;
  logic        unused_masked_msg_input;
  logic        unused_masked_ad_input;
  logic        unused_sideload_key;

  assign unused_force_data_overwrite = force_data_overwrite;
  assign unused_manual_start_trigger = manual_start_trigger;
  assign unused_wipe                 = wipe;
  assign unused_masked_ad_input      = masked_ad_input;
  assign unused_masked_msg_input     = masked_msg_input;
  assign unused_sideload_key         = sideload_key;


  // XOR shares for unprotected implementation
  logic [3:0][31:0] key_in;
  logic [3:0][31:0] data_in;
  logic [3:0][31:0] nonce_in;
  for (genvar i = 0; i < 4; i++) begin : gen_combine_shares
    assign nonce_in[i] = nonce_share0_in_q[i] ^ nonce_share1_in_q[i];
    assign key_in[i] = key_share0_in_q[i] ^ key_share1_in_q[i];
    assign data_in[i] = data_share0_in_q[i] ^ data_share1_in_q[i];
  end

  prim_mubi_pkg::mubi4_t last_ad_block;
  prim_mubi_pkg::mubi4_t last_msg_block;

  assign last_ad_block  = (data_type_last ==  AD_IN) ? prim_mubi_pkg::MuBi4True :
                                                       prim_mubi_pkg::MuBi4False;
  assign last_msg_block = (data_type_last == MSG_IN) ? prim_mubi_pkg::MuBi4True :
                                                       prim_mubi_pkg::MuBi4False;

  assign msg_out_d = swap_endianess_byte(msg_out);
  assign tag_out_d = swap_endianess_byte(tag_out);

  // Instantiate Ascon Duplex
  prim_ascon_duplex ascon_duplex (

    .clk_i(clk_i),
    .rst_ni(rst_ni),

    .ascon_variant(variant),
    .ascon_operation(operation),

    .start_i(start_ok),
    .done_o(duplex_done),
    .idle_o(duplex_idle),

    // It is assumed that no_ad, no_msg, key, and nonce are always
    // valid and constant, when the cipher is triggered by the start command
    .no_ad_i(no_ad),
    .no_msg_i(no_msg),

    .key_i(swap_endianess_byte(key_in)),
    .nonce_i(swap_endianess_byte(nonce_in)),

    // Cipher Input Port
    .data_in_i(swap_endianess_byte(data_in)),
    .data_in_valid_bytes_i(valid_bytes),
    .last_block_ad_i(last_ad_block),
    .last_block_msg_i(last_msg_block),
    .data_in_valid_i(data_in_valid),
    .data_in_ready_o(data_in_ready),

    // Cipher Output Port
    .data_out_o(msg_out),
    .data_out_ready_i(msg_out_ready),
    .data_out_valid_o(msg_out_valid),

    .tag_out_o(tag_out),
    .tag_out_valid_o(tag_out_valid),

    .fsm_state_o(duplex_fsm_state),
    .err_o(duplex_fatal_error)
  );

  // Unused alert signals. They are read in the toplevel!
  logic unused_alert_signals;
  assign unused_alert_signals = ^reg2hw.alert_test;

endmodule
