// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class chip_sw_flash_rma_unlocked_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_flash_rma_unlocked_vseq)

  `uvm_object_new

  // LC sends two 64-bit msg as input token.
  localparam uint TokenWidthBit = kmac_pkg::MsgWidth * 2;
  localparam uint TokenWidthByte = TokenWidthBit / 8;
  localparam uint KeyWidthBit = otp_ctrl_reg_pkg::CreatorRootKeyShare0Size * 8;
  localparam uint KeyWidthByte = KeyWidthBit / 8;

  typedef enum bit [7:0] {
    TestPhaseWriteData = 0,
    TestPhaseEnterRMA = 1,
    TestPhaseCheckWipe = 2
  } test_phases_e;

  localparam string SILICON_CREATOR_ID_PATH = "tb.dut.top_earlgrey.LcCtrlSiliconCreatorId";
  localparam string PRODUCT_ID_PATH = "tb.dut.top_earlgrey.LcCtrlProductId";
  localparam string REVISION_ID_PATH = "tb.dut.top_earlgrey.LcCtrlRevisionId";

  localparam string LC_CTRL_TRANS_SUCCESS_PATH =
    "tb.dut.top_earlgrey.u_lc_ctrl.u_lc_ctrl_fsm.trans_success_o";

  bit [15:0] silicon_creator_id = 16'h 0000;
  bit [15:0] product_id = 16'h 0000;
  bit [7:0] revision_id = 16'h 0000;

  bit [TokenWidthByte*8-1:0] rma_unlock_token_vector;
  rand bit [7:0] rma_unlock_token[TokenWidthByte];
  rand bit [7:0] creator_root_key0[KeyWidthByte];
  rand bit [7:0] creator_root_key1[KeyWidthByte];

  rand bit [lc_ctrl_reg_pkg::NumDeviceIdWords*BUS_DW-1:0] device_id;
  rand bit [lc_ctrl_reg_pkg::NumManufStateWords*BUS_DW-1:0] manuf_state;

  lc_ctrl_state_pkg::dec_lc_state_e src_lc_state;

  virtual function bit [KeyWidthBit-1:0] get_otp_key(bit [7:0] key_in[KeyWidthByte]);
    bit [kmac_pkg::AppDigestW-1:0] digest_bits;
    bit [7:0] dpi_digest[kmac_pkg::AppDigestW/8];

    digestpp_dpi_pkg::c_dpi_cshake128(key_in, "", "LC_CTRL", KeyWidthByte, kmac_pkg::AppDigestW / 8,
                                      dpi_digest);

    digest_bits = {<<byte{dpi_digest}};
    return (digest_bits[KeyWidthBit-1:0]);
  endfunction

  virtual function void write_test_phase(test_phases_e phase);
    bit [7:0] test_phase[1];
    test_phase[0] = phase;
    sw_symbol_backdoor_overwrite("kTestPhase", test_phase, SwTypeRom);
  endfunction

  virtual task dut_init(string reset_kind = "HARD");
    int retval;
    super.dut_init(reset_kind);

    // Flip a coin and either select Dev or Prod to start and override the state in OTP.
    if ($urandom_range(0, 1)) src_lc_state = DecLcStDev;
    else                      src_lc_state = DecLcStProd;
    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(encode_lc_state(src_lc_state));

    // Override Device ID and Manufacturing state with random values.
    cfg.mem_bkdr_util_h[Otp].otp_write_hw_cfg_partition(
      .device_id(device_id),
      .manuf_state(manuf_state),
      // Use same default config as in otp_ctrl_img_hw_cfg.hjson
      .en_sram_ifetch(prim_mubi_pkg::MuBi8False),
      .en_csrng_sw_app_read(prim_mubi_pkg::MuBi8True),
      .en_entropy_src_fw_read(prim_mubi_pkg::MuBi8True),
      .en_entropy_src_fw_over(prim_mubi_pkg::MuBi8True));

    // Read current chip revision and generation parameter values.
    retval = uvm_hdl_read(SILICON_CREATOR_ID_PATH, silicon_creator_id);
    `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", SILICON_CREATOR_ID_PATH))
    retval = uvm_hdl_read(PRODUCT_ID_PATH, product_id);
    `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", PRODUCT_ID_PATH))
    retval = uvm_hdl_read(REVISION_ID_PATH, revision_id);
    `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", REVISION_ID_PATH))
  endtask

  virtual task pre_start();
    cfg.chip_vif.tap_straps_if.drive(JtagTapLc);
    super.pre_start();
  endtask

  virtual task cpu_init();
    bit [7:0] state[1] = {8'(src_lc_state)};
    super.cpu_init();
    // Let SW know which lc state we picked.
    sw_symbol_backdoor_overwrite("kSrcLcState", state, SwTypeRom);
    if (cfg.en_small_rma) begin
      bit [7:0] en_short_rma[1];
      en_short_rma[0] = 1;
      sw_symbol_backdoor_overwrite("kShortRma", en_short_rma, SwTypeRom);
    end
  endtask

  virtual task check_lc_state(dec_lc_state_e exp_state);
    bit [BUS_DW-1:0] state;
    // acquire access for JTAG to LC CTRL
    wait_lc_initialized(.allow_err(1));
    // check LC state is correct
    jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl.lc_state.get_offset(),
                                        p_sequencer.jtag_sequencer_h, state);
    `DV_CHECK_EQ(state, {DecLcStateNumRep{exp_state}})
  endtask

  // Reads info registers in the LC controller via JTAG and checks whether they are correct.
  virtual task check_lc_info_regs();
    bit [BUS_DW-1:0] word;
    // acquire access for JTAG to LC CTRL
    wait_lc_initialized(.allow_err(1));

    // Check Revision
    jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl.hw_revision0.get_offset(),
                                        p_sequencer.jtag_sequencer_h, word);
    `DV_CHECK_EQ(word, {silicon_creator_id, product_id})
    jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl.hw_revision1.get_offset(),
                                        p_sequencer.jtag_sequencer_h, word);
    `DV_CHECK_EQ(word, {revision_id})

    // Check Device ID
    for (int k = 0; k < lc_ctrl_reg_pkg::NumDeviceIdWords; k++) begin
      jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl.device_id[k].get_offset(),
                                          p_sequencer.jtag_sequencer_h, word);
      `DV_CHECK_EQ(word, device_id[k*BUS_DW +: BUS_DW])
    end

    // Check Manuf State
    for (int k = 0; k < lc_ctrl_reg_pkg::NumManufStateWords; k++) begin
      jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl.manuf_state[k].get_offset(),
                                          p_sequencer.jtag_sequencer_h, word);
      `DV_CHECK_EQ(word, manuf_state[k*BUS_DW +: BUS_DW])
    end
  endtask

  virtual task provision_secret2_partition();
    // Override the rma unlock token to match SW test's input token.
    cfg.mem_bkdr_util_h[Otp].otp_write_secret2_partition(
        .rma_unlock_token(dec_otp_token_from_lc_csrs(rma_unlock_token)),
        .creator_root_key0(get_otp_key(creator_root_key0)),
        .creator_root_key1(get_otp_key(creator_root_key1)));
    // Convert to right format for jtag_lc_state_transition function below.
    rma_unlock_token_vector = {<< byte {rma_unlock_token}};
  endtask

  virtual task body();
    super.body();
    write_test_phase(TestPhaseWriteData);

    // First Boot.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)
    check_lc_state(src_lc_state);
    check_lc_info_regs();
    provision_secret2_partition();
    write_test_phase(TestPhaseEnterRMA);
    apply_reset();

    // Second Boot.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)
    check_lc_state(src_lc_state);
    check_lc_info_regs();
    // This function waits until the transition has successfully ended.
    jtag_lc_state_transition(src_lc_state, DecLcStRma, rma_unlock_token_vector);
    write_test_phase(TestPhaseCheckWipe);
    apply_reset();

    // Third Boot.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    check_lc_state(DecLcStRma);
    check_lc_info_regs();
  endtask

endclass
