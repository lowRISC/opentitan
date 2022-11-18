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

  localparam string LC_CTRL_TRANS_SUCCESS_PATH =
    "tb.dut.top_earlgrey.u_lc_ctrl.u_lc_ctrl_fsm.trans_success_o";

  rand bit [7:0] rma_unlock_token[TokenWidthByte];

  rand bit [7:0] creator_root_key0[KeyWidthByte];
  rand bit [7:0] creator_root_key1[KeyWidthByte];

  virtual function bit [KeyWidthBit-1:0] get_otp_key(bit [7:0] key_in[KeyWidthByte]);
    bit [kmac_pkg::AppDigestW-1:0] digest_bits;
    bit [7:0] dpi_digest[kmac_pkg::AppDigestW/8];

    digestpp_dpi_pkg::c_dpi_cshake128(key_in, "", "LC_CTRL", KeyWidthByte, kmac_pkg::AppDigestW / 8,
                                      dpi_digest);

    digest_bits = {<<byte{dpi_digest}};
    return (digest_bits[KeyWidthBit-1:0]);
  endfunction

  // When the RMA transition has been completed the CPU will be disabled
  // and therefore it cannot be detected in SW. Detect this transition here
  // to allow the CPU to be reset.
  virtual task wait_for_transition();
    int retval;
    int transition_success = 0;
    time rma_timeout_ns = 120_000_000; // 120ms
    retval = uvm_hdl_check_path(LC_CTRL_TRANS_SUCCESS_PATH);
    `DV_CHECK_EQ_FATAL(retval, 1, $sformatf(
                       "Hierarchical path %0s appears to be invalid.", LC_CTRL_TRANS_SUCCESS_PATH))
   `DV_SPINWAIT(while (transition_success == 0) begin
                  retval = uvm_hdl_read(LC_CTRL_TRANS_SUCCESS_PATH, transition_success);
                  `DV_CHECK_EQ(retval, 1, $sformatf("uvm_hdl_read failed for %0s", LC_CTRL_TRANS_SUCCESS_PATH))
                  cfg.clk_rst_vif.wait_clks(1);
                end,
                "timeout while wait for flash rma complete",
                rma_timeout_ns)
  endtask

  virtual function void write_test_phase(test_phases_e phase);
    bit [7:0] test_phase[1];
    test_phase[0] = phase;
    sw_symbol_backdoor_overwrite("kTestPhase", test_phase);
  endfunction

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init(reset_kind);
    // Override the LC partition to Dev state.
    cfg.mem_bkdr_util_h[Otp].otp_write_lc_partition_state(LcStDev);
  endtask

  virtual task cpu_init();
    super.cpu_init();
    sw_symbol_backdoor_overwrite("kLcRmaUnlockToken", rma_unlock_token, SwTypeRom);
  endtask

  virtual task body();
    // First Boot.
    super.body();
    write_test_phase(TestPhaseWriteData);

    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)
    write_test_phase(TestPhaseEnterRMA);
    apply_reset();

    // Second Boot.
    // Override the rma unlock token to match SW test's input token.
    cfg.mem_bkdr_util_h[Otp].otp_write_secret2_partition(
        .rma_unlock_token(dec_otp_token_from_lc_csrs(rma_unlock_token)),
        .creator_root_key0(get_otp_key(creator_root_key0)),
        .creator_root_key1(get_otp_key(creator_root_key1)));

    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInWfi)

    wait_for_transition();
    write_test_phase(TestPhaseCheckWipe);

    cfg.clk_rst_vif.wait_clks(1000);
    apply_reset();

    // Third Boot.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInTest)

  endtask

endclass
