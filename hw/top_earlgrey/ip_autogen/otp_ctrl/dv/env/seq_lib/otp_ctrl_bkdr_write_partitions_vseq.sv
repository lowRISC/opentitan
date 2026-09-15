// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This sequence provisions every buffered partition through the otp_ctrl_mem_bkdr_util_pkg
// helpers that top-level environments use to preload OTP, then triggers OTP initialization and
// checks that the hardware accepts the backdoor-written contents and digests.
//
// The scoreboard is disabled because the backdoor writes bypass its memory model; all checks are
// done within this sequence.
class otp_ctrl_bkdr_write_partitions_vseq extends otp_ctrl_base_vseq;
  `uvm_object_utils(otp_ctrl_bkdr_write_partitions_vseq)

  `uvm_object_new

  virtual task pre_start();
    // OTP initialization is triggered from body() so that the wait for it is bounded.
    do_otp_pwr_init = 0;
    super.pre_start();
  endtask

  // Backdoor write random contents and the matching digest into every buffered partition once
  // the OTP array has been cleared.
  virtual task otp_ctrl_init();
    bit [DeviceIdSize*8-1:0] device_id;
    bit [ManufStateSize*8-1:0] manuf_state;
    bit [EnSramIfetchSize*8-1:0] en_sram_ifetch;
    bit [EnCsrngSwAppReadSize*8-1:0] en_csrng_sw_app_read;
    bit [DisRvDmLateDebugSize*8-1:0] dis_rv_dm_late_debug;
    bit [TestUnlockTokenSize*8-1:0] test_unlock_token;
    bit [TestExitTokenSize*8-1:0] test_exit_token;
    bit [NvmAddrKeySeedSize*8-1:0] nvm_addr_key_seed;
    bit [NvmDataKeySeedSize*8-1:0] nvm_data_key_seed;
    bit [SramDataKeySeedSize*8-1:0] sram_data_key_seed;
    bit [RmaTokenSize*8-1:0] rma_token;
    bit [CreatorRootKeyShare0Size*8-1:0] creator_root_key_share0;
    bit [CreatorRootKeyShare1Size*8-1:0] creator_root_key_share1;

    super.otp_ctrl_init();

    `DV_CHECK_STD_RANDOMIZE_FATAL(device_id)
    `DV_CHECK_STD_RANDOMIZE_FATAL(manuf_state)
    otp_ctrl_mem_bkdr_util_pkg::otp_write_hw_cfg0_partition(
        .mem_bkdr_util_h(cfg.mem_bkdr_util_h),
        .device_id(device_id),
        .manuf_state(manuf_state)
    );

    `DV_CHECK_STD_RANDOMIZE_FATAL(en_sram_ifetch)
    `DV_CHECK_STD_RANDOMIZE_FATAL(en_csrng_sw_app_read)
    `DV_CHECK_STD_RANDOMIZE_FATAL(dis_rv_dm_late_debug)
    otp_ctrl_mem_bkdr_util_pkg::otp_write_hw_cfg1_partition(
        .mem_bkdr_util_h(cfg.mem_bkdr_util_h),
        .en_sram_ifetch(en_sram_ifetch),
        .en_csrng_sw_app_read(en_csrng_sw_app_read),
        .dis_rv_dm_late_debug(dis_rv_dm_late_debug)
    );

    `DV_CHECK_STD_RANDOMIZE_FATAL(test_unlock_token)
    `DV_CHECK_STD_RANDOMIZE_FATAL(test_exit_token)
    otp_ctrl_mem_bkdr_util_pkg::otp_write_secret0_partition(
        .mem_bkdr_util_h(cfg.mem_bkdr_util_h),
        .test_unlock_token(test_unlock_token),
        .test_exit_token(test_exit_token)
    );

    `DV_CHECK_STD_RANDOMIZE_FATAL(nvm_addr_key_seed)
    `DV_CHECK_STD_RANDOMIZE_FATAL(nvm_data_key_seed)
    `DV_CHECK_STD_RANDOMIZE_FATAL(sram_data_key_seed)
    otp_ctrl_mem_bkdr_util_pkg::otp_write_secret1_partition(
        .mem_bkdr_util_h(cfg.mem_bkdr_util_h),
        .nvm_addr_key_seed(nvm_addr_key_seed),
        .nvm_data_key_seed(nvm_data_key_seed),
        .sram_data_key_seed(sram_data_key_seed)
    );

    `DV_CHECK_STD_RANDOMIZE_FATAL(rma_token)
    `DV_CHECK_STD_RANDOMIZE_FATAL(creator_root_key_share0)
    `DV_CHECK_STD_RANDOMIZE_FATAL(creator_root_key_share1)
    otp_ctrl_mem_bkdr_util_pkg::otp_write_secret2_partition(
        .mem_bkdr_util_h(cfg.mem_bkdr_util_h),
        .rma_token(rma_token),
        .creator_root_key_share0(creator_root_key_share0),
        .creator_root_key_share1(creator_root_key_share1)
    );
  endtask

  task body();
    bit [63:0] digest;

    // The hardware loads every buffered partition and checks its digest during initialization.
    // A failed check is fatal: every partition enters its error state and init done still
    // asserts, so a bad digest shows up in the error status read below.
    cfg.otp_ctrl_vif.drive_pwr_otp_init(1);
    `DV_WAIT(cfg.otp_ctrl_vif.pwr_otp_done_o == 1, "OTP initialization did not complete")
    cfg.otp_ctrl_vif.drive_pwr_otp_init(0);

    csr_rd_check(.ptr(ral.status.partition_error), .compare_value(0));
    csr_rd_check(.ptr(ral.partition_status_0.hw_cfg0_error), .compare_value(0));
    csr_rd_check(.ptr(ral.partition_status_0.hw_cfg1_error), .compare_value(0));
    csr_rd_check(.ptr(ral.partition_status_0.secret0_error), .compare_value(0));
    csr_rd_check(.ptr(ral.partition_status_0.secret1_error), .compare_value(0));
    csr_rd_check(.ptr(ral.partition_status_0.secret2_error), .compare_value(0));

    // The digest CSRs must expose the backdoor-written digests. A zero digest would pass unchecked,
    // since the hardware skips the integrity check of a blank digest.
    digest = cfg.mem_bkdr_util_h.read64(HwCfg0DigestOffset);
    `DV_CHECK_NE(digest, 0)
    csr_rd_check(.ptr(ral.hw_cfg0_digest[0]), .compare_value(digest[31:0]));
    csr_rd_check(.ptr(ral.hw_cfg0_digest[1]), .compare_value(digest[63:32]));
    digest = cfg.mem_bkdr_util_h.read64(HwCfg1DigestOffset);
    `DV_CHECK_NE(digest, 0)
    csr_rd_check(.ptr(ral.hw_cfg1_digest[0]), .compare_value(digest[31:0]));
    csr_rd_check(.ptr(ral.hw_cfg1_digest[1]), .compare_value(digest[63:32]));
    digest = cfg.mem_bkdr_util_h.read64(Secret0DigestOffset);
    `DV_CHECK_NE(digest, 0)
    csr_rd_check(.ptr(ral.secret0_digest[0]), .compare_value(digest[31:0]));
    csr_rd_check(.ptr(ral.secret0_digest[1]), .compare_value(digest[63:32]));
    digest = cfg.mem_bkdr_util_h.read64(Secret1DigestOffset);
    `DV_CHECK_NE(digest, 0)
    csr_rd_check(.ptr(ral.secret1_digest[0]), .compare_value(digest[31:0]));
    csr_rd_check(.ptr(ral.secret1_digest[1]), .compare_value(digest[63:32]));
    digest = cfg.mem_bkdr_util_h.read64(Secret2DigestOffset);
    `DV_CHECK_NE(digest, 0)
    csr_rd_check(.ptr(ral.secret2_digest[0]), .compare_value(digest[31:0]));
    csr_rd_check(.ptr(ral.secret2_digest[1]), .compare_value(digest[63:32]));
  endtask : body

endclass : otp_ctrl_bkdr_write_partitions_vseq
