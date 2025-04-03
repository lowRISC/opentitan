// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This package has functions that perform mem_bkdr_util accesses to different partitions in OTP.
// These functions end up performing reads and writes to the underlying simulated otp memory, so
// the functions must get a handle to the mem_bkdr_util instance for otp_ctrl as an argument.
//
// NB: this package is only suitable for top-level environments since it depends on SKU-dependent
// OTP ctrl fields.

package otp_ctrl_mem_bkdr_util_pkg;

  import otp_ctrl_part_pkg::*;
  import otp_ctrl_reg_pkg::*;
  import otp_scrambler_pkg::*;

  function automatic void otp_write_lc_partition_state(
      mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h,
      lc_ctrl_state_pkg::lc_state_e lc_state
  );
    for (int i = 0; i < LcStateSize; i += 4) begin
      mem_bkdr_util_h.write32(i + LcStateOffset, lc_state[i*8+:32]);
    end
  endfunction : otp_write_lc_partition_state

  function automatic lc_ctrl_state_pkg::lc_state_e otp_read_lc_partition_state(
      mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h
  );
    lc_ctrl_state_pkg::lc_state_e lc_state;
    for (int i = 0; i < LcStateSize; i += 4) begin
      lc_state[i*8 +: 32] = mem_bkdr_util_h.read32(i + LcStateOffset);
    end

    return lc_state;
  endfunction : otp_read_lc_partition_state

  function automatic void otp_write_lc_partition_cnt(
      mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h,
      lc_ctrl_state_pkg::lc_cnt_e lc_cnt
  );
    for (int i = 0; i < LcTransitionCntSize; i += 4) begin
      mem_bkdr_util_h.write32(i + LcTransitionCntOffset, lc_cnt[i*8+:32]);
    end
  endfunction : otp_write_lc_partition_cnt

  function automatic void otp_write_lc_partition(mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h,
                                                 lc_ctrl_state_pkg::lc_cnt_e lc_cnt,
                                                 lc_ctrl_state_pkg::lc_state_e lc_state);

    otp_write_lc_partition_cnt(mem_bkdr_util_h, lc_cnt);
    otp_write_lc_partition_state(mem_bkdr_util_h, lc_state);
  endfunction : otp_write_lc_partition

  // The following steps are needed to backdoor write a non-secret partition:
  // 1). Backdoor write the input data to OTP memory.
  // 2). Calculate the correct digest for the secret partition.
  // 3). Backdoor write digest data to OTP memory.

  // The following steps are needed to backdoor write a secret partition:
  // 1). Scramble the RAW input data.
  // 2). Backdoor write the scrambled input data to OTP memory.
  // 3). Calculate the correct digest for the secret partition.
  // 4). Backdoor write digest data to OTP memory.

  // The HW_CFG1 partition needs to be a special case since it has items
  // smaller than 4 bytes and need to be concatenated. To make sure
  // this special case won't end up broken if the OTP layout changes
  // beyond what this supports the following checks are in place and
  // will cause a failure.
  // - No other partition except for HW_CFG1 has such small items.
  // - The small items in HW_CFG1 will be contained within 32 bits.

  function automatic void otp_write_hw_cfg0_partition(
      mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h,
      bit [DeviceIdSize*8-1:0] device_id,
      bit [ManufStateSize*8-1:0] manuf_state
  );
    bit [HwCfg0DigestSize*8-1:0] digest;
    bit [bus_params_pkg::BUS_DW-1:0] partition_data[$];

    for (int i = 0; i < DeviceIdSize; i += 4) begin
      mem_bkdr_util_h.write32(i + DeviceIdOffset, device_id[i*8+:32]);
    end
    for (int i = 0; i < ManufStateSize; i += 4) begin
      mem_bkdr_util_h.write32(i + ManufStateOffset, manuf_state[i*8+:32]);
    end

    partition_data = {<<32{
      manuf_state,
      device_id
    }};
    digest = cal_digest(HwCfg0Idx, partition_data);
    mem_bkdr_util_h.write64(HwCfg0DigestOffset, digest);
  endfunction

  function automatic void otp_write_hw_cfg1_partition(
      mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h,
      bit [SocDbgStateSize*8-1:0] soc_dbg_state,
      bit [EnCsrngSwAppReadSize*8-1:0] en_csrng_sw_app_read,
      bit [EnSramIfetchSize*8-1:0] en_sram_ifetch
  );
    bit [HwCfg1DigestSize*8-1:0] digest;
    bit [bus_params_pkg::BUS_DW-1:0] partition_data[$];
    bit [bus_params_pkg::BUS_DW-1:0] concat_data[$];
    bit [31:0] word;

    for (int i = 0; i < SocDbgStateSize; i += 4) begin
      mem_bkdr_util_h.write32(i + SocDbgStateOffset, soc_dbg_state[i*8+:32]);
      concat_data.push_front(soc_dbg_state[i*8+:32]);
    end
    word = {
      en_sram_ifetch,
      en_csrng_sw_app_read
    };
    mem_bkdr_util_h.write32(1 + EnCsrngSwAppReadOffset, word);
    concat_data.push_front(word);

    partition_data = {<<32{concat_data}};
    digest = cal_digest(HwCfg1Idx, partition_data);
    mem_bkdr_util_h.write64(HwCfg1DigestOffset, digest);
  endfunction

  function automatic void otp_write_secret0_partition(
      mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h,
      bit [TestUnlockTokenSize*8-1:0] test_unlock_token,
      bit [TestExitTokenSize*8-1:0] test_exit_token
  );
    bit [Secret0DigestSize*8-1:0] digest;
    bit [bus_params_pkg::BUS_DW-1:0] partition_data[$];
    bit [TestUnlockTokenSize*8-1:0] scrambled_test_unlock_token;
    bit [TestExitTokenSize*8-1:0] scrambled_test_exit_token;

    for (int i = 0; i < TestUnlockTokenSize; i += 8) begin
      scrambled_test_unlock_token[i*8+:64] = scramble_data(
          test_unlock_token[i*8+:64], Secret0Idx);
      mem_bkdr_util_h.write64(i + TestUnlockTokenOffset,
                              scrambled_test_unlock_token[i*8+:64]);
    end
    for (int i = 0; i < TestExitTokenSize; i += 8) begin
      scrambled_test_exit_token[i*8+:64] = scramble_data(
          test_exit_token[i*8+:64], Secret0Idx);
      mem_bkdr_util_h.write64(i + TestExitTokenOffset,
                              scrambled_test_exit_token[i*8+:64]);
    end

    partition_data = {<<32{
      scrambled_test_exit_token,
      scrambled_test_unlock_token
    }};
    digest = cal_digest(Secret0Idx, partition_data);
    mem_bkdr_util_h.write64(Secret0DigestOffset, digest);
  endfunction

  function automatic void otp_write_secret1_partition(
      mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h,
      bit [SramDataKeySeedSize*8-1:0] sram_data_key_seed
  );
    bit [Secret1DigestSize*8-1:0] digest;
    bit [bus_params_pkg::BUS_DW-1:0] partition_data[$];
    bit [SramDataKeySeedSize*8-1:0] scrambled_sram_data_key_seed;

    for (int i = 0; i < SramDataKeySeedSize; i += 8) begin
      scrambled_sram_data_key_seed[i*8+:64] = scramble_data(
          sram_data_key_seed[i*8+:64], Secret1Idx);
      mem_bkdr_util_h.write64(i + SramDataKeySeedOffset,
                              scrambled_sram_data_key_seed[i*8+:64]);
    end

    partition_data = {<<32{
      scrambled_sram_data_key_seed
    }};
    digest = cal_digest(Secret1Idx, partition_data);
    mem_bkdr_util_h.write64(Secret1DigestOffset, digest);
  endfunction

  function automatic void otp_write_secret2_partition(
      mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h,
      bit [RmaTokenSize*8-1:0] rma_token,
      bit [CreatorRootKeyShare0Size*8-1:0] creator_root_key_share0,
      bit [CreatorRootKeyShare1Size*8-1:0] creator_root_key_share1,
      bit [CreatorSeedSize*8-1:0] creator_seed
  );
    bit [Secret2DigestSize*8-1:0] digest;
    bit [bus_params_pkg::BUS_DW-1:0] partition_data[$];
    bit [RmaTokenSize*8-1:0] scrambled_rma_token;
    bit [CreatorRootKeyShare0Size*8-1:0] scrambled_creator_root_key_share0;
    bit [CreatorRootKeyShare1Size*8-1:0] scrambled_creator_root_key_share1;
    bit [CreatorSeedSize*8-1:0] scrambled_creator_seed;

    for (int i = 0; i < RmaTokenSize; i += 8) begin
      scrambled_rma_token[i*8+:64] = scramble_data(
          rma_token[i*8+:64], Secret2Idx);
      mem_bkdr_util_h.write64(i + RmaTokenOffset,
                              scrambled_rma_token[i*8+:64]);
    end
    for (int i = 0; i < CreatorRootKeyShare0Size; i += 8) begin
      scrambled_creator_root_key_share0[i*8+:64] = scramble_data(
          creator_root_key_share0[i*8+:64], Secret2Idx);
      mem_bkdr_util_h.write64(i + CreatorRootKeyShare0Offset,
                              scrambled_creator_root_key_share0[i*8+:64]);
    end
    for (int i = 0; i < CreatorRootKeyShare1Size; i += 8) begin
      scrambled_creator_root_key_share1[i*8+:64] = scramble_data(
          creator_root_key_share1[i*8+:64], Secret2Idx);
      mem_bkdr_util_h.write64(i + CreatorRootKeyShare1Offset,
                              scrambled_creator_root_key_share1[i*8+:64]);
    end
    for (int i = 0; i < CreatorSeedSize; i += 8) begin
      scrambled_creator_seed[i*8+:64] = scramble_data(
          creator_seed[i*8+:64], Secret2Idx);
      mem_bkdr_util_h.write64(i + CreatorSeedOffset,
                              scrambled_creator_seed[i*8+:64]);
    end

    partition_data = {<<32{
      scrambled_creator_seed,
      scrambled_creator_root_key_share1,
      scrambled_creator_root_key_share0,
      scrambled_rma_token
    }};
    digest = cal_digest(Secret2Idx, partition_data);
    mem_bkdr_util_h.write64(Secret2DigestOffset, digest);
  endfunction

  function automatic void otp_write_secret3_partition(
      mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h,
      bit [OwnerSeedSize*8-1:0] owner_seed
  );
    bit [Secret3DigestSize*8-1:0] digest;
    bit [bus_params_pkg::BUS_DW-1:0] partition_data[$];
    bit [OwnerSeedSize*8-1:0] scrambled_owner_seed;

    for (int i = 0; i < OwnerSeedSize; i += 8) begin
      scrambled_owner_seed[i*8+:64] = scramble_data(
          owner_seed[i*8+:64], Secret3Idx);
      mem_bkdr_util_h.write64(i + OwnerSeedOffset,
                              scrambled_owner_seed[i*8+:64]);
    end

    partition_data = {<<32{
      scrambled_owner_seed
    }};
    digest = cal_digest(Secret3Idx, partition_data);
    mem_bkdr_util_h.write64(Secret3DigestOffset, digest);
  endfunction

  // Functions that clear the provisioning state of the buffered partitions.
  // This is useful in tests that make front-door accesses for provisioning purposes.
  function automatic void otp_clear_hw_cfg0_partition(
      mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h
  );
    for (int i = 0; i < HwCfg0Size; i += 4) begin
      mem_bkdr_util_h.write32(i + HwCfg0Offset, 32'h0);
    end
  endfunction

  function automatic void otp_clear_hw_cfg1_partition(
      mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h
  );
    for (int i = 0; i < HwCfg1Size; i += 4) begin
      mem_bkdr_util_h.write32(i + HwCfg1Offset, 32'h0);
    end
  endfunction

  function automatic void otp_clear_secret0_partition(
      mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h
  );
    for (int i = 0; i < Secret0Size; i += 4) begin
      mem_bkdr_util_h.write32(i + Secret0Offset, 32'h0);
    end
  endfunction

  function automatic void otp_clear_secret1_partition(
      mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h
  );
    for (int i = 0; i < Secret1Size; i += 4) begin
      mem_bkdr_util_h.write32(i + Secret1Offset, 32'h0);
    end
  endfunction

  function automatic void otp_clear_secret2_partition(
      mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h
  );
    for (int i = 0; i < Secret2Size; i += 4) begin
      mem_bkdr_util_h.write32(i + Secret2Offset, 32'h0);
    end
  endfunction

  function automatic void otp_clear_secret3_partition(
      mem_bkdr_util_pkg::mem_bkdr_util mem_bkdr_util_h
  );
    for (int i = 0; i < Secret3Size; i += 4) begin
      mem_bkdr_util_h.write32(i + Secret3Offset, 32'h0);
    end
  endfunction

endpackage : otp_ctrl_mem_bkdr_util_pkg
