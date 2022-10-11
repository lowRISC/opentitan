// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Wrapper functions to write different partitions in OTP.
// This file is included in `mem_bkdr_util.sv` as a continuation of `mem_bkdr_util` class.

virtual function void otp_write_lc_partition_state(lc_ctrl_state_pkg::lc_state_e lc_state);
  for (int i = 0; i < LcStateSize; i += 4) begin
    write32(i + LcStateOffset, lc_state[i*8+:32]);
  end
endfunction : otp_write_lc_partition_state

virtual function lc_ctrl_state_pkg::lc_state_e otp_read_lc_partition_state();
  lc_ctrl_state_pkg::lc_state_e lc_state;
  for (int i = 0; i < LcStateSize; i += 4) begin
    lc_state[i*8 +: 32] = read32(i + LcStateOffset);
  end

  return lc_state;
endfunction : otp_read_lc_partition_state

virtual function void otp_write_lc_partition_cnt(lc_ctrl_state_pkg::lc_cnt_e lc_cnt);
  for (int i = 0; i < LcTransitionCntSize; i += 4) begin
    write32(i + LcTransitionCntOffset, lc_cnt[i*8+:32]);
  end
endfunction : otp_write_lc_partition_cnt

function void otp_write_lc_partition(lc_ctrl_state_pkg::lc_cnt_e lc_cnt,
                                     lc_ctrl_state_pkg::lc_state_e lc_state);

  otp_write_lc_partition_cnt(lc_cnt);
  otp_write_lc_partition_state(lc_state);
endfunction : otp_write_lc_partition

// The following steps are needed to backdoor write a secret partition:
// 1). Scramble the RAW input data.
// 2). Backdoor write the scrambled input data to OTP memory.
// 3). Calculate the correct digest for the secret partition.
// 4). Backdoor write digest data to OTP memory.
virtual function void otp_write_secret0_partition(
    bit [TestUnlockTokenSize*8-1:0] unlock_token,
    bit [TestExitTokenSize*8-1:0] exit_token);
  bit [Secret0DigestSize*8-1:0] digest;

  bit [TestUnlockTokenSize*8-1:0] scrambled_unlock_token;
  bit [TestExitTokenSize*8-1:0] scrambled_exit_token;
  bit [bus_params_pkg::BUS_DW-1:0] secret_data[$];

  for (int i = 0; i < TestUnlockTokenSize; i += 8) begin
    scrambled_unlock_token[i*8+:64] = scramble_data(unlock_token[i*8+:64], Secret0Idx);
    write64(i + TestUnlockTokenOffset, scrambled_unlock_token[i*8+:64]);
  end
  for (int i = 0; i < TestExitTokenSize; i += 8) begin
    scrambled_exit_token[i*8+:64] = scramble_data(exit_token[i*8+:64], Secret0Idx);
    write64(i + TestExitTokenOffset, scrambled_exit_token[i*8+:64]);
  end

  secret_data = {<<32{scrambled_exit_token, scrambled_unlock_token}};
  digest = cal_digest(Secret0Idx, secret_data);

  write64(Secret0DigestOffset, digest);
endfunction

virtual function void otp_write_secret1_partition(
    bit [FlashAddrKeySeedSize*8-1:0] flash_addr_key_seed,
    bit [FlashDataKeySeedSize*8-1:0] flash_data_key_seed,
    bit [SramDataKeySeedSize*8-1:0] sram_data_key_seed);
  bit [Secret1DigestSize*8-1:0] digest;

  bit [FlashAddrKeySeedSize*8-1:0] scrambled_flash_addr_key;
  bit [FlashDataKeySeedSize*8-1:0] scrambled_flash_data_key;
  bit [SramDataKeySeedSize*8-1:0] scrambled_sram_data_key;
  bit [bus_params_pkg::BUS_DW-1:0] secret_data[$];

  for (int i = 0; i < FlashAddrKeySeedSize; i += 8) begin
    scrambled_flash_addr_key[i*8+:64] = scramble_data(flash_addr_key_seed[i*8+:64], Secret1Idx);
    write64(i + FlashAddrKeySeedOffset, scrambled_flash_addr_key[i*8+:64]);
  end
  for (int i = 0; i < FlashDataKeySeedSize; i += 8) begin
    scrambled_flash_data_key[i*8+:64] = scramble_data(flash_data_key_seed[i*8+:64], Secret1Idx);
    write64(i + FlashDataKeySeedOffset, scrambled_flash_data_key[i*8+:64]);
  end
  for (int i = 0; i < SramDataKeySeedSize; i += 8) begin
    scrambled_sram_data_key[i*8+:64] = scramble_data(sram_data_key_seed[i*8+:64], Secret1Idx);
    write64(i + SramDataKeySeedOffset, scrambled_sram_data_key[i*8+:64]);
  end

  secret_data = {<<32 {scrambled_sram_data_key, scrambled_flash_data_key, scrambled_flash_addr_key}};
  digest = cal_digest(Secret1Idx, secret_data);

  write64(Secret1DigestOffset, digest);
endfunction

virtual function void otp_write_secret2_partition(bit [RmaTokenSize*8-1:0] rma_unlock_token,
                                                  bit [CreatorRootKeyShare0Size*8-1:0] creator_root_key0,
                                                  bit [CreatorRootKeyShare1Size*8-1:0] creator_root_key1
);

  bit [Secret2DigestSize*8-1:0] digest;

  bit [RmaTokenSize*8-1:0] scrambled_unlock_token;
  bit [CreatorRootKeyShare0Size*8-1:0] scrambled_root_key0;
  bit [CreatorRootKeyShare1Size*8-1:0] scrambled_root_key1;
  bit [bus_params_pkg::BUS_DW-1:0] secret_data[$];

  for (int i = 0; i < RmaTokenSize; i+=8) begin
    scrambled_unlock_token[i*8+:64] = scramble_data(rma_unlock_token[i*8+:64], Secret2Idx);
    write64(i + RmaTokenOffset, scrambled_unlock_token[i*8+:64]);
  end
  for (int i = 0; i < CreatorRootKeyShare0Size; i+=8) begin
    scrambled_root_key0[i*8+:64] = scramble_data(creator_root_key0[i*8+:64], Secret2Idx);
    write64(i + CreatorRootKeyShare0Offset, scrambled_root_key0[i*8+:64]);
  end
  for (int i = 0; i < CreatorRootKeyShare1Size; i+=8) begin
    scrambled_root_key1[i*8+:64] = scramble_data(creator_root_key1[i*8+:64], Secret2Idx);
    write64(i + CreatorRootKeyShare1Offset, scrambled_root_key1[i*8+:64]);
  end

  secret_data = {<<32 {scrambled_root_key1, scrambled_root_key0, scrambled_unlock_token}};
  digest = cal_digest(Secret2Idx, secret_data);

  write64(Secret2DigestOffset, digest);
endfunction

virtual function void otp_write_hw_cfg_partition(
    bit [DeviceIdSize*8-1:0] device_id, bit [ManufStateSize*8-1:0] manuf_state,
    bit [EnSramIfetchSize*8-1:0] en_sram_ifetch,
    bit [EnCsrngSwAppReadSize*8-1:0] en_csrng_sw_app_read,
    bit [EnEntropySrcFwReadSize*8-1:0] en_entropy_src_fw_read,
    bit [EnEntropySrcFwOverSize*8-1:0] en_entropy_src_fw_over);
  bit [HwCfgDigestSize*8-1:0] digest;

  bit [bus_params_pkg::BUS_DW-1:0] hw_cfg_data[$];

  for (int i = 0; i < DeviceIdSize; i += 4) begin
    write32(i + DeviceIdOffset, device_id[i*8+:32]);
  end
  for (int i = 0; i < ManufStateSize; i += 4) begin
    write32(i + ManufStateOffset, manuf_state[i*8+:32]);
  end
  write32(EnSramIfetchOffset,
          {en_entropy_src_fw_over, en_entropy_src_fw_read, en_csrng_sw_app_read, en_sram_ifetch});

  hw_cfg_data = {<<32 {32'h0, en_entropy_src_fw_over, en_entropy_src_fw_read,
                       en_csrng_sw_app_read, en_sram_ifetch, manuf_state, device_id}};
  digest = cal_digest(HwCfgIdx, hw_cfg_data);

  write64(HwCfgDigestOffset, digest);
endfunction

// Functions that clear the provisioning state of the buffered partitions.
// This is useful in tests that make front-door accesses for provisioning purposes.
virtual function void otp_clear_secret0_partition();
  for (int i = 0; i < Secret0Size; i += 4) begin
    write32(i + Secret0Offset, 32'h0);
  end
endfunction

virtual function void otp_clear_secret1_partition();
  for (int i = 0; i < Secret1Size; i += 4) begin
    write32(i + Secret1Offset, 32'h0);
  end
endfunction

virtual function void otp_clear_secret2_partition();
  for (int i = 0; i < Secret2Size; i += 4) begin
    write32(i + Secret2Offset, 32'h0);
  end
endfunction

virtual function void otp_clear_hw_cfg_partition();
  for (int i = 0; i < HwCfgSize; i += 4) begin
    write32(i + HwCfgOffset, 32'h0);
  end
endfunction
