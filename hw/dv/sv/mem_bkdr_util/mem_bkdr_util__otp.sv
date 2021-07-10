// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Wrapper functions to write different partitions in OTP.
// This file is included in `mem_bkdr_util.sv` as a continuation of `mem_bkdr_util` class.

virtual function void otp_write_lc_partition(lc_ctrl_state_pkg::lc_state_e lc_state);
  for (int i = 0; i < LcStateSize; i+=4) begin
    write32(i + LcStateOffset, lc_state[i*8+:32]);
  end
endfunction

// The following steps are needed to backdoor write a secret partition:
// 1). Scramble the RAW input data.
// 2). Backdoor write the scrambled input data to OTP memory.
// 3). Calculate the correct digest for the secret partition.
// 4). Backdoor write digest data to OTP memory.
virtual function void otp_write_secret0_partition(bit [TestUnlockTokenSize*8-1:0] unlock_token,
                                                  bit [TestExitTokenSize*8-1:0]   exit_token);
  bit [Secret0DigestSize*8-1:0] digest;

  bit [TestUnlockTokenSize*8-1:0] scrambled_unlock_token;
  bit [TestExitTokenSize*8-1:0] scrambled_exit_token;
  bit [bus_params_pkg::BUS_DW-1:0] secret_data[$];

  for (int i = 0; i < TestUnlockTokenSize; i+=8) begin
    scrambled_unlock_token[i*8+:64] = scramble_data(unlock_token[i*8+:64], Secret0Idx);
    write64(i + TestUnlockTokenOffset, scrambled_unlock_token[i*8+:64]);
  end
  for (int i = 0; i < TestExitTokenSize; i+=8) begin
    scrambled_exit_token[i*8+:64] = scramble_data(exit_token[i*8+:64], Secret0Idx);
    write64(i + TestExitTokenOffset, scrambled_exit_token[i*8+:64]);
  end

  secret_data = {<<32 {scrambled_exit_token, scrambled_unlock_token}};
  digest = cal_digest(Secret0Idx, secret_data);

  write64(Secret0DigestOffset, digest);
endfunction
