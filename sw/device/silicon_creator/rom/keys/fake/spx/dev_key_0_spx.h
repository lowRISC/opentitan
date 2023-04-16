// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_KEYS_FAKE_SPX_DEV_KEY_0_SPX_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_KEYS_FAKE_SPX_DEV_KEY_0_SPX_H_

/*
 * Public key of test 1 in
 * https://github.com/lowRISC/opentitan/blob/4e652475f697863fa3bf4ec38d53dbcf13e2f8a1/sw/device/tests/crypto/testvectors/sphincsplus_kat/sphincsplus_shake_128s_simple_testvectors_kat0.hjson
 * interpreted as a little-endian hex string and transformed using
 * `echo -n [HEX_STR] | sed -e 's/\(..\)\(..\)\(..\)\(..\)/0x\L\4\3\2\1,\\\n/g'`
 */
#define DEV_KEY_0_SPX \
  {                   \
    .data = {         \
      0x4c5aa4d5,     \
      0x3c4006ed,     \
      0x71e85755,     \
      0xea30cb13,     \
      0x5f0e5bd2,     \
      0x04e25326,     \
      0x55e0469b,     \
      0x0963a596,     \
    }                 \
  }
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_KEYS_FAKE_SPX_DEV_KEY_0_SPX_H_
