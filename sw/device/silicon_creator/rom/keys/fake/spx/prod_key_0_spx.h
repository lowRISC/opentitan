// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_KEYS_FAKE_SPX_PROD_KEY_0_SPX_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_KEYS_FAKE_SPX_PROD_KEY_0_SPX_H_

/*
 * Public key of test 2 in
 * https://github.com/lowRISC/opentitan/blob/4e652475f697863fa3bf4ec38d53dbcf13e2f8a1/sw/device/tests/crypto/testvectors/sphincsplus_kat/sphincsplus_shake_128s_simple_testvectors_kat0.hjson
 * interpreted as a big-endian hex string and transformed using
 * `echo -n [HEX_STR] | sed -e 's/\(..\)\(..\)\(..\)\(..\)/0x\L\4\3\2\1,\\\n/g'`
 */
#define PROD_KEY_0_SPX \
  {                    \
    .data = {          \
      0xf6bcd64f,      \
      0xf9231016,      \
      0x1f46dbdc,      \
      0x2504d00f,      \
      0x6d30febc,      \
      0xe9e511f9,      \
      0x98b648e1,      \
      0xde00e74b,      \
    }                  \
  }
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_KEYS_FAKE_SPX_PROD_KEY_0_SPX_H_
