// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_KEYS_FAKE_SPX_TEST_KEY_0_SPX_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_KEYS_FAKE_SPX_TEST_KEY_0_SPX_H_

/*
 * Public key of test 0 in
 * https://github.com/lowRISC/opentitan/blob/4e652475f697863fa3bf4ec38d53dbcf13e2f8a1/sw/device/tests/crypto/testvectors/sphincsplus_kat/sphincsplus_shake_128s_simple_testvectors_kat0.hjson
 * interpreted as a big-endian hex string and transformed using
 * `echo -n [HEX_STR] | sed -e 's/\(..\)\(..\)\(..\)\(..\)/0x\L\4\3\2\1,\\\n/g'`
 */
#define TEST_KEY_0_SPX \
  {                    \
    .data = {          \
      0xcfd705b5,      \
      0x74491bad,      \
      0x863c3299,      \
      0x475e3286,      \
      0xb2cb65fd,      \
      0xc3447a86,      \
      0x84cc7ad6,      \
      0x9f60cf0a,      \
    }                  \
  }
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_KEYS_FAKE_SPX_TEST_KEY_0_SPX_H_
