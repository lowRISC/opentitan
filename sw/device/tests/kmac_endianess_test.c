// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * KMAC test description.
 */
typedef struct kmac_test {
  dif_kmac_mode_kmac_t mode;
  dif_kmac_key_t key;

  const char *message_big_endian;
  const char *message_little_endian;
  size_t message_len;

  size_t digest_len;
} kmac_test_t;

/**
 * KMAC test.
 *
 * Example taken from:
 * https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/KMAC_samples.pdf
 */
const kmac_test_t kmac_test = {
    // KMAC
    .mode = kDifKmacModeKmacLen128,
    .key =
        (dif_kmac_key_t){
            .share0 = {0x43424140, 0x47464544, 0x4B4A4948, 0x4F4E4D4C,
                       0x53525150, 0x57565554, 0x5B5A5958, 0x5F5E5D5C},
            .share1 = {0},
            .length = kDifKmacKeyLen256,
        },
    .message_big_endian = "\x00\x01\x02\x03",
    .message_little_endian = "\x03\x02\x01\x00",
    .message_len = 4,
    .digest_len = 8,
};

/**
 * Big to little endianess converter.
 *
 * Helper function to convert from big to little endian.
 *
 * @param big_endian the number in big endian representation.
 * @return the number in little endian representation.
 */
uint32_t big_to_little_endian(uint32_t big_endian) {
  uint32_t little_endian = 0;
  little_endian = (big_endian >> 24) & 0xff;
  little_endian |= (big_endian >> 8) & 0xff00;
  little_endian |= (big_endian << 8) & 0xff0000;
  little_endian |= (big_endian << 24) & 0xff000000;

  return little_endian;
}

/**
 * Endianess test.
 *
 * This test runs the same KMAC operation four times with the following
 * endianess configuration:
 * - Little endian message, little endian digest.
 * - Little endian message, big endian digest.
 * - Big endian message, little endian digest.
 * - Big endian message, big endian digest.
 *
 * The output of the little endian message and little endian digest is used as a
 * reference output as this is the default configuration. The other outputs are
 * accordingly converted and compared.
 *
 * @return OK or error.
 */
status_t test_endianess(void) {
  // Intialize KMAC hardware.
  dif_kmac_t kmac;
  dif_kmac_operation_state_t kmac_operation_state;
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));

  // Test configurations.
  char msg_log[4][7] = {"little", "little", "big", "big"};
  char digest_log[4][7] = {"little", "big", "little", "big"};
  bool msg_endianess_big[4] = {false, false, true, true};
  bool digest_endianess_big[4] = {false, true, false, true};

  // Reference output for little endian message & digest.
  uint32_t ref_out[kmac_test.digest_len];

  for (size_t it = 0; it < ARRAYSIZE(msg_endianess_big); it++) {
    LOG_INFO("Testing %s endian message and %s endian digest.", msg_log[it],
             digest_log[it]);

    dif_kmac_config_t config = (dif_kmac_config_t){
        .entropy_mode = kDifKmacEntropyModeSoftware,
        .entropy_seed = {0xb153e3fe, 0x09596819, 0x3e85a6e8, 0xb6dcdaba,
                         0x50dc409c, 0x11e1ebd1},
        .entropy_fast_process = kDifToggleEnabled,
        .message_big_endian = msg_endianess_big[it],
        .output_big_endian = digest_endianess_big[it],
    };

    CHECK_DIF_OK(dif_kmac_configure(&kmac, config));
    CHECK_DIF_OK(dif_kmac_mode_kmac_start(&kmac, &kmac_operation_state,
                                          kmac_test.mode, kmac_test.digest_len,
                                          &kmac_test.key, NULL));
    const char *message;
    if (msg_endianess_big[it]) {
      message = kmac_test.message_big_endian;
    } else {
      message = kmac_test.message_little_endian;
    }

    uint32_t out[kmac_test.digest_len];
    CHECK_DIF_OK(dif_kmac_absorb(&kmac, &kmac_operation_state, message,
                                 kmac_test.message_len, NULL));
    CHECK_DIF_OK(dif_kmac_squeeze(&kmac, &kmac_operation_state, out,
                                  kmac_test.digest_len, /*processed=*/NULL,
                                  /*capacity=*/NULL));
    CHECK_DIF_OK(dif_kmac_end(&kmac, &kmac_operation_state));

    if (msg_endianess_big[it] == false && digest_endianess_big[it] == false) {
      // We use little endian message/digest as the reference output.
      memcpy(ref_out, out, sizeof(ref_out));
    } else if (digest_endianess_big[it] == true) {
      // Got big endianess digest, convert to little endian and compare with
      // reference digest.
      uint32_t big_to_little[kmac_test.digest_len];
      for (int i = 0; i < kmac_test.digest_len; i++) {
        big_to_little[i] = big_to_little_endian(out[i]);
      }
      CHECK_ARRAYS_EQ(big_to_little, ref_out, kmac_test.digest_len);
    } else {
      // Got little endianess digest, compare with reference digest.
      CHECK_ARRAYS_EQ(out, ref_out, kmac_test.digest_len);
    }
  }

  return OK_STATUS();
}

bool test_main(void) {
  test_endianess();
  return true;
}
