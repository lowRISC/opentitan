// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "kmac_regs.h"  // Generated.

OTTF_DEFINE_TEST_CONFIG();

/**
 * Digest lengths in 32-bit words.
 */
#define DIGEST_LEN_SHA3_224 (224 / 32)
#define DIGEST_LEN_SHA3_256 (256 / 32)
#define DIGEST_LEN_SHA3_384 (384 / 32)
#define DIGEST_LEN_SHA3_512 (512 / 32)
#define DIGEST_LEN_SHA3_MAX DIGEST_LEN_SHA3_512

/**
 * SHA-3 test description.
 */
typedef struct sha3_test {
  dif_kmac_mode_sha3_t mode;

  const char *message;
  size_t message_len;

  const uint32_t digest[DIGEST_LEN_SHA3_MAX];
  size_t digest_len;
} sha3_test_t;

/**
 * SHA-3 tests.
 */
const sha3_test_t sha3_tests[] = {
    // Examples taken from NIST FIPS-202 Algorithm Test Vectors:
    // https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/sha-3bytetestvectors.zip
    {
        .mode = kDifKmacModeSha3Len224,
        .message = NULL,
        .message_len = 0,
        .digest = {0x42034e6b, 0xb7db6736, 0x45156e3b, 0xabb10e4f, 0x9a7f59d4,
                   0x3f8e071b, 0xc76b5a5b},
        .digest_len = DIGEST_LEN_SHA3_224,
    },
    {
        .mode = kDifKmacModeSha3Len256,
        .message = "\xe7\x37\x21\x05",
        .message_len = 32 / 8,
        .digest = {0x8ab6423a, 0x8cf279b0, 0x52c7a34c, 0x90276f29, 0x78fec406,
                   0xd979ebb1, 0x057f7789, 0xae46401e},
        .digest_len = DIGEST_LEN_SHA3_256,
    },
    {
        .mode = kDifKmacModeSha3Len384,
        .message = "\xa7\x48\x47\x93\x0a\x03\xab\xee\xa4\x73\xe1\xf3\xdc\x30"
                   "\xb8\x88\x15",
        .message_len = 136 / 8,
        .digest = {0x29f9a6db, 0xd6f955fe, 0xc0675f6c, 0xf1823baf, 0xb358cf7b,
                   0x16f35267, 0x3f08165c, 0x78d48fea, 0xf20369ee, 0xd20a827f,
                   0xaf5099dd, 0x00678cb4},
        .digest_len = DIGEST_LEN_SHA3_384,
    },
    {
        .mode = kDifKmacModeSha3Len512,
        .message =
            "\x66\x4e\xf2\xe3\xa7\x05\x9d\xaf\x1c\x58\xca\xf5\x20\x08\xc5\x22"
            "\x7e\x85\xcd\xcb\x83\xb4\xc5\x94\x57\xf0\x2c\x50\x8d\x4f\x4f\x69"
            "\xf8\x26\xbd\x82\xc0\xcf\xfc\x5c\xb6\xa9\x7a\xf6\xe5\x61\xc6\xf9"
            "\x69\x70\x00\x52\x85\xe5\x8f\x21\xef\x65\x11\xd2\x6e\x70\x98\x89"
            "\xa7\xe5\x13\xc4\x34\xc9\x0a\x3c\xf7\x44\x8f\x0c\xae\xec\x71\x14"
            "\xc7\x47\xb2\xa0\x75\x8a\x3b\x45\x03\xa7\xcf\x0c\x69\x87\x3e\xd3"
            "\x1d\x94\xdb\xef\x2b\x7b\x2f\x16\x88\x30\xef\x7d\xa3\x32\x2c\x3d"
            "\x3e\x10\xca\xfb\x7c\x2c\x33\xc8\x3b\xbf\x4c\x46\xa3\x1d\xa9\x0c"
            "\xff\x3b\xfd\x4c\xcc\x6e\xd4\xb3\x10\x75\x84\x91\xee\xba\x60\x3a"
            "\x76",
        .message_len = 1160 / 8,
        .digest = {0xf15f82e5, 0xd570c0a3, 0xe7bb2fa5, 0x444a8511, 0x5f295405,
                   0x69797afb, 0xd10879a1, 0xbebf6301, 0xa6521d8f, 0x13a0e876,
                   0x1ca1567b, 0xb4fb0fdf, 0x9f89bc56, 0x4bd127c7, 0x322288d8,
                   0x4e919d54},
        .digest_len = DIGEST_LEN_SHA3_512,
    },
};

#define DIGEST_LEN_SHAKE_MAX 102

/**
 * SHAKE test description.
 */
typedef struct shake_test {
  dif_kmac_mode_shake_t mode;

  const char *message;
  size_t message_len;

  const uint32_t digest[DIGEST_LEN_SHAKE_MAX];
  size_t digest_len;
} shake_test_t;

/**
 * SHAKE tests.
 */
// Examples generated using a custom Go program importing package
// `golang.org/x/crypto/sha3`
const shake_test_t shake_tests[] = {
    {
        .mode = kDifKmacModeShakeLen128,
        .message = "OpenTitan",
        .message_len = 9,
        .digest = {0x235a6522, 0x3bd735ac, 0x77832247, 0xc6b12919, 0xfb80eff0,
                   0xb8308a5a, 0xcb25db1f, 0xc5ce4cf2, 0x349730fc, 0xcedf024c,
                   0xff0eefec, 0x6985fe35, 0x3c46a736, 0x0084044b, 0x6d9f9920,
                   0x7c0ab055, 0x19d1d3ce, 0xb4353949, 0xfe8ffbcd, 0x5a7f2ec6,
                   0xc3cf795f, 0xa56d0d7b, 0x520c3358, 0x11237ec9, 0x4ca5ed53,
                   0x2999edc0, 0x6c59c68f, 0x54d9890c, 0x89a33092, 0xf406c674,
                   0xe2b4ebf1, 0x14e68bb2, 0x898ceb72, 0x1878875f, 0x9d7bb8d2,
                   0x268e4a5a, 0xe5da510f, 0x97e5d3bc, 0xaae1b7bc, 0xa337f70b,
                   0xeae3cc65, 0xb8429058, 0xe4319c08, 0xd35e2786, 0xbc99af6e,
                   0x19a04aa8, 0xccbf18bf, 0xf681ebd4, 0x3d6da575, 0x2f0b9406},
        .digest_len = 1600 / 8 / 4,  // Rate (r) is 42 words.
    },
    {
        .mode = kDifKmacModeShakeLen256,
        .message = "OpenTitan",
        .message_len = 9,
        .digest = {0x6a0faccd, 0xbf29cb1a, 0xb631f604, 0xdbcab36,  0xa15d167b,
                   0x18dc668b, 0x272e411b, 0x865e651a, 0x8abedb2a, 0x8db38e78,
                   0xe503c9a2, 0xe64faca9, 0xcbd867d0, 0xdba6f20f, 0xbe129db9,
                   0x842dc15c, 0x1406410b, 0x014ce621, 0x5d24eaf2, 0x63bdf816,
                   0xfb236f50, 0xbdba910c, 0xf4ba0e9a, 0x74b5a51f, 0xd644dffd,
                   0xcd650165, 0xe4ec5e7d, 0x64df5448, 0xdcf7b5e7, 0x68709c07,
                   0x47eed1db, 0xc1e55b24, 0x3c02fad9, 0xd72db62e, 0xc5a48eaf,
                   0xd14bb0c4, 0x0f7143ba, 0x4071b63e, 0x21f0ec4b, 0x41065039,
                   0x1b3e41c0, 0xd0d3b1d0, 0xca16acb9, 0xa06f55aa, 0x7bc7ce75,
                   0x08da25ce, 0x596a654b, 0x0b57ae54, 0x4b88c863, 0x199202d7,
                   0x88c112b6, 0xf6dc4a95, 0xe1cfeffa, 0xa7809e6f, 0x3a796dcd,
                   0xb5962e44, 0x179d6ff0, 0xc898c5a9, 0xd3f02195, 0x43623028,
                   0x4c3a4fe7, 0x2fab7bda, 0x04e5b4d4, 0xe0420692, 0x32fcaa2a,
                   0x05e92f07, 0xba0564ea, 0x7b169778, 0x61d4ca3e, 0x4a5d92ec,
                   0x079cb3ba, 0x9a784e40, 0x6381498c, 0xed6d8b6a, 0x2be74d42,
                   0xa234a3db, 0x60d10de8, 0xf0c77dda, 0xc8f94b72, 0x239a2bdf,
                   0xbfeba4a6, 0xc91042e9, 0xa5a11310, 0x8b44d66a, 0xea9bff2f,
                   0x441a445f, 0xe88ee35d, 0x89386c12, 0x1a8de11e, 0x46aff650,
                   0x423323c9, 0xba7b8db4, 0x06c36eb0, 0x4fd75b36, 0xf0c70001,
                   0x0aefb1df, 0x6ae399e6, 0xf71930a6, 0xdef2206,  0x5ce2a640,
                   0x6a82fcf4, 0xa91b0815},
        .digest_len = 3264 / 8 / 4,  // Rate (r) is 34 words.
    },
};

/**
 * Run SHA-3 test cases using single blocking absorb/squeeze operations.
 */
void run_sha3_test(dif_kmac_t *kmac) {
  dif_kmac_operation_state_t operation_state;
  for (int i = 0; i < ARRAYSIZE(sha3_tests); ++i) {
    sha3_test_t test = sha3_tests[i];

    CHECK_DIF_OK(dif_kmac_mode_sha3_start(kmac, &operation_state, test.mode));
    if (test.message_len > 0) {
      CHECK_DIF_OK(dif_kmac_absorb(kmac, &operation_state, test.message,
                                   test.message_len, NULL));
    }
    uint32_t out[DIGEST_LEN_SHA3_MAX];
    CHECK(DIGEST_LEN_SHA3_MAX >= test.digest_len);
    CHECK_DIF_OK(dif_kmac_squeeze(kmac, &operation_state, out, test.digest_len,
                                  /*processed=*/NULL, /*capacity=*/NULL));
    CHECK_DIF_OK(dif_kmac_end(kmac, &operation_state));

    // Wait for the hardware engine to actually finish. On FPGA, it may take
    // a while until the DONE command gets actually executed (see SecCmdDelay
    // SystemVerilog parameter).
    CHECK_DIF_OK(dif_kmac_poll_status(kmac, KMAC_STATUS_SHA3_IDLE_BIT));

    for (int j = 0; j < test.digest_len; ++j) {
      CHECK(out[j] == test.digest[j],
            "test %d: mismatch at %d got=0x%x want=0x%x", i, j, out[j],
            test.digest[j]);
    }
  }
}

/**
 * Run a SHA-3 test case with varying alignments.
 */
void run_sha3_alignment_test(dif_kmac_t *kmac) {
  // Examples taken from NIST FIPS-202 Algorithm Test Vectors:
  // https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Algorithm-Validation-Program/documents/sha3/sha-3bytetestvectors.zip
  const char kMsg[] =
      "\xa7\x48\x47\x93\x0a\x03\xab\xee\xa4\x73\xe1\xf3\xdc\x30"
      "\xb8\x88\x15";
  const size_t kSize = ARRAYSIZE(kMsg);
  const uint32_t kExpect = 0x29f9a6db;
  const dif_kmac_mode_sha3_t kMode = kDifKmacModeSha3Len384;
  dif_kmac_operation_state_t operation_state;

  for (size_t i = 0; i < sizeof(uint32_t); ++i) {
    char buffer[ARRAYSIZE(kMsg) + sizeof(uint32_t)] = {0};
    memcpy(&buffer[i], kMsg, kSize);

    CHECK_DIF_OK(dif_kmac_mode_sha3_start(kmac, &operation_state, kMode));
    CHECK_DIF_OK(
        dif_kmac_absorb(kmac, &operation_state, &buffer[i], kSize, NULL));

    // Checking the first 32-bits of the digest is sufficient.
    uint32_t out;
    CHECK_DIF_OK(dif_kmac_squeeze(kmac, &operation_state, &out,
                                  sizeof(uint32_t), /*processed=*/NULL,
                                  /*capacity=*/NULL));
    CHECK_DIF_OK(dif_kmac_end(kmac, &operation_state));

    // Wait for the hardware engine to actually finish. On FPGA, it may take
    // a while until the DONE command gets actually executed (see SecCmdDelay
    // SystemVerilog parameter).
    CHECK_DIF_OK(dif_kmac_poll_status(kmac, KMAC_STATUS_SHA3_IDLE_BIT));

    CHECK_DIF_OK((out == kExpect),
                 "mismatch at alignment %u got 0x%u want 0x%x", i, out,
                 kExpect);
  }

  // Run a SHA-3 test case using multiple absorb calls.
  {
    CHECK_DIF_OK(dif_kmac_mode_sha3_start(kmac, &operation_state, kMode));
    CHECK_DIF_OK(dif_kmac_absorb(kmac, &operation_state, &kMsg[0], 1, NULL));
    CHECK_DIF_OK(dif_kmac_absorb(kmac, &operation_state, &kMsg[1], 2, NULL));
    CHECK_DIF_OK(dif_kmac_absorb(kmac, &operation_state, &kMsg[3], 5, NULL));
    CHECK_DIF_OK(dif_kmac_absorb(kmac, &operation_state, &kMsg[8], 4, NULL));
    CHECK_DIF_OK(
        dif_kmac_absorb(kmac, &operation_state, &kMsg[12], kSize - 12, NULL));

    // Checking the first 32-bits of the digest is sufficient.
    uint32_t out;
    CHECK_DIF_OK(dif_kmac_squeeze(kmac, &operation_state, &out,
                                  sizeof(uint32_t), /*processed=*/NULL,
                                  /*capacity=*/NULL));
    CHECK_DIF_OK(dif_kmac_end(kmac, &operation_state));

    // Wait for the hardware engine to actually finish. On FPGA, it may take
    // a while until the DONE command gets actually executed (see SecCmdDelay
    // SystemVerilog parameter).
    CHECK_DIF_OK(dif_kmac_poll_status(kmac, KMAC_STATUS_SHA3_IDLE_BIT));

    CHECK_DIF_OK((out == kExpect), "mismatch got 0x%u want 0x%x", out, kExpect);
  }
}

/**
 * Run SHAKE test cases using single blocking absorb/squeeze operations.
 */
void run_shake_test(dif_kmac_t *kmac) {
  dif_kmac_operation_state_t operation_state;

  for (int i = 0; i < ARRAYSIZE(shake_tests); ++i) {
    shake_test_t test = shake_tests[i];

    CHECK_DIF_OK(dif_kmac_mode_shake_start(kmac, &operation_state, test.mode));
    if (test.message_len > 0) {
      CHECK_DIF_OK(dif_kmac_absorb(kmac, &operation_state, test.message,
                                   test.message_len, NULL));
    }
    uint32_t out[DIGEST_LEN_SHAKE_MAX];
    CHECK(DIGEST_LEN_SHAKE_MAX >= test.digest_len);
    CHECK_DIF_OK(dif_kmac_squeeze(kmac, &operation_state, out, test.digest_len,
                                  /*processed=*/NULL, /*capacity=*/NULL));
    CHECK_DIF_OK(dif_kmac_end(kmac, &operation_state));

    // Wait for the hardware engine to actually finish. On FPGA, it may take
    // a while until the DONE command gets actually executed (see SecCmdDelay
    // SystemVerilog parameter).
    CHECK_DIF_OK(dif_kmac_poll_status(kmac, KMAC_STATUS_SHA3_IDLE_BIT));

    for (int j = 0; j < test.digest_len; ++j) {
      CHECK(out[j] == test.digest[j],
            "test %d: mismatch at %d got=0x%x want=0x%x", i, j, out[j],
            test.digest[j]);
    }
  }
}

bool test_main(void) {
  LOG_INFO("Running KMAC DIF test...");

  // Intialize KMAC hardware.
  dif_kmac_t kmac;
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));

  // Configure KMAC hardware using software entropy. The seed has been randomnly
  // chosen and is genrated using enerated using
  // ./util/design/gen-lfsr-seed.py --width 192 --seed 2034386436 --prefix ""
  dif_kmac_config_t config = (dif_kmac_config_t){
      .entropy_mode = kDifKmacEntropyModeSoftware,
      .entropy_seed = {0xb153e3fe, 0x09596819, 0x3e85a6e8, 0xb6dcdaba,
                       0x50dc409c, 0x11e1ebd1},
      .entropy_fast_process = kDifToggleEnabled,
  };
  CHECK_DIF_OK(dif_kmac_configure(&kmac, config));

  run_sha3_test(&kmac);
  run_sha3_alignment_test(&kmac);
  run_shake_test(&kmac);

  return true;
}
