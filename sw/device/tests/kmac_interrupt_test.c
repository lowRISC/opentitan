// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_kmac.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/flash_ctrl.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/test_framework/ottf.h"
#include "sw/device/lib/testing/test_framework/test_status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const test_config_t kTestConfig;

/**
 * Digest lengths in 32-bit words.
 */
#define DIGEST_LEN_SHA3_224 (224 / 32)
#define DIGEST_LEN_SHA3_256 (256 / 32)
#define DIGEST_LEN_SHA3_384 (384 / 32)
#define DIGEST_LEN_SHA3_512 (512 / 32)
#define DIGEST_LEN_SHA3_MAX DIGEST_LEN_SHA3_512

#define BLOCK_LEN (64 / 8 * 9)  // Fifo depth
#define TIMEOUT_US (10000)      // 10ms
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
        .mode = kDifKmacModeSha3Len256,
        .message = "\xe7\x37\x21\x05",
        .message_len = 32 / 8,
        .digest = {0x8ab6423a, 0x8cf279b0, 0x52c7a34c, 0x90276f29, 0x78fec406,
                   0xd979ebb1, 0x057f7789, 0xae46401e},
        .digest_len = DIGEST_LEN_SHA3_256,
    },
    {
        .mode = kDifKmacModeSha3Len224,
        .message =
            "\x31\xc8\x2d\x71\x78\x5b\x7c\xa6\xb6\x51\xcb\x6c\x8c\x9a\xd5\xe2"
            "\xac\xeb\x0b\x06\x33\xc0\x88\xd3\x3a\xa2\x47\xad\xa7\xa5\x94\xff"
            "\x49\x36\xc0\x23\x25\x13\x19\x82\x0a\x9b\x19\xfc\x6c\x48\xde\x8a"
            "\x6f\x7a\xda\x21\x41\x76\xcc\xda\xad\xae\xef\x51\xed\x43\x71\x4a"
            "\xc0\xc8\x26\x9b\xbd\x49\x7e\x46\xe7\x8b\xb5\xe5\x81\x96\x49\x4b"
            "\x24\x71\xb1\x68\x0e\x2d\x4c\x6d\xbd\x24\x98\x31\xbd\x83\xa4\xd3"
            "\xbe\x06\xc8\xa2\xe9\x03\x93\x39\x74\xaa\x05\xee\x74\x8b\xfe\x6e"
            "\xf3\x59\xf7\xa1\x43\xed\xf0\xd4\x91\x8d\xa9\x16\xbd\x6f\x15\xe2"
            "\x6a\x79\x0c\xff\x51\x4b\x40\xa5\xda\x7f\x72\xe1\xed\x2f\xe6\x3a"
            "\x05\xb8\x14\x95\x87\xbe\xa0\x56\x53\x71\x8c\xc8\x98\x0e\xad\xbf"
            "\xec\xa8\x5b\x7c\x9c\x28\x6d\xd0\x40\x93\x65\x85\x93\x8b\xe7\xf9"
            "\x82\x19\x70\x0c\x83\xa9\x44\x3c\x28\x56\xa8\x0f\xf4\x68\x52\xb2"
            "\x6d\x1b\x1e\xdf\x72\xa3\x02\x03\xcf\x6c\x44\xa1\x0f\xa6\xea\xf1"
            "\x92\x01\x73\xce\xdf\xb5\xc4\xcf\x3a\xc6\x65\xb3\x7a\x86\xed\x02"
            "\x15\x5b\xbb\xf1\x7d\xc2\xe7\x86\xaf\x94\x78\xfe\x08\x89\xd8\x6c"
            "\x5b\xfa\x85\xa2\x42\xeb\x08\x54\xb1\x48\x2b\x7b\xd1\x6f\x67\xf8"
            "\x0b\xef\x9c\x7a\x62\x8f\x05\xa1\x07\x93\x6a\x64\x27\x3a\x97\xb0"
            "\x08\x8b\x0e\x51\x54\x51\xf9\x16\xb5\x65\x62\x30\xa1\x2b\xa6\xdc"
            "\x78",
        .message_len = 2312 / 8,
        .digest = {0x9e3cb2aa, 0xdad7b97f, 0x0bfdfdce, 0xb15ae81a, 0xf7bf4a37,
                   0x55f7e3c4, 0x12e4ca6e},

        .digest_len = DIGEST_LEN_SHA3_224,
    },
    {
        .mode = kDifKmacModeSha3Len256,
        .message =
            "\xb1\xca\xa3\x96\x77\x1a\x09\xa1\xdb\x9b\xc2\x05\x43\xe9\x88\xe3"
            "\x59\xd4\x7c\x2a\x61\x64\x17\xbb\xca\x1b\x62\xcb\x02\x79\x6a\x88"
            "\x8f\xc6\xee\xff\x5c\x0b\x5c\x3d\x50\x62\xfc\xb4\x25\x6f\x6a\xe1"
            "\x78\x2f\x49\x2c\x1c\xf0\x36\x10\xb4\xa1\xfb\x7b\x81\x4c\x05\x78"
            "\x78\xe1\x19\x0b\x98\x35\x42\x5c\x7a\x4a\x0e\x18\x2a\xd1\xf9\x15"
            "\x35\xed\x2a\x35\x03\x3a\x5d\x8c\x67\x0e\x21\xc5\x75\xff\x43\xc1"
            "\x94\xa5\x8a\x82\xd4\xa1\xa4\x48\x81\xdd\x61\xf9\xf8\x16\x1f\xc6"
            "\xb9\x98\x86\x0c\xbe\x49\x75\x78\x0b\xe9\x3b\x6f\x87\x98\x0b\xad"
            "\x0a\x99\xaa\x2c\xb7\x55\x6b\x47\x8c\xa3\x5d\x1f\x37\x46\xc3\x3e"
            "\x2b\xb7\xc4\x7a\xf4\x26\x64\x1c\xc7\xbb\xb3\x42\x5e\x21\x44\x82"
            "\x03\x45\xe1\xd0\xea\x5b\x7d\xa2\xc3\x23\x6a\x52\x90\x6a\xcd\xc3"
            "\xb4\xd3\x4e\x47\x4d\xd7\x14\xc0\xc4\x0b\xf0\x06\xa3\xa1\xd8\x89"
            "\xa6\x32\x98\x38\x14\xbb\xc4\xa1\x4f\xe5\xf1\x59\xaa\x89\x24\x9e"
            "\x7c\x73\x8b\x3b\x73\x66\x6b\xac\x2a\x61\x5a\x83\xfd\x21\xae\x0a"
            "\x1c\xe7\x35\x2a\xde\x7b\x27\x8b\x58\x71\x58\xfd\x2f\xab\xb2\x17"
            "\xaa\x1f\xe3\x1d\x0b\xda\x53\x27\x20\x45\x59\x80\x15\xa8\xae\x4d"
            "\x8c\xec\x22\x6f\xef\xa5\x8d\xaa\x05\x50\x09\x06\xc4\xd8\x5e\x75"
            "\x67",
        .message_len = 2184 / 8,
        .digest = {0xa14856cb, 0x5b6c1cd6, 0xf896cdda, 0xde91951c, 0xdc5039bc,
                   0x5b1458f6, 0x7065998d, 0x051a88ba},
        .digest_len = DIGEST_LEN_SHA3_256,
    },
    {
        .mode = kDifKmacModeSha3Len384,
        .message =
            "\x92\xc4\x1d\x34\xbd\x24\x9c\x18\x2a\xd4\xe1\x8e\x3b\x85\x67\x70"
            "\x76\x6f\x17\x57\x20\x96\x75\x02\x0d\x4c\x1c\xf7\xb6\xf7\x68\x6c"
            "\x8c\x14\x72\x67\x8c\x7c\x41\x25\x14\xe6\x3e\xb9\xf5\xae\xe9\xf5"
            "\xc9\xd5\xcb\x8d\x87\x48\xab\x7a\x54\x65\x05\x9d\x9c\xbb\xb8\xa5"
            "\x62\x11\xff\x32\xd4\xaa\xa2\x3a\x23\xc8\x6e\xad\x91\x6f\xe2\x54"
            "\xcc\x6b\x2b\xff\x7a\x95\x53\xdf\x15\x51\xb5\x31\xf9\x5b\xb4\x1c"
            "\xbb\xc4\xac\xdd\xbd\x37\x29\x21",
        .message_len = 832 / 8,
        .digest = {0xec7e3071, 0x3ef75513, 0xd96e725b, 0x9012a1ef, 0x3681af86,
                   0x91a2304e, 0xaddf84f6, 0x4bcc93e6, 0xcbffd6c3, 0x12403b7f,
                   0xff7619a2, 0x61abdc9e},
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
// Examples generated using a custom Go program
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

static dif_kmac_t kmac;
static dif_rv_plic_t plic0;
static const uint32_t kPlicTarget = kTopEarlgreyPlicTargetIbex0;
static volatile bool fifo_empty_irq = false;
static volatile bool kmac_done_irq = false;

/**
 * KMAC interrupt handler
 *
 * Services KMAC interrupts, sets the appropriate flags that are used to
 * determine success or failure of the test.
 */
static void handle_kmac_isr(const dif_rv_plic_irq_id_t interrupt_id) {
  // NOTE: This initialization is superfluous, since the `default` case below
  // is effectively noreturn, but the compiler is unable to prove this.
  dif_kmac_irq_t kmac_irq = 0;

  switch (interrupt_id) {
    case kTopEarlgreyPlicIrqIdKmacFifoEmpty:
      kmac_irq = kDifKmacIrqFifoEmpty;
      fifo_empty_irq = true;
      break;
    case kTopEarlgreyPlicIrqIdKmacKmacDone:
      kmac_irq = kDifKmacIrqKmacDone;
      kmac_done_irq = true;
      break;
    case kTopEarlgreyPlicIrqIdKmacKmacErr:
      kmac_irq = kDifKmacIrqKmacErr;
      LOG_FATAL("KmacError!");
      test_status_set(kTestStatusFailed);
      break;
    default:
      LOG_FATAL("ISR is not implemented!");
      test_status_set(kTestStatusFailed);
  }

  CHECK_DIF_OK(dif_kmac_irq_acknowledge(&kmac, kmac_irq));
}

/**
 * External interrupt handler
 */
void ottf_external_isr(void) {
  // Claim the IRQ by reading the Ibex specific CC register.
  dif_rv_plic_irq_id_t interrupt_id = 0;

  CHECK_DIF_OK(dif_rv_plic_irq_claim(&plic0, kPlicTarget, &interrupt_id));

  // Check if the interrupted peripheral is KMAC.
  top_earlgrey_plic_peripheral_t peripheral_id =
      top_earlgrey_plic_interrupt_for_peripheral[interrupt_id];
  CHECK(peripheral_id == kTopEarlgreyPlicPeripheralKmac,
        "ISR interrupted peripheral is not KMAC!");
  handle_kmac_isr(interrupt_id);

  // Complete the IRQ by writing the IRQ source to the Ibex specific CC
  // register.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&plic0, kPlicTarget, interrupt_id));
}

/**
 * Configures all the relevant interrupts in KMAC.
 */
static void kmac_configure_irqs(dif_kmac_t *kmac) {
  CHECK_DIF_OK(
      dif_kmac_irq_set_enabled(kmac, kDifKmacIrqKmacDone, kDifToggleEnabled));
  CHECK_DIF_OK(
      dif_kmac_irq_set_enabled(kmac, kDifKmacIrqFifoEmpty, kDifToggleEnabled));
}

/**
 * Configures all the relevant interrupts in PLIC.
 */
static void plic_configure_irqs(dif_rv_plic_t *plic) {
  // Set IRQ priorities to MAX.
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(
      plic, kTopEarlgreyPlicIrqIdKmacKmacDone, kDifRvPlicMaxPriority));

  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(
      plic, kTopEarlgreyPlicIrqIdKmacFifoEmpty, kDifRvPlicMaxPriority));

  // Set Ibex IRQ priority threshold level.
  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(&plic0, kPlicTarget,
                                                kDifRvPlicMinPriority));

  // Enable IRQs in PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
      plic, kTopEarlgreyPlicIrqIdKmacKmacDone, kPlicTarget, kDifToggleEnabled));

  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(plic,
                                           kTopEarlgreyPlicIrqIdKmacFifoEmpty,
                                           kPlicTarget, kDifToggleEnabled));
}

/**
 * Feed the kmac with the message using the `dif_kmac_absorb` function.
 */
static void kmac_absorb(const char *message, size_t size) {
  dif_kmac_operation_state_t op_state;
  // Iterate the message in chunks of `BLOCK_LEN` long.
  size_t remaining = size;
  while (remaining > 0) {
    size_t len = OT_MIN(BLOCK_LEN, remaining);

    // Block the interation until the interrupt resume it.
    fifo_empty_irq = false;
    LOG_INFO("SHA3 - Absorbing %d bytes, address %p, alignment %u", len,
             message, (uintptr_t)message % sizeof(uint32_t));
    CHECK_DIF_OK(dif_kmac_absorb(&kmac, &op_state, message, len, NULL));
    remaining -= len;
    message += len;

    // If there still data to be processed, then waits for the interrupt to
    // resume the interation or a timeout stop the test.
    IBEX_SPIN_FOR((!remaining || fifo_empty_irq), TIMEOUT_US);
  }
}

/**
 * Run SHA-3 test cases using multiple blocking absorb and single squeeze
 * operations.
 */
static void run_sha3_tests(void) {
  dif_kmac_operation_state_t op_state;
  for (int i = 0; i < ARRAYSIZE(sha3_tests); ++i) {
    sha3_test_t test = sha3_tests[i];

    LOG_INFO("Test %d", i);

    CHECK_DIF_OK(dif_kmac_mode_sha3_start(&kmac, &op_state, test.mode));

    kmac_absorb(test.message, test.message_len);

    uint32_t out[DIGEST_LEN_SHA3_MAX];
    CHECK(DIGEST_LEN_SHA3_MAX >= test.digest_len);
    CHECK_DIF_OK(
        dif_kmac_squeeze(&kmac, &op_state, out, test.digest_len, NULL));

    IBEX_SPIN_FOR(kmac_done_irq, TIMEOUT_US);

    CHECK_DIF_OK(dif_kmac_end(&kmac, &op_state));

    // Check the result.
    for (int j = 0; j < test.digest_len; ++j) {
      CHECK(out[j] == test.digest[j],
            "SHA3-test %d: mismatch at %d got=0x%x want=0x%x", i, j, out[j],
            test.digest[j]);
    }
  }
}

/**
 * Run SHAKE test cases using multiple blocking absorb and single squeeze
 * operations.
 */
static void run_shake_tests(void) {
  dif_kmac_operation_state_t op_state;
  for (int i = 0; i < ARRAYSIZE(shake_tests); ++i) {
    shake_test_t test = shake_tests[i];

    CHECK_DIF_OK(dif_kmac_mode_shake_start(&kmac, &op_state, test.mode));

    kmac_absorb(test.message, test.message_len);

    uint32_t out[DIGEST_LEN_SHAKE_MAX];
    CHECK(DIGEST_LEN_SHAKE_MAX >= test.digest_len);
    CHECK_DIF_OK(
        dif_kmac_squeeze(&kmac, &op_state, out, test.digest_len, NULL));

    IBEX_SPIN_FOR(kmac_done_irq, TIMEOUT_US);

    CHECK_DIF_OK(dif_kmac_end(&kmac, &op_state));

    for (int j = 0; j < test.digest_len; ++j) {
      CHECK(out[j] == test.digest[j],
            "SHAKE-test %d: mismatch at %d got=0x%x want=0x%x", i, j, out[j],
            test.digest[j]);
    }
  }
}

bool test_main() {
  // Enable IRQs on Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  // Initialize KMAC hardware.
  CHECK_DIF_OK(
      dif_kmac_init(mmio_region_from_addr(TOP_EARLGREY_KMAC_BASE_ADDR), &kmac));

  // Initialize plic.
  mmio_region_t plic_base_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_plic_init(plic_base_addr, &plic0));

  // Configure KMAC hardware using software entropy.
  dif_kmac_config_t config = (dif_kmac_config_t){
      .entropy_mode = kDifKmacEntropyModeSoftware,
      .entropy_seed = 0xffff,
      .entropy_fast_process = kDifToggleEnabled,
  };
  CHECK_DIF_OK(dif_kmac_configure(&kmac, config));

  // Configure the interrupt `KmacIrqKmacDone` and `KmacIrqFifoEmpty`.
  kmac_configure_irqs(&kmac);
  plic_configure_irqs(&plic0);

  run_sha3_tests();
  run_shake_tests();

  return true;
}
