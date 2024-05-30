// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_otbn.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/otbn_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

typedef dif_result_t (*otbn_read_t)(const dif_otbn_t *otbn,
                                    uint32_t offset_bytes, void *dest,
                                    size_t len_bytes);

typedef dif_result_t (*otbn_write_t)(const dif_otbn_t *otbn,
                                     uint32_t offset_bytes, const void *src,
                                     size_t len_bytes);

enum {
  /**
   * Number of distinct addresses to check in each IMEM and DMEM.
   */
  kNumAddrs = 50,

  /**
   * Minimum number of expected integrity errors in IMEM and DMEM after
   * re-scrambling.
   * Note that there are `2^32` valid code words and that each non-valid code
   * word triggers an error. Therefore, the probability that a random 39-bit
   * word triggers an error is: `(2^39 - 2^32)/ 2^39 = 127/128`. Then the
   * probability that all `kNumAddrs` triggers an errors is
   * `(127/128)^kNumAddrs` after re-scrambling.
   *
   * The Generic formula:
   *               (w-i)
   *             127
   * Pr(i) =  -------- x (w choose i)
   *                w
   *             128
   * Where:
   *      w = The number of words tested.
   *      i = The number of words that may not generate errors.
   *      Pr(i) = Probability that i words will not generate an ECC error.
   *
   * So for i in (0..4):
   *
   * ``` Python
   * from math import comb
   * w = 50
   * t = 0
   * for i in range(5):
   *    p = ((127**(w-i))/(128**w)) * comb(w,i)
   *    t += p
   *    print(f'Pr({i}): { round(p, 4)},\tsum{{Pr(0-{i})}}: {round(t, 6)}')
   * ```
   * ```
   * Pr(0): 0.6756,   sum{Pr(0-0)}: 0.675597
   * Pr(1): 0.266,    sum{Pr(0-1)}: 0.94158
   * Pr(2): 0.0513,   sum{Pr(0-2)}: 0.992891
   * Pr(3): 0.0065,   sum{Pr(0-3)}: 0.999356
   * Pr(4): 0.0006,   sum{Pr(0-4)}: 0.999954
   * ```
   * So by choosing `(kNumAddrs - 2) = 48` as the threshold we will have a
   * probability of `1 - 0.992891 = 0.71%` that this test will fail randomly due
   * to ECC errors not being generated. That seems a reasonable number.
   */
  kNumIntgErrorsThreshold = kNumAddrs - 2,
};
static_assert(kNumAddrs == 50,
              "kNumAddrs changed, so kEccErrorProbability should be "
              "computed again");

static volatile bool has_irq_fired;

/**
 * This overrides the default OTTF load integrity handler.
 */
void ottf_load_integrity_error_handler(uint32_t *exc_info) {
  OT_DISCARD(exc_info);
  has_irq_fired = true;
}

/**
 * Get `num` distinct random numbers in the range [0, `max`] from
 * RV_CORE_IBEX_RND_DATA.
 *
 * @param ibex The Ibex DIF object.
 * @param num The number of random numbers to get.
 * @param[out] rnd_buf Pointer to the buffer to write the random numbers to.
 * @param max The maximum random value returned.
 */
static void get_rand_words(dif_rv_core_ibex_t *ibex, int num, uint32_t *rnd_buf,
                           uint32_t max) {
  uint32_t rnd_word;
  for (int i = 0; i < num; ++i) {
    bool found = false;
    while (found == false) {
      // Get a new random number.
      CHECK_DIF_OK(dif_rv_core_ibex_read_rnd_data(ibex, &rnd_word));
      rnd_word = rnd_word % max;
      // Check if the number is unique.
      found = true;
      for (int j = 0; j < i; ++j) {
        if (rnd_buf[j] == rnd_word) {
          // Start over.
          found = false;
          break;
        }
      }
    }
    // Add the number to the buffer.
    rnd_buf[i] = rnd_word;
  }
}

/**
 * Write values found at `word_addrs` to OTBN memory at addresses `word_addrs`.
 *
 * @param ctx The otbn context object.
 * @param num The number of addresses to write.
 * @param word_addrs The data to write and the word addresses to write to.
 * @param otbn_write Pointer to the function to write the memory. It can be
 *                   either `dif_otbn_imem_write` or `dif_otbn_dmem_write`.
 */
static void otbn_write_mem_words(const dif_otbn_t *otbn, const int num,
                                 const uint32_t *word_addrs,
                                 otbn_write_t otbn_write) {
  for (int i = 0; i < num; ++i) {
    otbn_write(otbn, word_addrs[i] * sizeof(uint32_t), (void *)&word_addrs[i],
               sizeof(uint32_t));
  }
}

/**
 * Check whether the contents at addresses `word_addrs` of an OTBN memory match
 * the reference data pointed at `word_addrs`.
 *
 * @param ctx The otbn context object.
 * @param num The number of addresses to check.
 * @param word_addrs The word addresses to check.
 * @param otbn_read Pointer to the function to read the memory. It can be
 *                  either `dif_otbn_imem_read` or `dif_otbn_dmem_read`.
 * @param[out] num_matches Pointer to the number of observed matches.
 * @param[out] num_intg_errors Pointer to the number of observed integrity
 *             errors.
 */
static void otbn_check_mem_words(const dif_otbn_t *otbn, const int num,
                                 const uint32_t *word_addrs,
                                 otbn_read_t otbn_read, int *num_matches,
                                 int *num_intg_errors) {
  *num_matches = 0;
  *num_intg_errors = 0;

  uint32_t word;
  bool match;
  for (int i = 0; i < num; ++i) {
    // If the memory has been scrambled we expect to receive an IRQ due to the
    // integrity error.
    has_irq_fired = false;
    otbn_read(otbn, word_addrs[i] * sizeof(uint32_t), (void *)&word,
              sizeof(uint32_t));
    match = (word_addrs[i] == word);
    if (match) {
      *num_matches += 1;
    }
    if (has_irq_fired) {
      *num_intg_errors += 1;
    }
    // It is possible that the integrity bits after re-scrambling are still
    // valid.
    if ((match == false) && (has_irq_fired == false)) {
      LOG_INFO(
          "Mismatch without integrity error: Entry %i, address 0x%x, "
          "data 0x%x",
          i, word_addrs[i], word);
    }
  }
}

bool test_main(void) {
  // Init OTBN DIF.
  dif_otbn_t otbn;
  mmio_region_t otbn_addr = mmio_region_from_addr(TOP_EARLGREY_OTBN_BASE_ADDR);
  CHECK_DIF_OK(dif_otbn_init(otbn_addr, &otbn));

  // Init Ibex DIF.
  dif_rv_core_ibex_t ibex;
  mmio_region_t ibex_addr =
      mmio_region_from_addr(TOP_EARLGREY_RV_CORE_IBEX_CFG_BASE_ADDR);
  CHECK_DIF_OK(dif_rv_core_ibex_init(ibex_addr, &ibex));

  uint32_t imem_offsets[kNumAddrs];
  uint32_t dmem_offsets[kNumAddrs];
  uint32_t max;
  int num_matches_imem, num_intg_errors_imem;
  int num_matches_dmem, num_intg_errors_dmem;

  // Get random address offsets to check.
  max = (uint32_t)dif_otbn_get_imem_size_bytes(&otbn) / sizeof(uint32_t) - 1;
  get_rand_words(&ibex, kNumAddrs, imem_offsets, max);
  max = (uint32_t)dif_otbn_get_dmem_size_bytes(&otbn) / sizeof(uint32_t) - 1;
  get_rand_words(&ibex, kNumAddrs, dmem_offsets, max);

  // Wait for OTBN to be idle.
  CHECK_STATUS_OK(otbn_testutils_wait_for_done(&otbn, kDifOtbnErrBitsNoError));

  // Write random address offsets.
  otbn_write_mem_words(&otbn, kNumAddrs, imem_offsets, dif_otbn_imem_write);
  otbn_write_mem_words(&otbn, kNumAddrs, dmem_offsets, dif_otbn_dmem_write);

  // Read back and check random address offsets. All values must match, we must
  // not see any integrity errors.
  otbn_check_mem_words(&otbn, kNumAddrs, imem_offsets, dif_otbn_imem_read,
                       &num_matches_imem, &num_intg_errors_imem);
  CHECK(num_matches_imem == kNumAddrs, "%i unexpected IMEM mismatches",
        kNumAddrs - num_matches_imem);
  CHECK(!num_intg_errors_imem, "%i unexpected IMEM integrity errors",
        num_intg_errors_imem);

  otbn_check_mem_words(&otbn, kNumAddrs, dmem_offsets, dif_otbn_dmem_read,
                       &num_matches_dmem, &num_intg_errors_dmem);
  CHECK(num_matches_dmem == kNumAddrs, "%i unexpected DMEM mismatches",
        kNumAddrs - num_matches_dmem);
  CHECK(!num_intg_errors_dmem, "%i unexpected DMEM integrity errors",
        num_intg_errors_dmem);

  // Re-scramble IMEM and DMEM by fetching new scrambling keys from OTP.
  CHECK_DIF_OK(dif_otbn_write_cmd(&otbn, kDifOtbnCmdSecWipeImem));
  CHECK_STATUS_OK(otbn_testutils_wait_for_done(&otbn, kDifOtbnErrBitsNoError));
  CHECK_DIF_OK(dif_otbn_write_cmd(&otbn, kDifOtbnCmdSecWipeDmem));
  CHECK_STATUS_OK(otbn_testutils_wait_for_done(&otbn, kDifOtbnErrBitsNoError));

  // Read back and check random address offsets. We don't care about the values.
  // "Most" reads should trigger integrity errors.
  otbn_check_mem_words(&otbn, kNumAddrs, imem_offsets, dif_otbn_imem_read,
                       &num_matches_imem, &num_intg_errors_imem);
  CHECK(num_intg_errors_imem >= kNumIntgErrorsThreshold,
        "Expecting at least %i IMEM integrity errors, got %i",
        kNumIntgErrorsThreshold, num_intg_errors_imem);
  otbn_check_mem_words(&otbn, kNumAddrs, dmem_offsets, dif_otbn_dmem_read,
                       &num_matches_dmem, &num_intg_errors_dmem);
  CHECK(num_intg_errors_dmem >= kNumIntgErrorsThreshold,
        "Expecting at least %i DMEM integrity errors, got %i",
        kNumIntgErrorsThreshold, num_intg_errors_dmem);

  return true;
}
