// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/freestanding/limits.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_rv_timer.h"
#include "sw/device/lib/flash_ctrl.h"
#include "sw/device/lib/ibex_peri.h"
#include "sw/device/lib/irq.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/ottf.h"
#include "sw/device/lib/testing/test_framework/test_status.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

/**
 * Basic logging macro to log a buffer in hex format.
 *
 * @param severity a severity of type `log_severity_t`.
 * @param buffer a buffer to the data which will be logged in hex
 * @param size  the size of the \p buffer.
 */
#include "sw/device/lib/runtime/print.h"
#define LOG_HEX(input, size)                                          \
  do {                                                                \
    char log_buffer[200];                                             \
    uint8_t *p = (uint8_t *)input;                                    \
    size_t bytes_left = sizeof(log_buffer);                           \
    for (int i = 0; i < size; i++) {                                  \
      bytes_left -=                                                   \
          base_snprintf(&log_buffer[sizeof(log_buffer) - bytes_left], \
                        bytes_left, "%02X ", p[i]);                   \
    }                                                                 \
    log_buffer[sizeof(log_buffer) - bytes_left] = 0;                  \
    LOG_INFO("%s", log_buffer);                                       \
  } while (false)

#define CHECK_EQZ(x)                      \
  do {                                    \
    int res = 0;                          \
    CHECK((res = x) == 0, "Res=%d", res); \
  } while (false)

#define CHECK_ARRAYS_EQ(xs, ys, len) \
  do {                               \
    uint8_t *xs_ = (xs);             \
    uint8_t *ys_ = (ys);             \
    size_t len_ = (len);             \
    for (int i = 0; i < len_; i++) { \
      CHECK(xs_[i] == ys_[i]);       \
    }                                \
  } while (false)

#define CHECK_STR_EQ(xs, ys)                         \
  do {                                               \
    for (int i = 0; xs[i] != 0 || ys[i] != 0; i++) { \
      CHECK(xs[i] == ys[i], "%s != %s", xs, ys);     \
    }                                                \
  } while (false)

typedef int (*get_version_t)(uint8_t *, uint32_t);
extern int get_version_1(uint8_t *ver, uint32_t size);
extern int get_version_1_size;
extern int get_version_2(uint8_t *ver, uint32_t size);
extern int get_version_2_size;

struct test_memory_region {
  uint32_t address;
  size_t size;
};

const test_config_t kTestConfig;
static const struct test_memory_region kPhysical_slot[2] = {
    {.address = 0x20010000, .size = 0x10000},
    {.address = 0x20020000, .size = 0x10000}};
static const struct test_memory_region kExecution_slot = {.address = 0xE0010000,
                                                          .size = 0x10000};

static size_t words_per_page;
static size_t word_sz;
static size_t page_sz;
static size_t pages_per_bank;
static size_t bank_sz;

static void flash_initialize(void) {
  flash_init_block();
  flash_cfg_bank_erase(FLASH_BANK_0, /*erase_en=*/true);
  flash_cfg_bank_erase(FLASH_BANK_1, /*erase_en=*/true);

  // setup default access for data partition
  flash_default_region_access(/*rd_en=*/true, /*prog_en=*/true,
                              /*erase_en=*/true);

  words_per_page = flash_get_words_per_page();
  word_sz = flash_get_word_size();
  page_sz = flash_get_page_size();
  pages_per_bank = flash_get_pages_per_bank();
  bank_sz = flash_get_bank_size();

  // also setup data region to enable scrambling
  mp_region_t data_region = {.num = 0x0,
                             .base = pages_per_bank,
                             .size = 0x1,
                             .part = kDataPartition,
                             .rd_en = true,
                             .prog_en = true,
                             .erase_en = true,
                             .ecc_en = true,
                             .scramble_en = true};
  flash_cfg_region(&data_region);
}

static void function_to_flash_copy(uint32_t dest, void *func, size_t size) {
  // Attempt to live-program an entire page, where the overall
  // payload is much larger than the internal flash FIFO.
  CHECK_EQZ(dest % page_sz);
  CHECK_EQZ(flash_page_erase(dest, kDataPartition));
  CHECK_EQZ(flash_write(dest, kDataPartition, func, size));
  CHECK_ARRAYS_EQ((void *)dest, func, size);
}

/**
 * Execute the functions received in the first argument ans compare the result
 * with the second argument.
 */
static void function_execute(get_version_t get_version, char *expected_result) {
  uint8_t buffer[64] = {
      0x00,
  };

  LOG_INFO("Running function on address: %p", get_version);
  CHECK_EQZ(get_version(buffer, sizeof(buffer)));
  CHECK_STR_EQ(buffer, expected_result);
}

bool test_main(void) {
  char *str_v1 = "V.1.23.12";
  char *str_v2 = "V.2.00.00";

  flash_initialize();

  // Execute the original functions on the addresses chosen by the linker.
  function_execute(get_version_1, /*expected_result=*/str_v1);
  function_execute(get_version_2, /*expected_result=*/str_v2);

  // Copy the function 1 to the first physical slot and execute it by the
  // physical address.
  function_to_flash_copy(kPhysical_slot[0].address, get_version_1,
                         get_version_1_size);
  function_execute((get_version_t)kPhysical_slot[0].address,
                   /*expected_result=*/str_v1);

  // Copy the function2 to the second physical slot and execute it by the
  // physical address.
  function_to_flash_copy(kPhysical_slot[1].address, get_version_2,
                         get_version_1_size);
  function_execute((get_version_t)kPhysical_slot[1].address,
                   /*expected_result=*/str_v2);

  // Map the physical address of the first slot to the virtual execution address
  // and execute it by the virtual address.
  CHECK_EQZ(ibex_set_translation(
      ibex_simple_address_translation_id_1, kExecution_slot.address,
      kPhysical_slot[0].size, kPhysical_slot[0].address));
  function_execute((get_version_t)kExecution_slot.address,
                   /*expected_result=*/str_v1);

  // Map the physical address of the second slot to the virtual execution
  // address and execute it by the virtual address.
  CHECK_EQZ(ibex_set_translation(
      ibex_simple_address_translation_id_1, kExecution_slot.address,
      kPhysical_slot[1].size, kPhysical_slot[1].address));
  function_execute((get_version_t)kExecution_slot.address,
                   /*expected_result=*/str_v2);

  return true;
}
