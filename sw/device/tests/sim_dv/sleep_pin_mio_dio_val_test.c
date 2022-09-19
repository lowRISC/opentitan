// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

OTTF_DEFINE_TEST_CONFIG();

/**
 * Test: chip_sw_sleep_pin_mio_dio_val
 *
 * chip_sw_sleep_pin_mio_dio_val test is to check the PADs assert desired
 * values. When the chip enters deep powerdown (turning off power domains
 * except AON), PADs cannot get the data from off domain logics.
 *
 * To not confuse the devices outside of the logic, usually isolation cells are
 * placed in between (off and on). OpenTitan, on top of the isolation, provides
 * a functionality to control the PADs output value among **0**, **1**,
 * **High-Z**, and **Passthrough**. Refer the PINMUX technical specification
 * for the details.
 *
 * In this test, the code randomizes the output values except the
 * **passthrough**, as **passthrough** is tested in other chip level test. Then
 * the chosen values are given to the UVM testbenches. UVM testbenches compare
 * the expected and measured values.
 */

/* NUM_MIO_PADS */
/* NUM_DIO_PADS */

/* DioOptOut: Some of DIO PADs are input only or does not need to be tested as
 * they are alive in deep powerdown state. This lists out the PADs. Its entry
 * is the index of DIOs.
 *
 * ```systemverilog
 * localparam chip_io_e DioPads [NumDioPads] = '{
 *   UsbP,       // DIO 0                INOUT
 *   UsbN,       // DIO 1                INOUT
 *   SpiHostD0,  // DIO 2                INOUT
 *   SpiHostD1,  // DIO 3                INOUT
 *   SpiHostD2,  // DIO 4                INOUT
 *   SpiHostD3,  // DIO 5                INOUT
 *   SpiDevD0,   // DIO 6                INOUT
 *   SpiDevD1,   // DIO 7                INOUT
 *   SpiDevD2,   // DIO 8                INOUT
 *   SpiDevD3,   // DIO 9                INOUT
 *   IoR8,       // DIO 10 EC_RST_L      INOUT
 *   IoR9,       // DIO 11 FLASH_WP_L    INOUT
 *   SpiDevClk,  // DIO 12               INPUT
 *   SpiDevCsL,  // DIO 13               INPUT
 *   SpiHostClk, // DIO 14               OUTPUT
 *   SpiHostCsL  // DIO 15               OUTPUT
 * }
 * ```
 */

typedef enum uint8_t {
  kDioUsbP,       /* DIO 0                INOUT  */
  kDioUsbN,       /* DIO 1                INOUT  */
  kDioSpiHostD0,  /* DIO 2                INOUT  */
  kDioSpiHostD1,  /* DIO 3                INOUT  */
  kDioSpiHostD2,  /* DIO 4                INOUT  */
  kDioSpiHostD3,  /* DIO 5                INOUT  */
  kDioSpiDevD0,   /* DIO 6                INOUT  */
  kDioSpiDevD1,   /* DIO 7                INOUT  */
  kDioSpiDevD2,   /* DIO 8                INOUT  */
  kDioSpiDevD3,   /* DIO 9                INOUT  */
  kDioIoR8,       /* DIO 10 EC_RST_L      INOUT  */
  kDioIoR9,       /* DIO 11 FLASH_WP_L    INOUT  */
  kDioSpiDevClk,  /* DIO 12               INPUT  */
  kDioSpiDevCsL,  /* DIO 13               INPUT  */
  kDioSpiHostClk, /* DIO 14               OUTPUT */
  kDioSpiHostCsL  /* DIO 15               OUTPUT */
} dio_pad_idx_t;

enum { kNumOptOutDio = 2 };
static const uint8_t kOptOutDio[kNumOptOutDio] = {kDioSpiDevClk,
                                                  kDioSpiDevCsL};

static uint8_t kMioPads[NUM_MIO_PADS] = {0};
static uint8_t kDioPads[NUM_DIO_PADS] = {0};

/** Configure pinmux retention value.
 *
 * Each gen32 can cover 16 PADs randomization. When each pad ret val draws
 * **3**, the code calls gen32_range to choose from 0 to 2.
 */
void draw_pinmux_ret(const uint32_t num_pins, uint8_t *arr) {
  for (int i = 0; i < num_pins; i += 16) {
    uint32_t val = rand_testutils_gen32();
    uint32_t min_idx = (i + 16 < num_pins) ? i + 16 : num_pins;

    for (int j = i; j < min_idx; j++) {
      /* Bit slice 2b at a time and if it is 3, redraw */
      arr[j] = (val >> ((j & 0xF) * 2)) & 0x3;
      if (arr[j] == 3) {
        arr[j] = (uint8_t)rand_testutils_gen32_range(0, 2);
      }
    }
  }
}

/**
 * Send the chosen values to UVM tb.
 *
 * Format:
 *
 *     "{DIO/MIO} [i]: {}"
 */
void print_chosen_values(void) {
  LOG_INFO("BEGIN Chosen Retention Types");
  for (int io = 0; io < 2; io++) {
    int max_pads = (io) ? NUM_DIO_PADS : NUM_MIO_PADS;
    for (int i = 0; i < max_pads; i++) {
      if (io == 1) {
        // DIO
        LOG_INFO("DIO [%d]: %x", i, kDioPads[i]);
      } else {
        // MIO
        LOG_INFO("MIO [%d]: %x", i, kMioPads[i]);
      }
    }
  }
  LOG_INFO("END Chosen Retention Types");
}

/**
 * Configure PADs retention types.
 *
 * @param pinmux Pinmux handle.
 */
void configure_pad_retention_types(dif_pinmux_t *pinmux) {
  uint8_t io;  // 1 for DIO, 0 for MIO
  uint32_t max_pads;
  dif_pinmux_pad_kind_t pad_kind;
  dif_pinmux_sleep_mode_t pad_mode;
  LOG_INFO("Configuring PADs retention types in PINMUX...");

  // TODO: for loop of writing values to PINMUX CSRs.
  for (io = 0; io < 2; io++) {
    max_pads = (io) ? NUM_DIO_PADS : NUM_MIO_PADS;
    pad_kind = (io) ? kDifPinmuxPadKindDio : kDifPinmuxPadKindMio;
    for (int i = 0; i < max_pads; i++) {
      pad_mode = (io) ? (dif_pinmux_sleep_mode_t)(kDioPads[i])
                      : (dif_pinmux_sleep_mode_t)(kMioPads[i]);
      CHECK_DIF_OK(dif_pinmux_pad_sleep_enable(pinmux, (dif_pinmux_index_t)i,
                                               pad_kind, pad_mode));
    }
  }

  LOG_INFO("PADs retention modes are configured.");
}

bool lowpower_prep(dif_pwrmgr_t *pwrmgr, dif_pinmux_t *pinmux) {
  bool result = false;
  dif_pwrmgr_domain_config_t pwrmgr_domain_cfg;

  LOG_INFO("Selecting PADs retention modes...");

  draw_pinmux_ret(NUM_DIO_PADS, kDioPads);
  draw_pinmux_ret(NUM_MIO_PADS, kMioPads);

  print_chosen_values();

  // Configure pwrmgr to deep powerdown.
  configure_pad_retention_types(pinmux);

  CHECK_DIF_OK(dif_pwrmgr_set_domain_config(pwrmgr, pwrmgr_domain_cfg,
                                            kDifToggleEnabled));
  CHECK_DIF_OK(dif_pwrmgr_low_power_set_enabled(pwrmgr, kDifToggleEnabled,
                                                kDifToggleEnabled));

  wait_for_interrupt();  // Entering deep power down.

  return result;
}

bool test_main(void) {
  dif_pwrmgr_t pwrmgr;
  dif_pinmux_t pinmux;

  bool result = false;

  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));

  if (pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) {
    result = lowpower_prep(&pwrmgr, &pinmux);

  } else if (pwrmgr_testutils_is_wakeup_reason(
                 &pwrmgr, kDifPwrmgrWakeupRequestSourceThree)) {
    // TODO: change PINMUX wakeup, not pin detector
    /**
     *  Usually this part won't be hit. UVM testbench checks the PAD output
     *  values and raises an error if failed.
     */
  } else {
    // Other wakeup. This is a failure.
    dif_pwrmgr_wakeup_reason_t wakeup_reason;
    CHECK_DIF_OK(dif_pwrmgr_wakeup_reason_get(&pwrmgr, &wakeup_reason));
    LOG_ERROR("Unexpected wakeup detected: type = %d, request_source = %d",
              wakeup_reason.types, wakeup_reason.request_sources);
    result = false;
  }

  return result;
}
