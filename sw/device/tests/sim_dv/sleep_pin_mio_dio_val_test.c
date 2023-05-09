// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_pwrmgr.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/pwrmgr_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/rv_plic_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"
#include "sw/device/lib/testing/autogen/isr_testutils.h"

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

typedef enum {
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
static const uint8_t kOptOutDio[kNumOptOutDio] = {kDioSpiDevClk, kDioSpiDevCsL};

typedef enum {
  kMioIoR0 = 35,
  kMioIoR2 = 37,
  kMioIoR3 = 38,
  kMioIoR4 = 39
} mio_pad_idx_t;

/**
 * If certain MIOs need to be skipped due to tied functionality, specify here.
 */
enum { kNumOptOutMio = 0 };

static uint8_t kMioPads[NUM_MIO_PADS] = {0};
static uint8_t kDioPads[NUM_DIO_PADS] = {0};

// PLIC structures
static dif_pwrmgr_t pwrmgr;
static dif_pinmux_t pinmux;
static dif_rv_plic_t plic;

static plic_isr_ctx_t plic_ctx = {.rv_plic = &plic,
                                  .hart_id = kTopEarlgreyPlicTargetIbex0};

static pwrmgr_isr_ctx_t pwrmgr_isr_ctx = {
    .pwrmgr = &pwrmgr,
    .plic_pwrmgr_start_irq_id = kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
    .expected_irq = kDifPwrmgrIrqWakeup,
    .is_only_irq = true};

/**
 * External interrupt handler.
 */
void ottf_external_isr(void) {
  dif_pwrmgr_irq_t irq_id;
  top_earlgrey_plic_peripheral_t peripheral;

  isr_testutils_pwrmgr_isr(plic_ctx, pwrmgr_isr_ctx, &peripheral, &irq_id);

  // Check that both the peripheral and the irq id is correct
  CHECK(peripheral == kTopEarlgreyPlicPeripheralPwrmgrAon,
        "IRQ peripheral: %d is incorrect", peripheral);
  CHECK(irq_id == kDifPwrmgrIrqWakeup, "IRQ ID: %d is incorrect", irq_id);
}

/** Configure pinmux retention value.
 *
 * Each gen32 can cover 16 PADs randomization. When each pad ret val draws
 * **3**, the code calls gen32_range to choose from 0 to 2.
 */
void draw_pinmux_ret(const uint32_t num_pins, uint8_t *arr,
                     const uint8_t *optout, const uint8_t num_optout) {
  for (uint32_t i = 0; i < num_pins; i += 16) {
    uint32_t val = rand_testutils_gen32();
    uint32_t min_idx = (i + 16 < num_pins) ? i + 16 : num_pins;

    for (uint32_t j = i; j < min_idx; j++) {
      /* Bit slice 2b at a time and if it is 3, redraw */
      arr[j] = (val >> ((j & 0xF) * 2)) & 0x3;
      if (arr[j] == 3) {
        arr[j] = (uint8_t)rand_testutils_gen32_range(0, 2);
      }
    }
  }

  // OptOut processing after draw.
  for (int i = 0; i < num_optout; i++) {
    CHECK(optout != NULL, "optout must be non-NULL");
    arr[optout[i]] = 2;  // High-Z always
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
  for (int i = 0; i < NUM_MIO_PADS; ++i) {
    LOG_INFO("MIO [%d]: %x", i, kMioPads[i]);
  }
  for (int i = 0; i < NUM_DIO_PADS; ++i) {
    LOG_INFO("DIO [%d]: %x", i, kDioPads[i]);
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

bool lowpower_prep(dif_pwrmgr_t *pwrmgr, dif_pinmux_t *pinmux, bool deepsleep) {
  bool result = false;
  dif_pwrmgr_domain_config_t pwrmgr_domain_cfg = 0;

  LOG_INFO("Selecting PADs retention modes...");

  draw_pinmux_ret(NUM_DIO_PADS, kDioPads, kOptOutDio, kNumOptOutDio);
  draw_pinmux_ret(NUM_MIO_PADS, kMioPads, NULL, kNumOptOutMio);

  print_chosen_values();

  // Configure pwrmgr to deep powerdown.
  configure_pad_retention_types(pinmux);

  if (!deepsleep) {
    pwrmgr_domain_cfg = kDifPwrmgrDomainOptionMainPowerInLowPower |
                        kDifPwrmgrDomainOptionUsbClockInActivePower;
  }
  CHECK_DIF_OK(dif_pwrmgr_set_domain_config(pwrmgr, pwrmgr_domain_cfg,
                                            kDifToggleEnabled));
  CHECK_DIF_OK(dif_pwrmgr_low_power_set_enabled(pwrmgr, kDifToggleEnabled,
                                                kDifToggleEnabled));

  wait_for_interrupt();  // Entering deep power down.

  return result;
}

bool test_main(void) {
  bool result = false;

  // Enable global and external IRQ at Ibex.
  irq_global_ctrl(true);
  irq_external_ctrl(true);

  CHECK_DIF_OK(dif_pwrmgr_init(
      mmio_region_from_addr(TOP_EARLGREY_PWRMGR_AON_BASE_ADDR), &pwrmgr));
  CHECK_DIF_OK(dif_pinmux_init(
      mmio_region_from_addr(TOP_EARLGREY_PINMUX_AON_BASE_ADDR), &pinmux));
  CHECK_DIF_OK(dif_rv_plic_init(
      mmio_region_from_addr(TOP_EARLGREY_RV_PLIC_BASE_ADDR), &plic));

  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(&pwrmgr, 0)) == true) {
    uint32_t deep_powerdown_en = rand_testutils_gen32_range(0, 1);
    bool deepsleep = (deep_powerdown_en) ? true : false;

    // TODO(lowrisc/opentitan#15889): The weak pull on IOC3 needs to be
    // disabled for this test. Remove this later.
    dif_pinmux_pad_attr_t out_attr;
    dif_pinmux_pad_attr_t in_attr = {0};
    CHECK_DIF_OK(dif_pinmux_pad_write_attrs(&pinmux, kTopEarlgreyMuxedPadsIoc3,
                                            kDifPinmuxPadKindMio, in_attr,
                                            &out_attr));

    if (!deepsleep) {
      // Enable all the AON interrupts used in this test.
      rv_plic_testutils_irq_range_enable(&plic, kTopEarlgreyPlicTargetIbex0,
                                         kTopEarlgreyPlicIrqIdPwrmgrAonWakeup,
                                         kTopEarlgreyPlicIrqIdPwrmgrAonWakeup);
      // Enable pwrmgr interrupt
      CHECK_DIF_OK(dif_pwrmgr_irq_set_enabled(&pwrmgr, 0, kDifToggleEnabled));
    }

    result = lowpower_prep(&pwrmgr, &pinmux, deepsleep);
  }

  if (UNWRAP(pwrmgr_testutils_is_wakeup_reason(
          &pwrmgr, kDifPwrmgrWakeupRequestSourceThree)) == true) {
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
