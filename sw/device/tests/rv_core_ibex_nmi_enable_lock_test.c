// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Verifies that the NMI enables can be cleared again and that
// NMI_ENABLE_REGWEN locks them. A watchdog bark checks that the enable
// actually gates the NMI.

#include <stdbool.h>
#include <stdint.h>

#include "hw/top/dt/aon_timer.h"     // Generated
#include "hw/top/dt/rv_core_ibex.h"  // Generated
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_aon_timer.h"
#include "sw/device/lib/dif/dif_rv_core_ibex.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/aon_timer_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top/rv_core_ibex_regs.h"  // Generated

OTTF_DEFINE_TEST_CONFIG();

enum {
  kWdogBarkMicros = 200,
  // Time to wait for an NMI after the bark has been recorded in NMI_STATE.
  kNmiLatencyMicros = 10,
};

static dif_rv_core_ibex_t rv_core_ibex;
static dif_aon_timer_t aon_timer;

static volatile bool nmi_fired;

static void wdog_stop_and_ack(void) {
  CHECK_DIF_OK(dif_aon_timer_watchdog_stop(&aon_timer));
  CHECK_DIF_OK(
      dif_aon_timer_irq_acknowledge(&aon_timer, kDifAonTimerIrqWdogTimerBark));
  CHECK_DIF_OK(dif_rv_core_ibex_clear_nmi_state(&rv_core_ibex,
                                                kDifRvCoreIbexNmiSourceWdog));
}

/**
 * OTTF external NMI handler, overrides the OTTF weak definition.
 */
void ottf_external_nmi_handler(uint32_t *exc_info) {
  nmi_fired = true;
  wdog_stop_and_ack();
}

static bool wdog_barked(void) {
  dif_rv_core_ibex_nmi_state_t nmi_state;
  CHECK_DIF_OK(dif_rv_core_ibex_get_nmi_state(&rv_core_ibex, &nmi_state));
  return nmi_state.wdog_barked;
}

/**
 * Lets the watchdog bark and returns whether the bark raised an NMI.
 */
static bool wdog_bark_raises_nmi(void) {
  nmi_fired = false;

  uint32_t bark_cycles = 0;
  CHECK_STATUS_OK(aon_timer_testutils_get_aon_cycles_32_from_us(kWdogBarkMicros,
                                                                &bark_cycles));
  CHECK_STATUS_OK(aon_timer_testutils_watchdog_config(
      &aon_timer, /*bark_cycles=*/bark_cycles, /*bite_cycles=*/UINT32_MAX,
      /*pause_in_sleep=*/false));

  // The NMI handler clears NMI_STATE, so it only stays set if the NMI is
  // disabled.
  IBEX_SPIN_FOR(nmi_fired || wdog_barked(), kWdogBarkMicros * 2);
  busy_spin_micros(kNmiLatencyMicros);

  bool fired = nmi_fired;
  if (!fired) {
    wdog_stop_and_ack();
  }
  return fired;
}

static uint32_t nmi_enable_read(void) {
  return mmio_region_read32(rv_core_ibex.base_addr,
                            RV_CORE_IBEX_NMI_ENABLE_REG_OFFSET);
}

static uint32_t nmi_enable_regwen_read(void) {
  return mmio_region_read32(rv_core_ibex.base_addr,
                            RV_CORE_IBEX_NMI_ENABLE_REGWEN_REG_OFFSET);
}

bool test_main(void) {
  // The NMI does not depend on the global or external interrupt enables.
  irq_global_ctrl(false);
  irq_external_ctrl(false);

  CHECK_DIF_OK(dif_rv_core_ibex_init_from_dt(kDtRvCoreIbex, &rv_core_ibex));
  CHECK_DIF_OK(dif_aon_timer_init_from_dt(kDtAonTimer, &aon_timer));

  // Start from a known state, the ROM may have enabled the watchdog NMI.
  CHECK_DIF_OK(
      dif_rv_core_ibex_disable_nmi(&rv_core_ibex, kDifRvCoreIbexNmiSourceAll));
  CHECK(nmi_enable_read() == 0, "NMI_ENABLE should be 0, got 0x%x",
        nmi_enable_read());

  LOG_INFO("Bark with the watchdog NMI enabled");
  CHECK_DIF_OK(
      dif_rv_core_ibex_enable_nmi(&rv_core_ibex, kDifRvCoreIbexNmiSourceWdog));
  CHECK(wdog_bark_raises_nmi(), "Enabled watchdog NMI did not fire");

  LOG_INFO("Bark with the watchdog NMI disabled");
  CHECK_DIF_OK(
      dif_rv_core_ibex_disable_nmi(&rv_core_ibex, kDifRvCoreIbexNmiSourceWdog));
  CHECK(nmi_enable_read() == 0, "NMI_ENABLE should be 0, got 0x%x",
        nmi_enable_read());
  CHECK(!wdog_bark_raises_nmi(), "Disabled watchdog NMI fired");

  LOG_INFO("Bark with the watchdog NMI enabled again");
  CHECK_DIF_OK(
      dif_rv_core_ibex_enable_nmi(&rv_core_ibex, kDifRvCoreIbexNmiSourceWdog));
  CHECK(wdog_bark_raises_nmi(), "Re-enabled watchdog NMI did not fire");

  LOG_INFO("Lock NMI_ENABLE");
  CHECK_DIF_OK(dif_rv_core_ibex_lock_nmi_enable(&rv_core_ibex));
  CHECK(nmi_enable_regwen_read() == 0,
        "NMI_ENABLE_REGWEN should be 0 after locking, got 0x%x",
        nmi_enable_regwen_read());

  // Writing 1 to NMI_ENABLE_REGWEN does not unlock it again.
  mmio_region_write32(rv_core_ibex.base_addr,
                      RV_CORE_IBEX_NMI_ENABLE_REGWEN_REG_OFFSET, 1);
  CHECK(nmi_enable_regwen_read() == 0,
        "NMI_ENABLE_REGWEN should stay 0, got 0x%x", nmi_enable_regwen_read());

  // Neither disabling nor enabling a source has an effect once locked.
  CHECK(dif_rv_core_ibex_disable_nmi(&rv_core_ibex,
                                     kDifRvCoreIbexNmiSourceWdog) == kDifLocked,
        "Disabling a locked NMI should return kDifLocked");
  CHECK(dif_rv_core_ibex_enable_nmi(&rv_core_ibex,
                                    kDifRvCoreIbexNmiSourceAlert) == kDifLocked,
        "Enabling a locked NMI should return kDifLocked");
  CHECK(nmi_enable_read() == 1u << RV_CORE_IBEX_NMI_ENABLE_WDOG_EN_BIT,
        "Locked NMI_ENABLE changed to 0x%x", nmi_enable_read());

  LOG_INFO("Bark with the watchdog NMI locked enabled");
  CHECK(wdog_bark_raises_nmi(), "Locked watchdog NMI did not fire");

  return true;
}
