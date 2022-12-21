// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/usb_testutils_diags.h"

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/check.h"

#if USBUTILS_FUNCTION_POINTS && USBUTILS_FUNCPT_USE_BUFFER
/**
 * Filenames of source files employing function points; must be kept consistent
 * with the USBUTILS_FUNCPT_FILE_ definitions
 */
static const char *funcpt_file[] = {"<nil>",
                                    "dif_usbdev.c",
                                    "usb_testutils.c",
                                    "usb_testutils_controlep.c",
                                    "usb_tesutils_simpleserial.c",
                                    "usbdev_test.c",
                                    "usbdev_stream_test.c"};

/**
 * Function point buffer
 */

volatile unsigned usbutils_fpt_next;
uint32_t usbutils_fpt_log[USBUTILS_FUNCPT_LOG_SIZE];

/**
 * Report contents of the function point buffer
 */
void usbutils_funcpt_report(void) {
  // Locate the oldest entry in the buffer
  uint32_t oldest_time = ~0U;
  unsigned oldest_idx = ~0U;
  unsigned idx = 0U;
  while (idx < USBUTILS_FUNCPT_LOG_SIZE) {
    if (usbutils_fpt_log[idx] == USBUTILS_FUNCPT_ENTRY_SIGNATURE) {
      uint32_t time = usbutils_fpt_log[idx + 1U];
      if (time < oldest_time) {
        oldest_time = time;
        oldest_idx = idx;
      }
    }
    idx += 4U;
  }

  // Report the valid entries
  if (oldest_idx == ~0U) {
    LOG_INFO("No function points recorded");
  } else {
    idx = oldest_idx;
    do {
      if (usbutils_fpt_log[idx] == USBUTILS_FUNCPT_ENTRY_SIGNATURE) {
        const char *file = funcpt_file[usbutils_fpt_log[idx + 2U] >> 16];
        uint16_t pt = (uint16_t)usbutils_fpt_log[idx + 2U];
        uint32_t d = usbutils_fpt_log[idx + 3U];

        // Note: Ibex is operating on a 10MHz clock in CW-310 FPGA
        uint32_t elapsed_time = usbutils_fpt_log[idx + 1U] - oldest_time;
        uint32_t elapsed_us = elapsed_time / 10U;
        unsigned fract_us = elapsed_time - (10U * elapsed_us);

        LOG_INFO("%u.%uus : %s : %04x datum 0x%08x", elapsed_us,
                 fract_us,  // usbutils_fpt_log[idx + 1U],
                 file, pt, d);
      }
      idx = (idx >= USBUTILS_FUNCPT_LOG_SIZE - 4U) ? 0U : (idx + 4U);
    } while (idx != oldest_idx);
  }
}
#endif

#if USBUTILS_MEM_FASTER
// Local data copying routines to/from mmio32 (USBDEV packet buffers)
//  to investigate the performance attaianble with the existing hardware,
//  reducing the current software overhead
//
// Note: for performance measurements only at present
void usbutils_memcpy_from_mmio32(mmio_region_t base, uint32_t offset,
                                 void *dest, size_t len) {
  // We are concerned only with word-aligned data for testing
  CHECK(!(((uintptr_t)dest | offset) & 3u));

  const volatile uint32_t *ws = (uint32_t *)base.base + (offset >> 2);
  uint32_t *ewd = (uint32_t *)dest + 4 * (len >> 4);
  uint32_t *wd = (uint32_t *)dest;
  // TODO - experiment with compiler hinting and automated unrolling?
  while (wd < ewd) {
    wd[0] = ws[0];
    wd[1] = ws[1];
    wd[2] = ws[2];
    wd[3] = ws[3];
    wd += 4;
    ws += 4;
  }
  len &= 15u;
  if (len) {
    // Remaining whole words
    ewd = wd + (len >> 2);
    while (wd < ewd) {
      *wd++ = *ws++;
    }
    len &= 3u;
    if (len) {
      // Remaining individual bytes
      uint8_t *bd = (uint8_t *)wd;
      uint32_t d = *ws;
      bd[0] = (uint8_t)d;
      if (len > 1)
        bd[1] = (uint8_t)(d >> 8);
      if (len > 2)
        bd[2] = (uint8_t)(d >> 16);
    }
  }
}

// Note: for performance measurements only at present
void usbutils_memcpy_to_mmio32(mmio_region_t base, uint32_t offset,
                               const void *src, size_t len) {
  // We are concerned only with word-aligned data for testing
  CHECK(!(((uintptr_t)src | offset) & 3u));

  volatile uint32_t *wd = (uint32_t *)base.base + (offset >> 2);
  volatile uint32_t *ewd = wd + 4 * (len >> 4);
  const uint32_t *ws = (uint32_t *)src;
  // TODO - experiment with compiler hinting and automated unrolling?
  while (wd < ewd) {
    wd[0] = ws[0];
    wd[1] = ws[1];
    wd[2] = ws[2];
    wd[3] = ws[3];
    wd += 4;
    ws += 4;
  }
  len &= 15u;
  if (len) {
    // Remaining whole words
    ewd = wd + (len >> 2);
    while (wd < ewd) {
      *wd++ = *ws++;
    }
    len &= 3u;
    if (len) {
      // Remaining individual bytes
      const uint8_t *bs = (uint8_t *)ws;
      uint32_t d = bs[0];
      if (len > 1)
        d |= (bs[1] << 8);
      if (len > 2)
        d |= (bs[2] << 16);
      *wd = d;
    }
  }
}
#endif

#if USBUTILS_ENABLE_TRC
extern void usbutils_log_text(const char *s);
#endif
