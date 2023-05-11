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
                                    "usbdev_stream_test.c",
                                    "usbdev_suspend_test.c"};
/**
 * Current index into function point circular buffer.
 */
volatile unsigned usbutils_fpt_next;
/**
 * Function point circular buffer.
 */
uint32_t usbutils_fpt_log[USBUTILS_FUNCPT_LOG_SIZE];

/**
 * Report contents of the function point buffer.
 */
void usbutils_funcpt_report(void) {
  // Locate the oldest entry in the buffer.
  uint32_t oldest_time = ~0U;
  unsigned oldest_idx = ~0U;
  unsigned idx = 0U;
  while (idx < USBUTILS_FUNCPT_LOG_SIZE) {
    if (usbutils_fpt_log[idx] == USBUTILS_FUNCPT_ENTRY_SIGNATURE) {
      uint32_t time = usbutils_fpt_log[idx + 1U];
      // Note: this is for diagnostic use onl; bear in mind that we're recording
      // only the bottom 32 bits of the cycle counter.
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
    const unsigned num_files = sizeof(funcpt_file) / sizeof(funcpt_file[0]);
    idx = oldest_idx;
    do {
      if (usbutils_fpt_log[idx] == USBUTILS_FUNCPT_ENTRY_SIGNATURE) {
        // Note: Ibex is operating on a 10MHz clock in CW310 FPGA
        // TODO: generalize this
        uint32_t elapsed_time = usbutils_fpt_log[idx + 1U] - oldest_time;
        uint32_t elapsed_us = elapsed_time / 10U;
        unsigned fract_us = elapsed_time - (10U * elapsed_us);

        // Determine the name of the file and the function point number within
        // that file.
        uint32_t datum = usbutils_fpt_log[idx + 2U];
        unsigned file_idx = (datum >> 16) & 0x7fffU;
        const char *file =
            (file_idx < num_files) ? funcpt_file[file_idx] : "<Unknown>";
        uint16_t pt = (uint16_t)usbutils_fpt_log[idx + 2U];

        // Datum value recorded with the function point.
        uint32_t d = usbutils_fpt_log[idx + 3U];

        //        LOG_INFO("%u.%uus : %s : %04x datum 0x%08x", elapsed_us,
        //        fract_us, file, pt, d);
        const char *s = (datum >> 31) ? (char *)d : ".";
        LOG_INFO("%u.%uus : %s : 0x%04x (%u) datum 0x%08x (%s)", elapsed_us,
                 fract_us, file, pt, pt, d, s);
      }
      idx = (idx >= USBUTILS_FUNCPT_LOG_SIZE - 4U) ? 0U : (idx + 4U);
    } while (idx != oldest_idx);
  }
}
#endif

#if USBUTILS_ENABLE_TRC
extern void usbutils_log_text(const char *s);
#endif
