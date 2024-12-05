// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_USB_TESTUTILS_DIAGS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_USB_TESTUTILS_DIAGS_H_
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/runtime/print.h"

// Diagnostic, testing and performance measurements utilities for verification
// of usbdev and development of the usb_testutils support software; the
// requirements of this software are peculiar in that the USBDPI model used in
// top-level requires packet responses very promptly, so the introduction of
// logging/tracing code can substantially alter behavior and cause malfunction
//
// Employ faster memory copying routines to/from the packet buffer
//   (the standard dif_usbdev_buffer_write/read functionality should normally be
//    employed, but it is inefficient; the replacement routines better model the
//    attainable performance)
#ifndef USBUTILS_MEM_FASTER
#define USBUTILS_MEM_FASTER 1
#endif

// Implement low-impact tracing of software execution, permitting the software
//   and hardware behavior to be married, hopefully without modifying the
//   behavior/performance, particularly in top-level simulation
#define USBUTILS_FUNCTION_POINTS 0

// Record the function points to a memory buffer instead, for use where test
//   hardware is unavailable, eg. FPGA builds
#define USBUTILS_FUNCPT_USE_BUFFER 0

#if USBUTILS_MEM_FASTER
#include "sw/device/lib/base/mmio.h"
#endif

#if USBUTILS_FUNCTION_POINTS
// For access to ibex_mcycle_read()
#include "sw/device/lib/runtime/ibex.h"

// Function point file numbers
//   (used to index filename table in usb_testutils_diags.c)
#define USBUTILS_FUNCPT_FILE_DIF_USBDEV 0x01U
#define USBUTILS_FUNCPT_FILE_USB_TESTUTILS 0x02U
#define USBUTILS_FUNCPT_FILE_USB_CONTROLEP 0x03U
#define USBUTILS_FUNCPT_FILE_USB_SIMPLESER 0x04U
#define USBUTILS_FUNCPT_FILE_USBDEV_TEST 0x05U
#define USBUTILS_FUNCPT_FILE_USBDEV_STRM_TEST 0x06U

#define USBUTILS_FUNCPT_LOG_ENTRIES 0x1000U
#define USBUTILS_FUNCPT_LOG_SIZE (USBUTILS_FUNCPT_LOG_ENTRIES * 4U)

#define USBUTILS_FUNCPT_ENTRY_SIGNATURE 0xAA55FF99U
/**
 * Entry in function point stream
 */
typedef struct {
  uint32_t sig;
  uint32_t time;
  uint32_t file_point;
  uint32_t data;
} funcpt_entry_t;

#if USBUTILS_FUNCPT_USE_BUFFER
// Record function points to RAM buffer for deferred reporting, eg. FPGA
#define USBUTILS_FUNCPT(pt, d)                                        \
  {                                                                   \
    unsigned idx = usbutils_fpt_next;                                 \
    usbutils_fpt_next =                                               \
        (idx >= USBUTILS_FUNCPT_LOG_SIZE - 4U) ? 0U : (idx + 4U);     \
    functpt_enttry_t *e = (functpt_enttry_t *)&usbutils_fpt_log[idx]; \
    e->sig = USBUTILS_FUNCPT_ENTRY_SIGNATURE;                         \
    e->time = (uint32_t)ibex_mcycle_read();                           \
    e->file_point = (USBUTILS_FUNCPT_FILE << 16) | pt;                \
    e->data = (d);                                                    \
  }

extern volatile unsigned usbutils_fpt_next;
extern uint32_t usbutils_fpt_log[];
#else
// Emit function points to special address for waveform viewing in simulation
//   (this is the address used by DV simulation for logging output)
#define USBUTILS_FUNCPT(pt, d)                           \
  {                                                      \
    volatile uint32_t *log_hw = (uint32_t *)0x411f0084u; \
    uint32_t time = (uint32_t)ibex_mcycle_read();        \
    *log_hw = USBUTILS_FUNCPT_ENTRY_SIGNATURE;           \
    *log_hw = time;                                      \
    *log_hw = (USBUTILS_FUNCPT_FILE << 16) | (pt);       \
    *log_hw = (d);                                       \
  }
#endif

/**
 * Report the contents of the function point log
 */
void usbutils_funcpt_report(void);
#else
// Omit function point tracing
#define USBUTILS_FUNCPT(pt, d)
#endif

// For investigation of usbdev performance characteristics
#if USBUTILS_MEM_FASTER
/**
 * Performant copying routine from usbdev packet buffer (MMIO)
 *
 * @param  base      MMIO base address
 * @param  offset    MMIO word offset
 * @param  dest      Buffer to receive data
 * @param  len       Number of bytes to be copied
 */
void usbutils_memcpy_from_mmio32(mmio_region_t base, uint32_t offset,
                                 void *dest, size_t len);
/**
 * Performant copying routine to usbdev packet buffer (MMIO)
 *
 * @param  base      MMIO base address
 * @param  offset    MMIO word offset
 * @param  src       Data to be copied
 * @param  len       Number of bytes to be copied
 */
void usbutils_memcpy_to_mmio32(mmio_region_t base, uint32_t offset,
                               const void *src, size_t len);
#endif

// Used for tracing what is going on. This may impact timing which is critical
// when simulating with the USB DPI module.
#define USBUTILS_ENABLE_TRC 0

// Prompt the user for intervention if we're not running in simulation;
// logging within simulation can be time-consuming and induce failures.
#define USBUTILS_USER_PROMPT(...)                                            \
  do {                                                                       \
    if (kDeviceType != kDeviceSimDV && kDeviceType != kDeviceSimVerilator) { \
      LOG_INFO(__VA_ARGS__);                                                 \
    }                                                                        \
  } while (false)

#if USBUTILS_ENABLE_TRC
#if 0
// May be useful on FPGA CW310
#include "sw/device/lib/runtime/log.h"
#define TRC_S(s) LOG_INFO("%s", s)
#define TRC_I(i, b) LOG_INFO("0x%x", i)
#define TRC_C(c) LOG_INFO("%c", c)
#else
// Very low impact, for use in t-l simulation
#define USBDIAGS_LOG_EMIT(d) (*((volatile uint32_t *)0x411f0084u) = (d))

#define TRC_S(s) usbutils_log_text(s)
#define TRC_I(i, b) USBDIAGS_LOG_EMIT(i)
#define TRC_C(c) USBDIAGS_LOG_EMIT(0xcc000000u | (uint16_t)c)

// Faster string logging to minimise impact upon timing
inline void usbutils_log_text(const char *s) {
  while (*s) {
    USBDIAGS_LOG_EMIT(*s);
    s++;
  }
}
#endif
#else
#define TRC_S(s)
#define TRC_I(i, b)
#define TRC_C(c)
#endif

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_USB_TESTUTILS_DIAGS_H_
