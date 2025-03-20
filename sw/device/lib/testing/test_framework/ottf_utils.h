// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_UTILS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_UTILS_H_

#include <stdatomic.h>
#include <stdbool.h>
#include <stdnoreturn.h>

#include "sw/device/lib/base/status.h"
#include "sw/device/lib/testing/json/command.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf_commands.h"

/**
 * Wait until a condition is true.
 *
 * @param cond: an expression that can be repeated tested for.
 * @param timeout_usec: timeout in microseconds.
 *
 * In DV, this function will simply spin since the DV environment can do
 * backdoor writes to make the condition true. On real device, this will wait
 * for host to send ujson message. The condition is checked after each command.
 */
#define OTTF_WAIT_FOR(cond, timeout_usec)                                     \
  do {                                                                        \
    if (kDeviceType != kDeviceSimDV) {                                        \
      ujson_t uj = ujson_ottf_console();                                      \
      const ibex_timeout_t timeout_ = ibex_timeout_init(timeout_usec);        \
      test_command_t command;                                                 \
      LOG_INFO("SiVal: waiting for commands");                                \
      while (!(cond)) {                                                       \
        CHECK(!ibex_timeout_check(&timeout_),                                 \
              "Timed out after %d usec waiting for " #cond, timeout_usec);    \
        /* FIXME: what to do on error? */                                     \
        CHECK_STATUS_OK(                                                      \
            UJSON_WITH_CRC(ujson_deserialize_test_command_t, &uj, &command)); \
        CHECK_STATUS_OK(ujson_ottf_dispatch(&uj, command));                   \
      }                                                                       \
    } else {                                                                  \
      IBEX_SPIN_FOR(cond, timeout_usec);                                      \
    }                                                                         \
  } while (0)

/**
 * Declare a variable which can be used with `OTTF_WAIT_FOR`.
 *
 * Variable declared this way will have an associated symbol in the final ELF
 * binary. This will allow host test harness or DV to find the variable and
 * manipulate it with backdoor access mechanism, via OTTF uJSON commands for
 * SiVal or directly modifying the underlying memory for DV.
 *
 * This variable can be accessed directly if you're certain there'll be no
 * concurrent DV modification. However, if a concurrent modification may occur,
 * you need to use `OTTF_BACKDOOR_READ` to provide correct synchronization to
 * avoid miscompilation.
 *
 * NOTE: this macro guarantees that the variable works in all non-DV
 * environments but may not work in DV.
 *
 * Example:
 * ```c
 * OTTF_BACKDOOR_VAR bool sival_is_ready = false;
 * ```
 */
#define OTTF_BACKDOOR_VAR OT_USED OT_SECTION(".data")

/**
 * Same as `OTTF_BACKDOOR_VAR` but for DV environments.
 * ```
 */
#define OTTF_BACKDOOR_VAR_DV OT_USED OT_SECTION(".rodata")

#if defined(OPENTITAN_IS_EARLGREY)

static void ottf_backdoor_flush_read_buffers(void) {
  // On earlgrey, some backdoor variables may live on flash, which
  // has a read buffer that needs to be flushed to get up-to-date value.
  //
  // Cause read buffers to flush since it reads 32 bytes, which is the
  // size of the read buffers.
  enum { kBufferBytes = 32 };
  static volatile const uint8_t kFlashFlusher[kBufferBytes];
  for (int i = 0; i < sizeof(kFlashFlusher); ++i) {
    (void)kFlashFlusher[i];
  }
}

#elif defined(OPENTITAN_IS_DARJEELING)

static void ottf_backdoor_flush_read_buffers(void) {}

#else
#error Unsupported top
#endif

/**
 * Reads a backdoor variable.
 *
 * This function can work on both normal and DV-specific backdoor variables.
 * This function has acquire semantics. All memory accesses after the read
 * will not be reordered by compiler to happen before the read.
 *
 * @param var the variable to read from.
 * @return the read value.
 */
#define OTTF_BACKDOOR_READ(var)                               \
  ({                                                          \
    ottf_backdoor_flush_read_buffers();                       \
    typeof(var) _tmp = *(const volatile typeof(var) *)&(var); \
    atomic_signal_fence(memory_order_acquire);                \
    _tmp;                                                     \
  })

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_UTILS_H_
