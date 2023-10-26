// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_E2E_BOOT_SVC_BOOT_SVC_TEST_LIB_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_E2E_BOOT_SVC_BOOT_SVC_TEST_LIB_H_
#include "sw/device/lib/base/status.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"

typedef enum boot_svc_test {
  kBootSvcTestEmpty = 1,
} boot_svc_test_t;

typedef enum boot_svc_test_state {
  kBootSvcTestStateInit = 0,
  kBootSvcTestStateCheckEmpty,
  kBootSvcTestStateFinal,
} boot_svc_test_state_t;

typedef struct boot_svc_retram {
  // Which boot service test is running.
  boot_svc_test_t test;
  // The state of the test.
  boot_svc_test_state_t state;
  // The number of boots the test has performed.
  int boots;
  // The owner partition that was booted on each boot.
  char partition[10];
} boot_svc_retram_t;

status_t boot_svc_test_init(retention_sram_t *retram, boot_svc_test_t test);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_ROM_EXT_E2E_BOOT_SVC_BOOT_SVC_TEST_LIB_H_
