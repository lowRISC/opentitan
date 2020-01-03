// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_TESTING_MOCK_MMIO_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_TESTING_MOCK_MMIO_H_

#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C++" {
#include <vector>
namespace dif_test {

enum class AccessType { kRead, kWrite };

struct VolatileAction {
  AccessType kind;
  ptrdiff_t offset;
  uint32_t value;
};

struct MockDevice {
  std::vector<VolatileAction> expected_actions;

  size_t current_action_index;
  size_t failed_expectations;
};

}  // namespace dif_test

typedef dif_test::MockDevice *reg32_t;

}  // extern "C++"
extern "C" {
#endif  // __cplusplus

#ifndef __cplusplus
typedef void *reg32_t;
#endif  // __cplusplus

uint32_t reg32_read(reg32_t base, ptrdiff_t offset);

void reg32_write(reg32_t base, ptrdiff_t offset, uint32_t value);

#ifdef __cplusplus
}  // extern C
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_TESTING_MOCK_MMIO_H_
