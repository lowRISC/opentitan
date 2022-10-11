// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_MACROS_H_
#define OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_MACROS_H_

#define OTTF_WORD_SIZE 4
#define OTTF_NV_SCRATCH _non_volatile_scratch_start
#define OTTF_HALF_WORD_SIZE (OTTF_WORD_SIZE / 2)
#define OTTF_CONTEXT_SIZE (OTTF_WORD_SIZE * 30)
#define OTTF_TASK_DELETE_SELF_OR_DIE \
  ottf_task_delete_self();           \
  abort();

#endif  // OPENTITAN_SW_DEVICE_LIB_TESTING_TEST_FRAMEWORK_OTTF_MACROS_H_
