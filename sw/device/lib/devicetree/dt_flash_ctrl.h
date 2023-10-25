// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_FLASH_CTRL_H_
#define OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_FLASH_CTRL_H_

#include <stdint.h>

typedef enum {
  kDtFlashCtrlRegBlockCore = 0,
  kDtFlashCtrlRegBlockPrim,
  kDtFlashCtrlRegBlockMem,
  kDtFlashCtrlRegBlockCount,
} dt_flash_ctrl_reg_block_t;

typedef enum {
  kDtFlashCtrlIrqProgEmpty = 0,
  kDtFlashCtrlIrqProgLvl,
  kDtFlashCtrlIrqRdFull,
  kDtFlashCtrlIrqRdLvl,
  kDtFlashCtrlIrqOpDone,
  kDtFlashCtrlIrqCorrErr,
  kDtFlashCtrlIrqTypeCount,
} dt_flash_ctrl_irq_type_t;

extern uint32_t dt_flash_ctrl_num_devices(void);
extern int32_t dt_flash_ctrl_device_id(uint32_t dev_idx);
extern uintptr_t dt_flash_ctrl_reg_addr(uint32_t dev_idx,
                                        dt_flash_ctrl_reg_block_t reg_block);
extern int32_t dt_flash_ctrl_irq_id(uint32_t dev_idx,
                                    dt_flash_ctrl_irq_type_t irq_type);

#endif  // OPENTITAN_SW_DEVICE_LIB_DEVICETREE_DT_FLASH_CTRL_H_
