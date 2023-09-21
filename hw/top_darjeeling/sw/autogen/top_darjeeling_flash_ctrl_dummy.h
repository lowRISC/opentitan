// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_FLASH_CTRL_DUMMY_H_
#define OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_FLASH_CTRL_DUMMY_H_

// TODO(opentitan-integrated/issues/332): dummy definitions added as
// a workaround so that the flash_ctrl can be removed without having to
// refactor all dependent tests and the ROM at once. This needs to be
// cleaned up and removed. Note that the SW depending on flash_ctrl
// is currently not functional.
#define TOP_DARJEELING_FLASH_CTRL_CORE_BASE_ADDR 0x000A0000u
#define TOP_DARJEELING_FLASH_CTRL_MEM_BASE_ADDR  0x000A1000u
#define TOP_DARJEELING_EFLASH_BASE_ADDR          0x000A2000u
#define TOP_DARJEELING_EFLASH_SIZE_BYTES         0x100000


#define kTopDarjeelingPlicPeripheralFlashCtrl     0
#define kTopDarjeelingPlicIrqIdFlashCtrlProgEmpty 1
#define kTopDarjeelingPlicIrqIdFlashCtrlOpDone    2

#endif  // OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_FLASH_CTRL_DUMMY_H_
