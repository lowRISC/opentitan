// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_KEYMGR_DUMMY_H_
#define OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_KEYMGR_DUMMY_H_

// TODO(opentitan-integrated/issues/145): dummy definitions added as
// a workaround so that the the old keymgr can be removed without having to
// refactor all dependent tests and the ROM at once. These tests and the DIF
// need to be refactored so that they work with keymgr_dpe instead.
//  Note that the SW depending on the old keymgr is currently not functional.
#define TOP_DARJEELING_KEYMGR_BASE_ADDR 0x000A0000u

#define kTopDarjeelingPlicPeripheralKeymgr     0
#define kTopDarjeelingPlicIrqIdKeymgrProgEmpty 1
#define kTopDarjeelingPlicIrqIdKeymgrOpDone    2

#endif  // OPENTITAN_HW_TOP_DARJEELING_SW_AUTOGEN_TOP_DARJEELING_KEYMGR_DUMMY_H_
