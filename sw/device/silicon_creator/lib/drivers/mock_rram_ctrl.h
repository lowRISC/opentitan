// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_RRAM_CTRL_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_RRAM_CTRL_H_

#include "gmock/gmock.h"
#include "sw/device/lib/base/global_mock.h"
#include "sw/device/silicon_creator/lib/drivers/rram_ctrl.h"

namespace rom_test {
namespace internal {

/**
 * Mock class for rram_ctrl.
 */
class MockRramCtrl : public global_mock::GlobalMock<MockRramCtrl> {
 public:
  MOCK_METHOD(void, Init, ());
  MOCK_METHOD(void, Disable, ());
  MOCK_METHOD(void, StatusGet, (rram_ctrl_status_t *));
  MOCK_METHOD(void, ErrorCodeGet, (rram_ctrl_error_code_t *));
  MOCK_METHOD(rom_error_t, DataRead, (uint32_t, uint32_t, void *));
  MOCK_METHOD(rom_error_t, InfoRead,
              (const rram_ctrl_info_page_t *, uint32_t, uint32_t, void *));
  MOCK_METHOD(rom_error_t, InfoReadZerosOnReadError,
              (const rram_ctrl_info_page_t *, uint32_t, uint32_t, void *));
  MOCK_METHOD(rom_error_t, DataWrite, (uint32_t, uint32_t, const void *));
  MOCK_METHOD(rom_error_t, InfoWrite,
              (const rram_ctrl_info_page_t *, uint32_t, uint32_t,
               const void *));
  MOCK_METHOD(void, DataDefaultPermsSet, (rram_ctrl_perms_t));
  MOCK_METHOD(void, InfoPermsSet,
              (const rram_ctrl_info_page_t *, rram_ctrl_perms_t));
  MOCK_METHOD(rram_ctrl_cfg_t, DataDefaultCfgGet, ());
  MOCK_METHOD(void, DataDefaultCfgSet, (rram_ctrl_cfg_t));
  MOCK_METHOD(rram_ctrl_cfg_t, BootDataCfgGet, ());
  MOCK_METHOD(void, DataRegionProtect,
              (rram_ctrl_region_index_t region, uint32_t page_offset,
               uint32_t num_pages, rram_ctrl_perms_t perms, rram_ctrl_cfg_t cfg,
               hardened_bool_t));
  MOCK_METHOD(void, InfoCfgSet,
              (const rram_ctrl_info_page_t *, rram_ctrl_cfg_t));
  MOCK_METHOD(void, InfoCfgLock, (const rram_ctrl_info_page_t *));
  MOCK_METHOD(void, ExecSet, (uint32_t));
  MOCK_METHOD(void, InfoPageLockdown, (const rram_ctrl_info_page_t *));
};

}  // namespace internal

using MockRramCtrl = testing::StrictMock<internal::MockRramCtrl>;
using NiceMockRramCtrl = testing::NiceMock<internal::MockRramCtrl>;

MATCHER_P2(RramPerms, read, write, "") {
  // It would be nice to use `testing::Field` here, but that matcher does not
  // work with bitfields.
  return arg.read == static_cast<uint8_t>(read) &&
         arg.write == static_cast<uint8_t>(write);
}

MATCHER_P2(RramCfg, scrambling, ecc, "") {
  // It would be nice to use `testing::Field` here, but that matcher does not
  // work with bitfields.
  return arg.scrambling == static_cast<uint8_t>(scrambling) &&
         arg.ecc == static_cast<uint8_t>(ecc);
}

MATCHER_P(RramInfoPage, page, "") {
  return ::testing::Value(
      arg,
      ::testing::AllOf(
          ::testing::Field(&rram_ctrl_info_page_t::page_id, page.page_id),
          ::testing::Field(&rram_ctrl_info_page_t::emulated, page.emulated),
          ::testing::Field(&rram_ctrl_info_page_t::num_pages, page.num_pages)));
}

/**
 * Sets expectations matching `nvm_ctrl_info_erase()`'s RRAM implementation
 * for the given (possibly multi-page) info page: RRAM has no hardware erase
 * primitive, so `nvm_ctrl.c` emulates a page erase with one all-0xFF write
 * per physical page the logical page spans, via `DataWrite` for an emulated
 * page (relocated onto the data partition) or `InfoWrite` for a real one.
 *
 * @param mock The mock to set expectations on.
 * @param page The (possibly multi-page) info page expected to be erased.
 *             Must be one of the named `kRramCtrlInfoPage*` globals: for a
 *             real (non-emulated) page, the `InfoWrite` expectation matches
 *             on `&page`'s identity, which only matches the pointer
 *             `nvm_ctrl.c` actually passes (`page_ptr()`) if `page` refers to
 *             the same global rather than a local copy.
 */
inline void ExpectRramInfoErase(MockRramCtrl &mock,
                                const rram_ctrl_info_page_t &page) {
  enum { kPageWords = RRAM_CTRL_PARAM_BYTES_PER_PAGE / sizeof(uint32_t) };
  for (uint32_t i = 0; i < page.num_pages; ++i) {
    if (page.emulated) {
      EXPECT_CALL(mock,
                  DataWrite((page.page_id + i) * RRAM_CTRL_PARAM_BYTES_PER_PAGE,
                            kPageWords, ::testing::_))
          .WillOnce(::testing::Return(kErrorOk));
    } else {
      EXPECT_CALL(mock, InfoWrite(&page, i * RRAM_CTRL_PARAM_BYTES_PER_PAGE,
                                  kPageWords, ::testing::_))
          .WillOnce(::testing::Return(kErrorOk));
    }
  }
}

}  // namespace rom_test

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_DRIVERS_MOCK_RRAM_CTRL_H_
