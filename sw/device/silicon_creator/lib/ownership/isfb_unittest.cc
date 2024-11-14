// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/ownership/isfb.h"

#include <algorithm>
#include <limits>
#include <stdint.h>
#include <vector>

#include "sw/device/lib/base/hardened.h"
#include "sw/device/silicon_creator/lib/drivers/mock_flash_ctrl.h"
#include "sw/device/silicon_creator/testing/rom_test.h"

namespace {
using rom_test::FlashCfg;
using rom_test::FlashPerms;
using rom_test::MockFlashCtrl;
using ::testing::_;
using ::testing::Return;

enum {
  kStrikeCntMax = 128,
  kProductExprCntMax = 256,
};

class IsfbTest : public rom_test::RomTest {
 protected:
  void SetUp() override {
    RomTest::SetUp();
    isfb_config_ = {
        .bank = 0,
        .page = 5,
        .product_words = 4,
    };
    owner_config_ = {
        .isfb = &isfb_config_,
    };
  }

  void ExpectInfoRead(const std::vector<uint32_t> &data, uint32_t offset,
                      rom_error_t error) {
    EXPECT_CALL(flash_ctrl_, InfoRead(_, offset, data.size(), _))
        .WillOnce([data, error](auto, auto, auto, void *out) {
          uint32_t *data_out = reinterpret_cast<uint32_t *>(out);
          std::copy_n(data.begin(), data.size(), data_out);
          return error;
        });
  }

  std::vector<uint32_t> StrikeFlashWords(uint32_t strike_count) {
    EXPECT_LE(strike_count, kStrikeCntMax);
    std::vector<uint32_t> words(kStrikeCntMax,
                                std::numeric_limits<uint32_t>::max());
    std::fill_n(words.begin(), strike_count, 0);
    return words;
  }

  std::vector<uint32_t> ProductExpressionInit(const manifest_ext_isfb_t &ext) {
    EXPECT_LE(ext.product_expr_count, kProductExprCntMax);
    std::vector<uint32_t> words(kProductExprCntMax,
                                std::numeric_limits<uint32_t>::max());
    for (size_t i = 0; i < ext.product_expr_count; ++i) {
      words[i] = ext.product_expr[i].value;
    }
    return words;
  }
  MockFlashCtrl flash_ctrl_;
  owner_isfb_config_t isfb_config_;
  owner_config_t owner_config_;
};

const manifest_ext_isfb_t kManifestExtGood = {
    .header =
        {
            .identifier = kManifestExtIdIsfb,
            .name = kManifestExtIdIsfb,
        },
    .strike_mask =
        {
            // Only the first word is struck.
            0xfffffffe,
            0xffffffff,
            0xffffffff,
            0xffffffff,
        },
    .product_expr_count = 2,
    .product_expr =
        {
            {
                .mask = 0xffffffff,
                .value = 0xa5a5a5a5,
            },
            {
                .mask = 0xf0f0f0f0,
                .value = 0xa0a0a0a0,
            },
        },
};

TEST_F(IsfbTest, OwnershipIsfbNotPreset) {
  manifest_ext_isfb_t ext = {
      .header =
          {
              .identifier = kManifestExtIdIsfb,
              .name = kManifestExtIdIsfb,
          },
  };
  owner_config_t owner_config = {
      .isfb = (owner_isfb_config_t *)kHardenedBoolFalse,
  };
  uint32_t checks_performed_count;
  rom_error_t error =
      isfb_boot_request_process(&ext, &owner_config, &checks_performed_count);
  EXPECT_EQ(error, kErrorOwnershipISFBNotPresent);
  EXPECT_EQ(checks_performed_count, UINT32_MAX);
}

TEST_F(IsfbTest, InvalidManifestProductExpressionCount) {
  manifest_ext_isfb_t ext = {
      .header =
          {
              .identifier = kManifestExtIdIsfb,
              .name = kManifestExtIdIsfb,
          },
      // The product expression count is larger than what is allowed in the
      // ownership configuration.
      .product_expr_count = 4,
  };
  uint32_t checks_performed_count;
  rom_error_t error =
      isfb_boot_request_process(&ext, &owner_config_, &checks_performed_count);
  EXPECT_EQ(error, kErrorOwnershipISFBProductExpCnt);
  EXPECT_EQ(checks_performed_count, UINT32_MAX);
}

TEST_F(IsfbTest, BootRequestProcess) {
  EXPECT_CALL(flash_ctrl_, InfoType0ParamsBuild(0, 5, _))
      .WillOnce(Return(kErrorOk));

  // This matches the number of strikes present in the manifest extension
  // `strike_mask` field value.
  ExpectInfoRead(StrikeFlashWords(/*strike_count=*/1), /*offset=*/0, kErrorOk);

  ExpectInfoRead(ProductExpressionInit(kManifestExtGood), /*offset=*/1024,
                 kErrorOk);

  uint32_t checks_performed_count;
  rom_error_t error = isfb_boot_request_process(
      &kManifestExtGood, &owner_config_, &checks_performed_count);
  EXPECT_EQ(error, kErrorOk);
  EXPECT_EQ(checks_performed_count,
            kStrikeCntMax + kManifestExtGood.product_expr_count);
}

// This test checks the anti-rollback mechanism in the ISFB strike mask.
TEST_F(IsfbTest, AntiRollbackBootFailure) {
  EXPECT_CALL(flash_ctrl_, InfoType0ParamsBuild(0, 5, _))
      .WillOnce(Return(kErrorOk));
  enum {
    // this value is derived from the strike mask in the manifest extension to
    // be larger than the expected number of 0s in the strike mask. See
    // `strike_mask` check.
    kExpectedStrikeCount = 2,
  };

  // Sanity check to ensure that the strike mask only has the first word struck.
  // Plase update the test if the strike mask is changed.
  EXPECT_EQ(kManifestExtGood.strike_mask[0], 0xfffffffe);

  // The state of device is such that the number of strikes is larger than what
  // is defined in the manifest extension. This must result in an anti-rollback
  // failure which is mapped to the `kErrorOwnershipISFBStrikeMask` error code.
  ExpectInfoRead(StrikeFlashWords(kExpectedStrikeCount), /*offset=*/0,
                 kErrorOk);

  uint32_t checks_performed_count;
  rom_error_t error = isfb_boot_request_process(
      &kManifestExtGood, &owner_config_, &checks_performed_count);
  EXPECT_EQ(error, kErrorOwnershipISFBStrikeMask);
  EXPECT_EQ(checks_performed_count, UINT32_MAX);
}

// This test checks that an invalid product association detected at boot time
// results in an error.
TEST_F(IsfbTest, ProductAssociationError) {
  EXPECT_CALL(flash_ctrl_, InfoType0ParamsBuild(0, 5, _))
      .WillOnce(Return(kErrorOk));
  ExpectInfoRead(StrikeFlashWords(/*strike_count=*/1), /*offset=*/0, kErrorOk);

  // The following manifest extension is used to generate an invalid product
  // configuration in the `ProductExpressionInit` call. Note that the
  // `isfb_boot_request_process` function still uses the `kManifestExtGood`
  // manifest extension to trigger the error condition.
  const manifest_ext_isfb_t kManifestExtBadProdExpr = {
      // This value is set to 0 to generate an info flash page configuration
      // with an invalid product expression.
      .product_expr_count = 0,
  };

  ExpectInfoRead(ProductExpressionInit(kManifestExtBadProdExpr),
                 /*offset=*/1024, kErrorOk);

  uint32_t checks_performed_count;
  rom_error_t error = isfb_boot_request_process(
      &kManifestExtGood, &owner_config_, &checks_performed_count);
  EXPECT_EQ(error, kErrorOwnershipISFBProductExp);
  EXPECT_EQ(checks_performed_count, UINT32_MAX);
}

}  // namespace
