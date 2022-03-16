// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_aes.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

extern "C" {
#include "aes_regs.h"  // Generated.
}  // extern "C"

namespace dif_aes_test {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::ElementsAreArray;
using testing::Test;

// Base class for the rest fixtures in this file.
class AesTest : public testing::Test, public mock_mmio::MmioTest {
 public:
  void SetExpectedKey(const dif_aes_key_share_t &key, uint32_t key_size) {
    for (uint32_t i = 0; i < key_size; ++i) {
      ptrdiff_t offset = AES_KEY_SHARE0_0_REG_OFFSET + (i * sizeof(uint32_t));
      EXPECT_WRITE32(offset, key.share0[i]);
    }

    for (uint32_t i = 0; i < key_size; ++i) {
      ptrdiff_t offset = AES_KEY_SHARE1_0_REG_OFFSET + (i * sizeof(uint32_t));
      EXPECT_WRITE32(offset, key.share1[i]);
    }
  }

  void SetExpectedIv(const dif_aes_iv_t &iv, const uint32_t kIvSize = 4) {
    for (uint32_t i = 0; i < kIvSize; ++i) {
      ptrdiff_t offset = AES_IV_0_REG_OFFSET + (i * sizeof(uint32_t));
      EXPECT_WRITE32(offset, iv.iv[i]);
    }
  }

  struct ConfigOptions {
    uint32_t key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128;
    uint32_t mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB;
    uint32_t operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC;
    uint32_t mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1;
    bool manual_op = false;
    bool force_zero_masks = false;
    bool key_sideloaded = false;
  };

  void SetExpectedConfig(const ConfigOptions &options) {
    EXPECT_WRITE32_SHADOWED(
        AES_CTRL_SHADOWED_REG_OFFSET,
        {{AES_CTRL_SHADOWED_KEY_LEN_OFFSET, options.key_len},
         {AES_CTRL_SHADOWED_MODE_OFFSET, options.mode},
         {AES_CTRL_SHADOWED_OPERATION_OFFSET, options.operation},
         {AES_CTRL_SHADOWED_PRNG_RESEED_RATE_OFFSET, options.mask_reseed},
         {AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, options.manual_op},
         {AES_CTRL_SHADOWED_SIDELOAD_BIT, options.key_sideloaded},
         {AES_CTRL_SHADOWED_FORCE_ZERO_MASKS_BIT, options.force_zero_masks}});
  }

  struct AuxConfigOptions {
    bool reseed_on_key_change = false;
    bool lock = false;
  };
  void SetExpectedAuxConfig(const AuxConfigOptions &options) {
    EXPECT_READ32(AES_CTRL_AUX_REGWEN_REG_OFFSET,
                  {{AES_CTRL_AUX_REGWEN_CTRL_AUX_REGWEN_BIT, 1}});

    EXPECT_WRITE32_SHADOWED(AES_CTRL_AUX_SHADOWED_REG_OFFSET,
                            {{AES_CTRL_AUX_SHADOWED_KEY_TOUCH_FORCES_RESEED_BIT,
                              options.reseed_on_key_change}});

    EXPECT_WRITE32(AES_CTRL_AUX_REGWEN_REG_OFFSET,
                   {{AES_CTRL_AUX_REGWEN_CTRL_AUX_REGWEN_BIT, !options.lock}});
  }
};

// Init tests
class AesInitTest : public AesTest {};

TEST_F(AesInitTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_aes_init(dev().region(), nullptr));
}

TEST_F(AesInitTest, Sucess) {
  dif_aes_t aes;
  EXPECT_DIF_OK(dif_aes_init(dev().region(), &aes));
}

// Base class for the rest of the tests in this file, provides a
// `dif_aes_t` instance.
class AesTestInitialized : public AesTest {
 protected:
  dif_aes_t aes_;

  dif_aes_transaction_t transaction = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeEcb,
      .key_len = kDifAesKey128,
      .manual_operation = kDifAesManualOperationAuto,
      .masking = kDifAesMaskingInternalPrng,
      .key_provider = kDifAesKeySoftwareProvided,
      .mask_reseeding = kDifAesReseedPerBlock,

      .reseed_on_key_change_lock = false,
  };

  const dif_aes_key_share_t kKey_ = {
      .share0 = {0x59, 0x70, 0x33, 0x73, 0x36, 0x76, 0x39, 0x79},
      .share1 = {0x4B, 0x61, 0x50, 0x64, 0x53, 0x67, 0x56, 0x6B}};

  const dif_aes_iv_t kIv_ = {0x50, 0x64, 0x53, 0x67};

  AesTestInitialized() { EXPECT_DIF_OK(dif_aes_init(dev().region(), &aes_)); }
};

// ECB tests.
class EcbTest : public AesTestInitialized {
 protected:
  EcbTest() { transaction.mode = kDifAesModeEcb; }
};

TEST_F(EcbTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  SetExpectedConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });
  SetExpectedAuxConfig({});
  SetExpectedKey(kKey_, 8);

  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction, &kKey_, NULL));
}

class CbcTest : public AesTestInitialized {
 protected:
  CbcTest() { transaction.mode = kDifAesModeCbc; }
};

TEST_F(CbcTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  SetExpectedConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_CBC,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });
  SetExpectedAuxConfig({});
  SetExpectedKey(kKey_, 8);
  SetExpectedIv(kIv_);

  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction, &kKey_, &kIv_));
}

// CFB tests.
class CFBTest : public AesTestInitialized {
 protected:
  CFBTest() { transaction.mode = kDifAesModeCfb; }
};

TEST_F(CFBTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  SetExpectedConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_CFB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });
  SetExpectedAuxConfig({});
  SetExpectedKey(kKey_, 8);
  SetExpectedIv(kIv_);

  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction, &kKey_, &kIv_));
}

// OFB tests.
class OFBTest : public AesTestInitialized {
 protected:
  OFBTest() { transaction.mode = kDifAesModeOfb; }
};

TEST_F(OFBTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  SetExpectedConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_OFB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });
  SetExpectedAuxConfig({});
  SetExpectedKey(kKey_, 8);
  SetExpectedIv(kIv_);

  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction, &kKey_, &kIv_));
}

// CTR tests.
class CTRTest : public AesTestInitialized {
 protected:
  CTRTest() { transaction.mode = kDifAesModeCtr; }
};

TEST_F(CTRTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  SetExpectedConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_CTR,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });
  SetExpectedAuxConfig({});
  SetExpectedKey(kKey_, 8);
  SetExpectedIv(kIv_);

  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction, &kKey_, &kIv_));
}

// Decrypt tests.
class DecryptTest : public AesTestInitialized {
 protected:
  DecryptTest() {
    transaction.mode = kDifAesModeEcb;
    transaction.operation = kDifAesOperationDecrypt;
  }
};

TEST_F(DecryptTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  SetExpectedConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_DEC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });
  SetExpectedAuxConfig({});
  SetExpectedKey(kKey_, 8);

  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction, &kKey_, NULL));
}

// Key size test.
class Key192Test : public AesTestInitialized {
 protected:
  Key192Test() { transaction.key_len = kDifAesKey192; }
};

TEST_F(Key192Test, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  SetExpectedConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_192,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });
  SetExpectedAuxConfig({});
  SetExpectedKey(kKey_, 8);

  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction, &kKey_, NULL));
}

// Key size test.
class Key256Test : public AesTestInitialized {
 protected:
  Key256Test() { transaction.key_len = kDifAesKey256; }
};

TEST_F(Key256Test, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  SetExpectedConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_256,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });
  SetExpectedAuxConfig({});
  SetExpectedKey(kKey_, 8);

  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction, &kKey_, NULL));
}

// Manual operation
class ManualOperationTest : public AesTestInitialized {
 protected:
  ManualOperationTest() {
    transaction.manual_operation = kDifAesManualOperationManual;
  }
};

TEST_F(ManualOperationTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  SetExpectedConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
      .manual_op = true,
  });
  SetExpectedAuxConfig({});
  SetExpectedKey(kKey_, 8);

  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction, &kKey_, NULL));
}

// Zero masking
class ZeroMaskingTest : public AesTestInitialized {
 protected:
  ZeroMaskingTest() { transaction.masking = kDifAesMaskingForceZero; }
};

TEST_F(ZeroMaskingTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  SetExpectedConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
      .force_zero_masks = true,
  });
  SetExpectedAuxConfig({});
  SetExpectedKey(kKey_, 8);

  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction, &kKey_, NULL));
}

// Alert test.
class AlertTest : public AesTestInitialized {};

TEST_F(AlertTest, RecovCtrlUpdateErr) {
  EXPECT_WRITE32(AES_ALERT_TEST_REG_OFFSET,
                 {{AES_ALERT_TEST_RECOV_CTRL_UPDATE_ERR_BIT, true},
                  {AES_ALERT_TEST_FATAL_FAULT_BIT, false}});

  EXPECT_DIF_OK(dif_aes_alert_force(&aes_, kDifAesAlertRecovCtrlUpdateErr));
}

TEST_F(AlertTest, AlertFatalFault) {
  EXPECT_WRITE32(AES_ALERT_TEST_REG_OFFSET,
                 {{AES_ALERT_TEST_RECOV_CTRL_UPDATE_ERR_BIT, false},
                  {AES_ALERT_TEST_FATAL_FAULT_BIT, true}});

  EXPECT_DIF_OK(dif_aes_alert_force(&aes_, kDifAesAlertFatalFault));
}

// Data tests.
class DataTest : public AesTestInitialized {
 protected:
  const dif_aes_data_t data_ = {
      .data = {0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A}};
};

TEST_F(DataTest, DataIn) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_INPUT_READY_BIT, true}});

  for (uint32_t i = 0; i < ARRAYSIZE(data_.data); i++) {
    ptrdiff_t offset = AES_DATA_IN_0_REG_OFFSET + (i * sizeof(uint32_t));
    EXPECT_WRITE32(offset, data_.data[i]);
  }

  EXPECT_DIF_OK(dif_aes_load_data(&aes_, data_));
}

TEST_F(DataTest, DataOut) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {
                                           {AES_STATUS_INPUT_READY_BIT, true},
                                           {AES_STATUS_OUTPUT_VALID_BIT, true},
                                       });

  for (uint32_t i = 0; i < ARRAYSIZE(data_.data); ++i) {
    ptrdiff_t offset = AES_DATA_OUT_0_REG_OFFSET + (i * sizeof(uint32_t));
    EXPECT_READ32(offset, data_.data[i]);
  }

  dif_aes_data_t out;
  EXPECT_DIF_OK(dif_aes_read_output(&aes_, &out));

  EXPECT_THAT(out.data, ElementsAreArray(data_.data));
}

// Read the IV tests.
class IVTest : public AesTestInitialized {};

TEST_F(IVTest, Read) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_IDLE_BIT, true}});

  for (uint32_t i = 0; i < ARRAYSIZE(kIv_.iv); ++i) {
    ptrdiff_t offset = AES_IV_0_REG_OFFSET + (i * sizeof(uint32_t));
    EXPECT_READ32(offset, kIv_.iv[i]);
  }

  dif_aes_iv_t iv;
  EXPECT_DIF_OK(dif_aes_read_iv(&aes_, &iv));

  EXPECT_THAT(iv.iv, ElementsAreArray(kIv_.iv));
}

// Trigger
class TriggerTest : public AesTestInitialized {};

TEST_F(TriggerTest, Start) {
  EXPECT_WRITE32(AES_TRIGGER_REG_OFFSET, {{AES_TRIGGER_START_BIT, true}});

  EXPECT_DIF_OK(dif_aes_trigger(&aes_, kDifAesTriggerStart));
}

TEST_F(TriggerTest, KeyIvDataInClear) {
  EXPECT_WRITE32(AES_TRIGGER_REG_OFFSET,
                 {
                     {AES_TRIGGER_KEY_IV_DATA_IN_CLEAR_BIT, true},
                 });

  EXPECT_DIF_OK(dif_aes_trigger(&aes_, kDifAesTriggerKeyIvDataInClear));
}

TEST_F(TriggerTest, DataOutClear) {
  EXPECT_WRITE32(AES_TRIGGER_REG_OFFSET,
                 {
                     {AES_TRIGGER_DATA_OUT_CLEAR_BIT, true},
                 });

  EXPECT_DIF_OK(dif_aes_trigger(&aes_, kDifAesTriggerDataOutClear));
}

TEST_F(TriggerTest, PrngReseed) {
  EXPECT_WRITE32(AES_TRIGGER_REG_OFFSET,
                 {
                     {AES_TRIGGER_PRNG_RESEED_BIT, true},
                 });

  EXPECT_DIF_OK(dif_aes_trigger(&aes_, kDifAesTriggerPrngReseed));
}

// Status
class Status : public AesTestInitialized {};

TEST_F(Status, True) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_IDLE_BIT, true}});
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_STALL_BIT, true}});
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_OUTPUT_LOST_BIT, true}});
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_OUTPUT_VALID_BIT, true}});
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_INPUT_READY_BIT, true}});
  EXPECT_READ32(AES_STATUS_REG_OFFSET,
                {{AES_STATUS_ALERT_FATAL_FAULT_BIT, true}});
  EXPECT_READ32(AES_STATUS_REG_OFFSET,
                {{AES_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_BIT, true}});

  bool set;
  EXPECT_DIF_OK(dif_aes_get_status(&aes_, kDifAesStatusIdle, &set));
  EXPECT_TRUE(set);

  EXPECT_DIF_OK(dif_aes_get_status(&aes_, kDifAesStatusStall, &set));
  EXPECT_TRUE(set);

  EXPECT_DIF_OK(dif_aes_get_status(&aes_, kDifAesStatusOutputLost, &set));
  EXPECT_TRUE(set);

  EXPECT_DIF_OK(dif_aes_get_status(&aes_, kDifAesStatusOutputValid, &set));
  EXPECT_TRUE(set);

  EXPECT_DIF_OK(dif_aes_get_status(&aes_, kDifAesStatusInputReady, &set));
  EXPECT_TRUE(set);

  EXPECT_DIF_OK(dif_aes_get_status(&aes_, kDifAesStatusAlertFatalFault, &set));
  EXPECT_TRUE(set);

  EXPECT_DIF_OK(
      dif_aes_get_status(&aes_, kDifAesStatusAlertRecovCtrlUpdateErr, &set));
  EXPECT_TRUE(set);
}

TEST_F(Status, False) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_IDLE_BIT, false}});
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_STALL_BIT, false}});
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_OUTPUT_LOST_BIT, false}});
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_OUTPUT_VALID_BIT, false}});
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_INPUT_READY_BIT, false}});
  EXPECT_READ32(AES_STATUS_REG_OFFSET,
                {{AES_STATUS_ALERT_FATAL_FAULT_BIT, false}});
  EXPECT_READ32(AES_STATUS_REG_OFFSET,
                {{AES_STATUS_ALERT_RECOV_CTRL_UPDATE_ERR_BIT, false}});

  bool set;
  EXPECT_DIF_OK(dif_aes_get_status(&aes_, kDifAesStatusIdle, &set));
  EXPECT_FALSE(set);

  EXPECT_DIF_OK(dif_aes_get_status(&aes_, kDifAesStatusStall, &set));
  EXPECT_FALSE(set);

  EXPECT_DIF_OK(dif_aes_get_status(&aes_, kDifAesStatusOutputLost, &set));
  EXPECT_FALSE(set);

  EXPECT_DIF_OK(dif_aes_get_status(&aes_, kDifAesStatusOutputValid, &set));
  EXPECT_FALSE(set);

  EXPECT_DIF_OK(dif_aes_get_status(&aes_, kDifAesStatusInputReady, &set));
  EXPECT_FALSE(set);

  EXPECT_DIF_OK(dif_aes_get_status(&aes_, kDifAesStatusAlertFatalFault, &set));
  EXPECT_FALSE(set);

  EXPECT_DIF_OK(
      dif_aes_get_status(&aes_, kDifAesStatusAlertRecovCtrlUpdateErr, &set));
  EXPECT_FALSE(set);
}

// Sideloaded key.
class SideloadedKeyTest : public AesTestInitialized {
 protected:
  SideloadedKeyTest() { transaction.key_provider = kDifAesKeySideload; }
};

TEST_F(SideloadedKeyTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  SetExpectedConfig(
      {.key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
       .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
       .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
       .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
       .key_sideloaded = true});

  SetExpectedAuxConfig({});
  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction, NULL, NULL));
}
// Mask reseeding.
class MaskReseedingTest : public AesTestInitialized {};

TEST_F(MaskReseedingTest, ReseedPer64Block) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  SetExpectedConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_64,
  });
  SetExpectedAuxConfig({});
  SetExpectedKey(kKey_, 8);
  transaction.mask_reseeding = kDifAesReseedPer64Block;
  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction, &kKey_, NULL));
}

TEST_F(MaskReseedingTest, ReseedPer8kBlock) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  SetExpectedConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_8K,
  });
  SetExpectedAuxConfig({});
  SetExpectedKey(kKey_, 8);
  transaction.mask_reseeding = kDifAesReseedPer8kBlock;
  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction, &kKey_, NULL));
}

// Reseed on key change.
class RessedOnKeyChangeTest : public AesTestInitialized {};

TEST_F(RessedOnKeyChangeTest, Unlock) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  SetExpectedConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });

  transaction.reseed_on_key_change = true;
  transaction.reseed_on_key_change_lock = false;
  SetExpectedAuxConfig({
      .reseed_on_key_change = true,
  });
  SetExpectedKey(kKey_, 8);
  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction, &kKey_, NULL));
}

TEST_F(RessedOnKeyChangeTest, Lock) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  SetExpectedConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });

  transaction.reseed_on_key_change = true;
  transaction.reseed_on_key_change_lock = true;
  SetExpectedAuxConfig({.reseed_on_key_change = true, .lock = true});
  SetExpectedKey(kKey_, 8);
  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction, &kKey_, NULL));
}

TEST_F(RessedOnKeyChangeTest, LockedSuccess) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  SetExpectedConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });

  transaction.reseed_on_key_change = true;
  transaction.reseed_on_key_change_lock = true;

  EXPECT_READ32(AES_CTRL_AUX_REGWEN_REG_OFFSET,
                {{AES_CTRL_AUX_REGWEN_CTRL_AUX_REGWEN_BIT, 0}});
  EXPECT_READ32(AES_CTRL_AUX_SHADOWED_REG_OFFSET,
                {{AES_CTRL_AUX_SHADOWED_KEY_TOUCH_FORCES_RESEED_BIT, true}});
  SetExpectedKey(kKey_, 8);
  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction, &kKey_, NULL));
}

TEST_F(RessedOnKeyChangeTest, LockedError) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  SetExpectedConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });

  transaction.reseed_on_key_change = true;
  transaction.reseed_on_key_change_lock = true;

  EXPECT_READ32(AES_CTRL_AUX_REGWEN_REG_OFFSET,
                {{AES_CTRL_AUX_REGWEN_CTRL_AUX_REGWEN_BIT, 0}});
  EXPECT_READ32(AES_CTRL_AUX_SHADOWED_REG_OFFSET,
                {{AES_CTRL_AUX_SHADOWED_KEY_TOUCH_FORCES_RESEED_BIT, false}});

  EXPECT_EQ(dif_aes_start(&aes_, &transaction, &kKey_, NULL), kDifError);
}

// Dif functions.
class DifFunctionsTest : public AesTestInitialized {
 protected:
  DifFunctionsTest() {}
};

TEST_F(DifFunctionsTest, Reset) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  EXPECT_WRITE32_SHADOWED(AES_CTRL_SHADOWED_REG_OFFSET,
                          {{AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, true}});

  EXPECT_WRITE32(AES_TRIGGER_REG_OFFSET,
                 {
                     {AES_TRIGGER_KEY_IV_DATA_IN_CLEAR_BIT, true},
                     {AES_TRIGGER_DATA_OUT_CLEAR_BIT, true},
                 });

  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);

  EXPECT_WRITE32_SHADOWED(
      AES_CTRL_SHADOWED_REG_OFFSET,
      {{AES_CTRL_SHADOWED_OPERATION_OFFSET, AES_CTRL_SHADOWED_OPERATION_MASK},
       {AES_CTRL_SHADOWED_MODE_OFFSET, AES_CTRL_SHADOWED_MODE_VALUE_AES_NONE},
       {AES_CTRL_SHADOWED_KEY_LEN_OFFSET, AES_CTRL_SHADOWED_KEY_LEN_MASK}});

  EXPECT_DIF_OK(dif_aes_reset(&aes_));
}

TEST_F(DifFunctionsTest, End) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  EXPECT_WRITE32_SHADOWED(AES_CTRL_SHADOWED_REG_OFFSET,
                          {{AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, true}});

  EXPECT_WRITE32(AES_TRIGGER_REG_OFFSET,
                 {
                     {AES_TRIGGER_KEY_IV_DATA_IN_CLEAR_BIT, true},
                     {AES_TRIGGER_DATA_OUT_CLEAR_BIT, true},
                 });

  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);

  EXPECT_DIF_OK(dif_aes_end(&aes_));
}

// Dif errors
class DifBadArgError : public AesTestInitialized {
 protected:
  DifBadArgError() {
    transaction.key_provider = kDifAesKeySoftwareProvided;
    transaction.mode = kDifAesModeCbc;
  }
};

TEST_F(DifBadArgError, start) {
  EXPECT_DIF_BADARG(dif_aes_start(NULL, &transaction, &kKey_, &kIv_));
  EXPECT_DIF_BADARG(dif_aes_start(&aes_, NULL, &kKey_, &kIv_));
  EXPECT_DIF_BADARG(dif_aes_start(&aes_, &transaction, NULL, &kIv_));
  EXPECT_DIF_BADARG(dif_aes_start(&aes_, &transaction, &kKey_, NULL));
}

TEST_F(DifBadArgError, reset) { EXPECT_DIF_BADARG(dif_aes_reset(NULL)); }

TEST_F(DifBadArgError, end) { EXPECT_DIF_BADARG(dif_aes_end(NULL)); }

TEST_F(DifBadArgError, LoadData) {
  dif_aes_data_t data = {};
  EXPECT_DIF_BADARG(dif_aes_load_data(NULL, data));
}

TEST_F(DifBadArgError, ReadOutput) {
  dif_aes_data_t data = {};
  EXPECT_DIF_BADARG(dif_aes_read_output(NULL, &data));
  EXPECT_DIF_BADARG(dif_aes_read_output(&aes_, NULL));
}

TEST_F(DifBadArgError, Trigger) {
  EXPECT_DIF_BADARG(dif_aes_trigger(NULL, kDifAesTriggerPrngReseed));
}

TEST_F(DifBadArgError, GetStatus) {
  bool set;
  EXPECT_DIF_BADARG(dif_aes_get_status(NULL, kDifAesStatusIdle, &set));
  EXPECT_DIF_BADARG(dif_aes_get_status(&aes_, kDifAesStatusIdle, NULL));
}

TEST_F(DifBadArgError, ReadIV) {
  dif_aes_iv_t iv = {};
  EXPECT_DIF_BADARG(dif_aes_read_iv(NULL, &iv));
  EXPECT_DIF_BADARG(dif_aes_read_iv(&aes_, NULL));
}

class DifUnavailableError : public AesTestInitialized {
 protected:
  DifUnavailableError() {
    EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_IDLE_BIT, false}});
  }
};

TEST_F(DifUnavailableError, start) {
  EXPECT_EQ(dif_aes_start(&aes_, &transaction, &kKey_, NULL), kDifUnavailable);
}

TEST_F(DifUnavailableError, end) {
  EXPECT_EQ(dif_aes_end(&aes_), kDifUnavailable);
}

TEST_F(DifUnavailableError, LoadData) {
  dif_aes_data_t data = {{0}};
  EXPECT_EQ(dif_aes_load_data(&aes_, data), kDifUnavailable);
}

TEST_F(DifUnavailableError, ReadIV) {
  dif_aes_iv_t iv = {{0}};
  EXPECT_EQ(dif_aes_read_iv(&aes_, &iv), kDifUnavailable);
}
}  // namespace
}  // namespace dif_aes_test
