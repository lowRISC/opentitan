// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_aes.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
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
  void ExpectReadMultreg(const uint32_t reg, const uint32_t *data,
                         size_t size) {
    for (uint32_t i = 0; i < size; ++i) {
      ptrdiff_t offset = reg + (i * sizeof(uint32_t));
      EXPECT_READ32(offset, data[i]);
    }
  }
  void ExpectWriteMultreg(const uint32_t reg, const uint32_t *data,
                          size_t size) {
    for (uint32_t i = 0; i < size; ++i) {
      ptrdiff_t offset = reg + (i * sizeof(uint32_t));
      EXPECT_WRITE32(offset, data[i]);
    }
  }
  void ExpectKey(const dif_aes_key_share_t &key, uint32_t key_size) {
    ExpectWriteMultreg(AES_KEY_SHARE0_0_REG_OFFSET, key.share0, key_size);
    ExpectWriteMultreg(AES_KEY_SHARE1_0_REG_OFFSET, key.share1, key_size);
  }

  void ExpectIv(const dif_aes_iv_t &iv, const uint32_t kIvSize = 4) {
    EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_IDLE_BIT, true}});
    ExpectWriteMultreg(AES_IV_0_REG_OFFSET, iv.iv, kIvSize);
  }

  struct ConfigOptions {
    uint32_t key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128;
    uint32_t mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB;
    uint32_t operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC;
    uint32_t mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1;
    bool manual_op = false;
    bool key_sideloaded = false;
  };

  void ExpectConfig(const ConfigOptions &options) {
    EXPECT_WRITE32_SHADOWED(
        AES_CTRL_SHADOWED_REG_OFFSET,
        {{AES_CTRL_SHADOWED_KEY_LEN_OFFSET, options.key_len},
         {AES_CTRL_SHADOWED_MODE_OFFSET, options.mode},
         {AES_CTRL_SHADOWED_OPERATION_OFFSET, options.operation},
         {AES_CTRL_SHADOWED_PRNG_RESEED_RATE_OFFSET, options.mask_reseed},
         {AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, options.manual_op},
         {AES_CTRL_SHADOWED_SIDELOAD_BIT, options.key_sideloaded}});
  }

  struct AuxConfigOptions {
    bool reseed_on_key_change = false;
    bool force_masks = false;
    bool lock = false;
  };
  void ExpectAuxConfig(const AuxConfigOptions &options) {
    EXPECT_READ32(AES_CTRL_AUX_REGWEN_REG_OFFSET,
                  {{AES_CTRL_AUX_REGWEN_CTRL_AUX_REGWEN_BIT, 1}});

    EXPECT_WRITE32_SHADOWED(
        AES_CTRL_AUX_SHADOWED_REG_OFFSET,
        {{AES_CTRL_AUX_SHADOWED_KEY_TOUCH_FORCES_RESEED_BIT,
          options.reseed_on_key_change},
         {AES_CTRL_AUX_SHADOWED_FORCE_MASKS_BIT, options.force_masks}});

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

  dif_aes_transaction_t transaction_ = {
      .operation = kDifAesOperationEncrypt,
      .mode = kDifAesModeEcb,
      .key_len = kDifAesKey128,
      .manual_operation = kDifAesManualOperationAuto,
      .key_provider = kDifAesKeySoftwareProvided,
      .mask_reseeding = kDifAesReseedPerBlock,
      .reseed_on_key_change = false,
      .force_masks = false,
      .ctrl_aux_lock = false,
  };

  const dif_aes_key_share_t kKey = {
      .share0 = {0x59, 0x70, 0x33, 0x73, 0x36, 0x76, 0x39, 0x79},
      .share1 = {0x4B, 0x61, 0x50, 0x64, 0x53, 0x67, 0x56, 0x6B}};

  const dif_aes_iv_t kIv = {0x50, 0x64, 0x53, 0x67};

  AesTestInitialized() { EXPECT_DIF_OK(dif_aes_init(dev().region(), &aes_)); }
};

// ECB tests.
class EcbTest : public AesTestInitialized {
 protected:
  EcbTest() { transaction_.mode = kDifAesModeEcb; }
};

TEST_F(EcbTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  ExpectConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });
  ExpectAuxConfig({});
  ExpectKey(kKey, 8);

  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction_, &kKey, nullptr));
}

class CbcTest : public AesTestInitialized {
 protected:
  CbcTest() { transaction_.mode = kDifAesModeCbc; }
};

TEST_F(CbcTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  ExpectConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_CBC,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });
  ExpectAuxConfig({});
  ExpectKey(kKey, 8);
  ExpectIv(kIv);

  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction_, &kKey, &kIv));
}

// CFB tests.
class CFBTest : public AesTestInitialized {
 protected:
  CFBTest() { transaction_.mode = kDifAesModeCfb; }
};

TEST_F(CFBTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  ExpectConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_CFB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });
  ExpectAuxConfig({});
  ExpectKey(kKey, 8);
  ExpectIv(kIv);

  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction_, &kKey, &kIv));
}

// OFB tests.
class OFBTest : public AesTestInitialized {
 protected:
  OFBTest() { transaction_.mode = kDifAesModeOfb; }
};

TEST_F(OFBTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  ExpectConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_OFB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });
  ExpectAuxConfig({});
  ExpectKey(kKey, 8);
  ExpectIv(kIv);

  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction_, &kKey, &kIv));
}

// CTR tests.
class CTRTest : public AesTestInitialized {
 protected:
  CTRTest() { transaction_.mode = kDifAesModeCtr; }
};

TEST_F(CTRTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  ExpectConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_CTR,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });
  ExpectAuxConfig({});
  ExpectKey(kKey, 8);
  ExpectIv(kIv);

  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction_, &kKey, &kIv));
}

// Decrypt tests.
class DecryptTest : public AesTestInitialized {
 protected:
  DecryptTest() {
    transaction_.mode = kDifAesModeEcb;
    transaction_.operation = kDifAesOperationDecrypt;
  }
};

TEST_F(DecryptTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  ExpectConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_DEC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });
  ExpectAuxConfig({});
  ExpectKey(kKey, 8);

  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction_, &kKey, nullptr));
}

// Key size test.
class Key192Test : public AesTestInitialized {
 protected:
  Key192Test() { transaction_.key_len = kDifAesKey192; }
};

TEST_F(Key192Test, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  ExpectConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_192,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });
  ExpectAuxConfig({});
  ExpectKey(kKey, 8);

  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction_, &kKey, nullptr));
}

// Key size test.
class Key256Test : public AesTestInitialized {
 protected:
  Key256Test() { transaction_.key_len = kDifAesKey256; }
};

TEST_F(Key256Test, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  ExpectConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_256,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });
  ExpectAuxConfig({});
  ExpectKey(kKey, 8);

  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction_, &kKey, nullptr));
}

// Manual operation
class ManualOperationTest : public AesTestInitialized {
 protected:
  ManualOperationTest() {
    transaction_.manual_operation = kDifAesManualOperationManual;
  }
};

TEST_F(ManualOperationTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  ExpectConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
      .manual_op = true,
  });
  ExpectAuxConfig({});
  ExpectKey(kKey, 8);

  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction_, &kKey, nullptr));
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

  ExpectWriteMultreg(AES_DATA_IN_0_REG_OFFSET, data_.data,
                     ARRAYSIZE(data_.data));

  EXPECT_DIF_OK(dif_aes_load_data(&aes_, data_));
}

TEST_F(DataTest, DataOut) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {
                                           {AES_STATUS_INPUT_READY_BIT, true},
                                           {AES_STATUS_OUTPUT_VALID_BIT, true},
                                       });

  ExpectReadMultreg(AES_DATA_OUT_0_REG_OFFSET, data_.data,
                    ARRAYSIZE(data_.data));

  dif_aes_data_t out;
  EXPECT_DIF_OK(dif_aes_read_output(&aes_, &out));

  EXPECT_THAT(out.data, ElementsAreArray(data_.data));
}

class DataProcessTest : public AesTestInitialized {
 protected:
  static constexpr size_t kBlockCount = 3;
  static constexpr size_t kBlockSize = 4;
  static constexpr dif_aes_data_t kDataIn[kBlockCount] = {
      {.data = {0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A}},
      {.data = {0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A, 0x5AA5A55A}},
      {.data = {0xA55AA55A, 0xA55AA55A, 0xA55AA55A, 0xA55AA55A}},
  };

  static constexpr dif_aes_data_t kDataOut[kBlockCount] = {
      {.data = {0xB44BB44B, 0xB44BB44B, 0xB44BB44B, 0xB44BB44B}},
      {.data = {0x4BB4B44B, 0x4BB4B44B, 0x4BB4B44B, 0x4BB4B44B}},
      {.data = {0xB44BB44B, 0xB44BB44B, 0xB44BB44B, 0xB44BB44B}},
  };
};
constexpr size_t DataProcessTest::kBlockCount;
constexpr size_t DataProcessTest::kBlockSize;
constexpr dif_aes_data_t DataProcessTest::kDataIn[kBlockCount];
constexpr dif_aes_data_t DataProcessTest::kDataOut[kBlockCount];

TEST_F(DataProcessTest, ThreeBlocksSuccess) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_INPUT_READY_BIT, true},
                                        {AES_STATUS_OUTPUT_VALID_BIT, true}});

  ExpectWriteMultreg(AES_DATA_IN_0_REG_OFFSET, kDataIn[0].data, kBlockSize);
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_INPUT_READY_BIT, true}});

  ExpectWriteMultreg(AES_DATA_IN_0_REG_OFFSET, kDataIn[1].data, kBlockSize);
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_OUTPUT_VALID_BIT, true}});
  ExpectReadMultreg(AES_DATA_OUT_0_REG_OFFSET, kDataOut[0].data, kBlockSize);

  ExpectWriteMultreg(AES_DATA_IN_0_REG_OFFSET, kDataIn[2].data, kBlockSize);
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_OUTPUT_VALID_BIT, true}});
  ExpectReadMultreg(AES_DATA_OUT_0_REG_OFFSET, kDataOut[1].data, kBlockSize);

  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_OUTPUT_VALID_BIT, true}});
  ExpectReadMultreg(AES_DATA_OUT_0_REG_OFFSET, kDataOut[2].data, kBlockSize);

  dif_aes_data_t out[kBlockCount];
  EXPECT_DIF_OK(dif_aes_process_data(&aes_, kDataIn, out, kBlockCount));

  for (size_t i = 0; i < kBlockCount; ++i) {
    EXPECT_THAT(out[i].data, ElementsAreArray(kDataOut[i].data));
  }
}

TEST_F(DataProcessTest, OneBlockSuccess) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_INPUT_READY_BIT, true}});
  ExpectWriteMultreg(AES_DATA_IN_0_REG_OFFSET, kDataIn[0].data, kBlockSize);

  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_OUTPUT_VALID_BIT, true}});
  ExpectReadMultreg(AES_DATA_OUT_0_REG_OFFSET, kDataOut[0].data, kBlockSize);

  dif_aes_data_t out[kBlockCount];
  EXPECT_DIF_OK(dif_aes_process_data(&aes_, kDataIn, out, 1));
  EXPECT_THAT(out[0].data, ElementsAreArray(kDataOut[0].data));
}

TEST_F(DataProcessTest, OneBlockUnavailable) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_INPUT_READY_BIT, false}});

  dif_aes_data_t out[kBlockCount];
  EXPECT_EQ(dif_aes_process_data(&aes_, kDataIn, out, 1), kDifUnavailable);
}
// Read the IV tests.
class IVTest : public AesTestInitialized {};

TEST_F(IVTest, Read) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_IDLE_BIT, true}});

  ExpectReadMultreg(AES_IV_0_REG_OFFSET, kIv.iv, ARRAYSIZE(kIv.iv));
  dif_aes_iv_t iv;
  EXPECT_DIF_OK(dif_aes_read_iv(&aes_, &iv));

  EXPECT_THAT(iv.iv, ElementsAreArray(kIv.iv));
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
  SideloadedKeyTest() { transaction_.key_provider = kDifAesKeySideload; }
};

TEST_F(SideloadedKeyTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  ExpectConfig({.key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
                .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
                .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
                .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
                .key_sideloaded = true});

  ExpectAuxConfig({});
  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction_, nullptr, nullptr));
}
// Mask reseeding.
class MaskReseedingTest : public AesTestInitialized {};

TEST_F(MaskReseedingTest, ReseedPer64Block) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  ExpectConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_64,
  });
  ExpectAuxConfig({});
  ExpectKey(kKey, 8);
  transaction_.mask_reseeding = kDifAesReseedPer64Block;
  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction_, &kKey, nullptr));
}

TEST_F(MaskReseedingTest, ReseedPer8kBlock) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  ExpectConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_8K,
  });
  ExpectAuxConfig({});
  ExpectKey(kKey, 8);
  transaction_.mask_reseeding = kDifAesReseedPer8kBlock;
  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction_, &kKey, nullptr));
}

// Reseed on key change.
class CtrlAuxTest : public AesTestInitialized {};

TEST_F(CtrlAuxTest, Unlock) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  ExpectConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });

  transaction_.reseed_on_key_change = true;
  transaction_.force_masks = true;
  ExpectAuxConfig({
      .reseed_on_key_change = true,
      .force_masks = true,
  });
  ExpectKey(kKey, 8);
  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction_, &kKey, nullptr));
}

TEST_F(CtrlAuxTest, Lock) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  ExpectConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });

  transaction_.reseed_on_key_change = true;
  transaction_.ctrl_aux_lock = true;
  ExpectAuxConfig({.reseed_on_key_change = true, .lock = true});
  ExpectKey(kKey, 8);
  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction_, &kKey, nullptr));
}

TEST_F(CtrlAuxTest, LockedSuccess) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  ExpectConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });

  transaction_.reseed_on_key_change = true;
  transaction_.ctrl_aux_lock = true;

  EXPECT_READ32(AES_CTRL_AUX_REGWEN_REG_OFFSET,
                {{AES_CTRL_AUX_REGWEN_CTRL_AUX_REGWEN_BIT, 0}});
  EXPECT_READ32(AES_CTRL_AUX_SHADOWED_REG_OFFSET,
                {{AES_CTRL_AUX_SHADOWED_KEY_TOUCH_FORCES_RESEED_BIT, true},
                 {AES_CTRL_AUX_SHADOWED_FORCE_MASKS_BIT, false}});
  ExpectKey(kKey, 8);
  EXPECT_DIF_OK(dif_aes_start(&aes_, &transaction_, &kKey, nullptr));
}

TEST_F(CtrlAuxTest, LockedErrorReseedOnKeyChange) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  ExpectConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });

  transaction_.reseed_on_key_change = true;
  transaction_.ctrl_aux_lock = true;

  EXPECT_READ32(AES_CTRL_AUX_REGWEN_REG_OFFSET,
                {{AES_CTRL_AUX_REGWEN_CTRL_AUX_REGWEN_BIT, 0}});
  EXPECT_READ32(AES_CTRL_AUX_SHADOWED_REG_OFFSET,
                {{AES_CTRL_AUX_SHADOWED_KEY_TOUCH_FORCES_RESEED_BIT, false},
                 {AES_CTRL_AUX_SHADOWED_FORCE_MASKS_BIT, false}});

  EXPECT_EQ(dif_aes_start(&aes_, &transaction_, &kKey, nullptr), kDifError);
}

TEST_F(CtrlAuxTest, LockedErrorForceMasks) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  ExpectConfig({
      .key_len = AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
      .mode = AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
      .operation = AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC,
      .mask_reseed = AES_CTRL_SHADOWED_PRNG_RESEED_RATE_VALUE_PER_1,
  });

  transaction_.reseed_on_key_change = true;
  transaction_.ctrl_aux_lock = true;

  EXPECT_READ32(AES_CTRL_AUX_REGWEN_REG_OFFSET,
                {{AES_CTRL_AUX_REGWEN_CTRL_AUX_REGWEN_BIT, 0}});
  EXPECT_READ32(AES_CTRL_AUX_SHADOWED_REG_OFFSET,
                {{AES_CTRL_AUX_SHADOWED_KEY_TOUCH_FORCES_RESEED_BIT, true},
                 {AES_CTRL_AUX_SHADOWED_FORCE_MASKS_BIT, true}});

  EXPECT_EQ(dif_aes_start(&aes_, &transaction_, &kKey, nullptr), kDifError);
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
    transaction_.key_provider = kDifAesKeySoftwareProvided;
    transaction_.mode = kDifAesModeCbc;
  }
};

TEST_F(DifBadArgError, start) {
  EXPECT_DIF_BADARG(dif_aes_start(nullptr, &transaction_, &kKey, &kIv));
  EXPECT_DIF_BADARG(dif_aes_start(&aes_, nullptr, &kKey, &kIv));
  EXPECT_DIF_BADARG(dif_aes_start(&aes_, &transaction_, nullptr, &kIv));
  EXPECT_DIF_BADARG(dif_aes_start(&aes_, &transaction_, &kKey, nullptr));
}

TEST_F(DifBadArgError, reset) { EXPECT_DIF_BADARG(dif_aes_reset(nullptr)); }

TEST_F(DifBadArgError, end) { EXPECT_DIF_BADARG(dif_aes_end(nullptr)); }

TEST_F(DifBadArgError, LoadData) {
  dif_aes_data_t data = {};
  EXPECT_DIF_BADARG(dif_aes_load_data(nullptr, data));
}

TEST_F(DifBadArgError, ReadOutput) {
  dif_aes_data_t data = {};
  EXPECT_DIF_BADARG(dif_aes_read_output(nullptr, &data));
  EXPECT_DIF_BADARG(dif_aes_read_output(&aes_, nullptr));
}

TEST_F(DifBadArgError, Trigger) {
  EXPECT_DIF_BADARG(dif_aes_trigger(nullptr, kDifAesTriggerPrngReseed));
}

TEST_F(DifBadArgError, GetStatus) {
  bool set;
  EXPECT_DIF_BADARG(dif_aes_get_status(nullptr, kDifAesStatusIdle, &set));
  EXPECT_DIF_BADARG(dif_aes_get_status(&aes_, kDifAesStatusIdle, nullptr));
}

TEST_F(DifBadArgError, ReadIV) {
  dif_aes_iv_t iv = {};
  EXPECT_DIF_BADARG(dif_aes_read_iv(nullptr, &iv));
  EXPECT_DIF_BADARG(dif_aes_read_iv(&aes_, nullptr));
}

TEST_F(DifBadArgError, ProcessData) {
  dif_aes_data_t data[1] = {};
  dif_aes_data_t out[1] = {};
  EXPECT_DIF_BADARG(dif_aes_process_data(nullptr, data, out, 1));
  EXPECT_DIF_BADARG(dif_aes_process_data(&aes_, nullptr, out, 1));
  EXPECT_DIF_BADARG(dif_aes_process_data(&aes_, data, nullptr, 1));
  EXPECT_DIF_BADARG(dif_aes_process_data(&aes_, data, out, 0));
}

class DifUnavailableError : public AesTestInitialized {
 protected:
  DifUnavailableError() {
    EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_IDLE_BIT, false}});
  }
};

TEST_F(DifUnavailableError, start) {
  EXPECT_EQ(dif_aes_start(&aes_, &transaction_, &kKey, nullptr),
            kDifUnavailable);
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

TEST_F(DifUnavailableError, ProcessData) {
  dif_aes_data_t data[2] = {};
  dif_aes_data_t out[2] = {};
  EXPECT_EQ(dif_aes_process_data(&aes_, data, out, ARRAYSIZE(data)),
            kDifUnavailable);
}

class DifError : public AesTestInitialized {
 protected:
  DifError() {}
};

TEST_F(DifError, ReadOutput) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, {{AES_STATUS_OUTPUT_VALID_BIT, false}});
  dif_aes_data_t data = {{0}};
  EXPECT_EQ(dif_aes_read_output(&aes_, &data), kDifError);
}
}  // namespace
}  // namespace dif_aes_test
