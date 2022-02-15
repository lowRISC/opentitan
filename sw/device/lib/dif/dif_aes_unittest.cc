// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_aes.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

extern "C" {
#include "aes_regs.h"  // Generated.
}  // extern "C"

namespace dif_aes_test {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Test;

// Base class for the rest fixtures in this file.
class AesTest : public testing::Test, public mock_mmio::MmioTest {
 public:
  void setExpectedKey(const dif_aes_key_share_t &key, uint32_t key_size = 8) {
    for (uint32_t i = 0; i < key_size; ++i) {
      ptrdiff_t offset = AES_KEY_SHARE0_0_REG_OFFSET + (i * sizeof(uint32_t));
      EXPECT_WRITE32(offset, key.share0[i]);
    }

    for (uint32_t i = 0; i < key_size; ++i) {
      ptrdiff_t offset = AES_KEY_SHARE1_0_REG_OFFSET + (i * sizeof(uint32_t));
      EXPECT_WRITE32(offset, key.share1[i]);
    }
  }

  void setExpectedIv(const dif_aes_iv_t &iv, const uint32_t kIvSize = 4) {
    for (uint32_t i = 0; i < kIvSize; ++i) {
      ptrdiff_t offset = AES_IV_0_REG_OFFSET + (i * sizeof(uint32_t));
      EXPECT_WRITE32(offset, iv.iv[i]);
    }
  }
  void setExpectedConfig(uint32_t key_len, uint32_t mode, uint32_t operation) {
    for (int i = 0; i < 2; i++) {
      EXPECT_WRITE32(AES_CTRL_SHADOWED_REG_OFFSET,
                     {{AES_CTRL_SHADOWED_KEY_LEN_OFFSET, key_len},
                      {AES_CTRL_SHADOWED_MODE_OFFSET, mode},
                      {AES_CTRL_SHADOWED_OPERATION_OFFSET, operation},
                      {AES_CTRL_SHADOWED_MANUAL_OPERATION_BIT, false},
                      {AES_CTRL_SHADOWED_FORCE_ZERO_MASKS_BIT, false}});
    }
  }
};

// Init tests
class AesInitTest : public AesTest {};

TEST_F(AesInitTest, NullArgs) {
  EXPECT_EQ(dif_aes_init(dev().region(), nullptr), kDifBadArg);
}

TEST_F(AesInitTest, Sucess) {
  dif_aes_t aes;
  EXPECT_EQ(dif_aes_init(dev().region(), &aes), kDifOk);
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
  };

  const dif_aes_key_share_t kKey_ = {
      .share0 = {0x59, 0x70, 0x33, 0x73, 0x36, 0x76, 0x39, 0x79},
      .share1 = {0x4B, 0x61, 0x50, 0x64, 0x53, 0x67, 0x56, 0x6B}};

  const dif_aes_iv_t kIv_ = {0x50, 0x64, 0x53, 0x67};

  AesTestInitialized() {
    EXPECT_EQ(dif_aes_init(dev().region(), &aes_), kDifOk);
  }
};

// ECB tests
class EcbTest : public AesTestInitialized {
 protected:
  EcbTest() { transaction.mode = kDifAesModeEcb; }
};

TEST_F(EcbTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  setExpectedConfig(AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
                    AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
                    AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC);
  setExpectedKey(kKey_, 8);

  EXPECT_EQ(dif_aes_start(&aes_, &transaction, kKey_, NULL), kDifOk);
}

class CbcTest : public AesTestInitialized {
 protected:
  CbcTest() { transaction.mode = kDifAesModeCbc; }
};

TEST_F(CbcTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  setExpectedConfig(AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
                    AES_CTRL_SHADOWED_MODE_VALUE_AES_CBC,
                    AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC);
  setExpectedKey(kKey_, 8);
  setExpectedIv(kIv_);

  EXPECT_EQ(dif_aes_start(&aes_, &transaction, kKey_, &kIv_), kDifOk);
}

// CFB tests
class CFBTest : public AesTestInitialized {
 protected:
  CFBTest() { transaction.mode = kDifAesModeCfb; }
};

TEST_F(CFBTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  setExpectedConfig(AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
                    AES_CTRL_SHADOWED_MODE_VALUE_AES_CFB,
                    AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC);
  setExpectedKey(kKey_, 8);
  setExpectedIv(kIv_);

  EXPECT_EQ(dif_aes_start(&aes_, &transaction, kKey_, &kIv_), kDifOk);
}

// OFB tests
class OFBTest : public AesTestInitialized {
 protected:
  OFBTest() { transaction.mode = kDifAesModeOfb; }
};

TEST_F(OFBTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  setExpectedConfig(AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
                    AES_CTRL_SHADOWED_MODE_VALUE_AES_OFB,
                    AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC);
  setExpectedKey(kKey_, 8);
  setExpectedIv(kIv_);

  EXPECT_EQ(dif_aes_start(&aes_, &transaction, kKey_, &kIv_), kDifOk);
}

// CTR tests
class CTRTest : public AesTestInitialized {
 protected:
  CTRTest() { transaction.mode = kDifAesModeCtr; }
};

TEST_F(CTRTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  setExpectedConfig(AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
                    AES_CTRL_SHADOWED_MODE_VALUE_AES_CTR,
                    AES_CTRL_SHADOWED_OPERATION_VALUE_AES_ENC);
  setExpectedKey(kKey_, 8);
  setExpectedIv(kIv_);

  EXPECT_EQ(dif_aes_start(&aes_, &transaction, kKey_, &kIv_), kDifOk);
}

// Decrypt tests
class DecryptTest : public AesTestInitialized {
 protected:
  DecryptTest() {
    transaction.mode = kDifAesModeEcb;
    transaction.operation = kDifAesOperationDecrypt;
  }
};

TEST_F(DecryptTest, start) {
  EXPECT_READ32(AES_STATUS_REG_OFFSET, 1);
  setExpectedConfig(AES_CTRL_SHADOWED_KEY_LEN_VALUE_AES_128,
                    AES_CTRL_SHADOWED_MODE_VALUE_AES_ECB,
                    AES_CTRL_SHADOWED_OPERATION_VALUE_AES_DEC);
  setExpectedKey(kKey_, 8);

  EXPECT_EQ(dif_aes_start(&aes_, &transaction, kKey_, NULL), kDifOk);
}

}  // namespace
}  // namespace dif_aes_test
