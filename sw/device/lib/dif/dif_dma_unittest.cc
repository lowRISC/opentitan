// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_dma.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

extern "C" {
#include "dma_regs.h"  // Generated.
}  // extern "C"

namespace dif_dma_test {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Test;

// Base class for the rest fixtures in this file.
class DmaTest : public testing::Test, public mock_mmio::MmioTest {};

// Base class for the rest of the tests in this file, provides a
// `dif_dma_t` instance.
class DmaTestInitialized : public DmaTest {
 protected:
  dif_dma_t dma_;

  DmaTestInitialized() { EXPECT_DIF_OK(dif_dma_init(dev().region(), &dma_)); }
};

class ConfigureTest
    : public DmaTestInitialized,
      public testing::WithParamInterface<dif_dma_transaction_t> {};

TEST_P(ConfigureTest, Success) {
  dif_dma_transaction_t transaction = GetParam();
  EXPECT_WRITE32(
      DMA_SOURCE_ADDRESS_LO_REG_OFFSET,
      transaction.source.address & std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(DMA_SOURCE_ADDRESS_HI_REG_OFFSET,
                 transaction.source.address >> 32);
  EXPECT_WRITE32(
      DMA_DESTINATION_ADDRESS_LO_REG_OFFSET,
      transaction.destination.address & std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(DMA_DESTINATION_ADDRESS_HI_REG_OFFSET,
                 transaction.destination.address >> 32);

  EXPECT_WRITE32(
      DMA_ADDRESS_SPACE_ID_REG_OFFSET,
      {
          {DMA_ADDRESS_SPACE_ID_SOURCE_ASID_OFFSET, transaction.source.asid},
          {DMA_ADDRESS_SPACE_ID_DESTINATION_ASID_OFFSET,
           transaction.destination.asid},
      });

  EXPECT_WRITE32(DMA_CHUNK_DATA_SIZE_REG_OFFSET, transaction.chunk_size);
  EXPECT_WRITE32(DMA_TOTAL_DATA_SIZE_REG_OFFSET, transaction.total_size);
  EXPECT_WRITE32(DMA_TRANSFER_WIDTH_REG_OFFSET, transaction.width);

  EXPECT_DIF_OK(dif_dma_configure(&dma_, transaction));
}

INSTANTIATE_TEST_SUITE_P(
    ConfigureTest, ConfigureTest,
    testing::ValuesIn(std::vector<dif_dma_transaction_t>{{
        // Test 0
        {
            .source =
                {
                    .address = 0xB05BA84B,
                    .asid = kDifDmaOpentitanInternalBus,
                },
            .destination =
                {
                    .address = 0x721F400F,
                    .asid = kDifDmaOpentitanInternalBus,
                },
            .chunk_size = 0x1,
            .total_size = 0x1,
            .width = kDifDmaTransWidth1Byte,
        },
        // Test 1
        {
            .source =
                {
                    .address = 0x34FCA80BC5C5CA67,
                    .asid = kDifDmaSoCSystemBus,
                },
            .destination =
                {
                    .address = 0xD0CF2C50,
                    .asid = kDifDmaSoCControlRegisterBus,
                },
            .chunk_size = 0x2,
            .total_size = 0x2,
            .width = kDifDmaTransWidth2Bytes,
        },
        // Test 2
        {
            .source =
                {
                    .address = 0x05BA857F8D9C0838,
                    .asid = kDifDmaSoCControlRegisterBus,
                },
            .destination =
                {
                    .address = 0x32CD872A12225CCE,
                    .asid = kDifDmaSoCSystemBus,
                },
            .chunk_size = 0x4,
            .total_size = 0x4,
            .width = kDifDmaTransWidth4Bytes,
        },
        // Test 3
        {
            .source =
                {
                    .address = 0xBFED148856E0555E,
                    .asid = kDifDmaSoCSystemBus,
                },
            .destination =
                {
                    .address = 0x9ECFA11919F684D7,
                    .asid = kDifDmaOpentitanInternalBus,
                },
            .chunk_size = std::numeric_limits<uint32_t>::max(),
            .total_size = std::numeric_limits<uint32_t>::max(),
            .width = kDifDmaTransWidth4Bytes,
        },
    }}));

TEST_F(ConfigureTest, BadArg) {
  dif_dma_transaction_t transaction;
  EXPECT_DIF_BADARG(dif_dma_configure(nullptr, transaction));
}

// Handshake tests
class HandshakeTest : public DmaTestInitialized,
                      public testing::WithParamInterface<dif_dma_handshake_t> {
};

TEST_P(HandshakeTest, EnableSuccess) {
  dif_dma_handshake_t handshake = GetParam();
  EXPECT_READ32(DMA_CONTROL_REG_OFFSET, 0);
  EXPECT_WRITE32(DMA_CONTROL_REG_OFFSET,
                 {
                     {DMA_CONTROL_DATA_DIRECTION_BIT,
                      handshake.direction_from_mem_to_fifo},
                     {DMA_CONTROL_FIFO_AUTO_INCREMENT_ENABLE_BIT,
                      handshake.fifo_auto_increment},
                     {DMA_CONTROL_MEMORY_BUFFER_AUTO_INCREMENT_ENABLE_BIT,
                      handshake.memory_auto_increment},
                     {DMA_CONTROL_HARDWARE_HANDSHAKE_ENABLE_BIT, true},
                 });

  EXPECT_DIF_OK(dif_dma_handshake_enable(&dma_, handshake));
}

TEST_P(HandshakeTest, DisableSuccess) {
  EXPECT_READ32(DMA_CONTROL_REG_OFFSET,
                {
                    {DMA_CONTROL_HARDWARE_HANDSHAKE_ENABLE_BIT, true},
                });
  EXPECT_WRITE32(DMA_CONTROL_REG_OFFSET,
                 {
                     {DMA_CONTROL_HARDWARE_HANDSHAKE_ENABLE_BIT, false},
                 });

  EXPECT_DIF_OK(dif_dma_handshake_disable(&dma_));
}

INSTANTIATE_TEST_SUITE_P(HandshakeTest, HandshakeTest,
                         testing::ValuesIn(std::vector<dif_dma_handshake_t>{{
                             {false, false, false},
                             {false, false, true},
                             {false, true, false},
                             {false, true, true},
                             {true, false, false},
                             {true, true, false},
                             {true, true, true},
                         }}));

TEST_F(HandshakeTest, EnableBadArg) {
  dif_dma_handshake_t handshake;
  EXPECT_DIF_BADARG(dif_dma_handshake_enable(nullptr, handshake));
}

TEST_F(HandshakeTest, DisableBadArg) {
  EXPECT_DIF_BADARG(dif_dma_handshake_disable(nullptr));
}

// DMA start tests
class StartTest
    : public DmaTestInitialized,
      public testing::WithParamInterface<dif_dma_transaction_opcode_t> {};

TEST_P(StartTest, Success) {
  dif_dma_transaction_opcode_t opcode = GetParam();
  EXPECT_READ32(DMA_CONTROL_REG_OFFSET,
                {{DMA_CONTROL_HARDWARE_HANDSHAKE_ENABLE_BIT, true}});
  EXPECT_WRITE32(DMA_CONTROL_REG_OFFSET,
                 {
                     {DMA_CONTROL_OPCODE_OFFSET, opcode},
                     {DMA_CONTROL_INITIAL_TRANSFER_BIT, true},
                     {DMA_CONTROL_GO_BIT, true},
                     {DMA_CONTROL_HARDWARE_HANDSHAKE_ENABLE_BIT, true},
                 });

  EXPECT_DIF_OK(dif_dma_start(&dma_, opcode));
}

INSTANTIATE_TEST_SUITE_P(
    StartTest, StartTest,
    testing::ValuesIn(std::vector<dif_dma_transaction_opcode_t>{{
        kDifDmaCopyOpcode,
    }}));

TEST_F(StartTest, BadArg) {
  EXPECT_DIF_BADARG(dif_dma_start(nullptr, kDifDmaCopyOpcode));
}

// DMA memory range tests
class MemoryRangeTests : public DmaTestInitialized {};

TEST_F(MemoryRangeTests, SetSuccess) {
  enum { kStartAddr = 0xD0CF2C50, kEndAddr = 0xD1CF2C0F };
  EXPECT_WRITE32(DMA_ENABLED_MEMORY_RANGE_BASE_REG_OFFSET, kStartAddr);
  EXPECT_WRITE32(DMA_ENABLED_MEMORY_RANGE_LIMIT_REG_OFFSET, kEndAddr);
  EXPECT_WRITE32(DMA_RANGE_VALID_REG_OFFSET, 1);

  EXPECT_DIF_OK(
      dif_dma_memory_range_set(&dma_, kStartAddr, kEndAddr - kStartAddr + 1));
}

TEST_F(MemoryRangeTests, GetSuccess) {
  enum { kAddress = 0x721F400F, kSize = 0xF0000 };
  EXPECT_READ32(DMA_ENABLED_MEMORY_RANGE_BASE_REG_OFFSET, kAddress);
  EXPECT_READ32(DMA_ENABLED_MEMORY_RANGE_LIMIT_REG_OFFSET,
                kAddress + kSize - 1);

  uint32_t address = 0;
  size_t size = 0;
  EXPECT_DIF_OK(dif_dma_memory_range_get(&dma_, &address, &size));
  EXPECT_EQ(address, kAddress);
  EXPECT_EQ(size, kSize);
}

TEST_F(MemoryRangeTests, GetBadArg) {
  uint32_t address = 0;
  size_t size = 0;
  EXPECT_DIF_BADARG(dif_dma_memory_range_get(nullptr, &address, &size));
  EXPECT_DIF_BADARG(dif_dma_memory_range_get(&dma_, NULL, &size));
  EXPECT_DIF_BADARG(dif_dma_memory_range_get(&dma_, &address, NULL));
}

// DMA abort tests
class AbortTest : public DmaTestInitialized {};

TEST_F(AbortTest, Success) {
  EXPECT_READ32(DMA_CONTROL_REG_OFFSET,
                {{DMA_CONTROL_HARDWARE_HANDSHAKE_ENABLE_BIT, true}});
  EXPECT_WRITE32(DMA_CONTROL_REG_OFFSET,
                 {
                     {DMA_CONTROL_HARDWARE_HANDSHAKE_ENABLE_BIT, true},
                     {DMA_CONTROL_ABORT_BIT, true},
                 });

  EXPECT_DIF_OK(dif_dma_abort(&dma_));
}

TEST_F(AbortTest, BadArg) { EXPECT_DIF_BADARG(dif_dma_abort(nullptr)); }

// DMA Memory range lock tests
class MemoryRangeLockTest : public DmaTestInitialized {};

TEST_F(MemoryRangeLockTest, SetSuccess) {
  EXPECT_WRITE32(DMA_RANGE_REGWEN_REG_OFFSET, kMultiBitBool4False);

  EXPECT_DIF_OK(dif_dma_memory_range_lock(&dma_));
}

TEST_F(MemoryRangeLockTest, GetLocked) {
  bool locked = false;
  EXPECT_READ32(DMA_RANGE_REGWEN_REG_OFFSET, kMultiBitBool4False);

  EXPECT_DIF_OK(dif_dma_is_memory_range_locked(&dma_, &locked));
  EXPECT_TRUE(locked);
}

TEST_F(MemoryRangeLockTest, SetBadArg) {
  EXPECT_DIF_BADARG(dif_dma_memory_range_lock(nullptr));
}

TEST_F(MemoryRangeLockTest, GetBadArg) {
  bool dummy;
  EXPECT_DIF_BADARG(dif_dma_is_memory_range_locked(nullptr, &dummy));
  EXPECT_DIF_BADARG(dif_dma_is_memory_range_locked(&dma_, nullptr));
}

// DMA thresholds tests
class IrqThresholdsTest : public DmaTestInitialized {};

TEST_F(IrqThresholdsTest, SetSuccess) {
  EXPECT_WRITE32(DMA_DESTINATION_ADDRESS_ALMOST_LIMIT_LO_REG_OFFSET,
                 0x9000F000);
  EXPECT_WRITE32(DMA_DESTINATION_ADDRESS_ALMOST_LIMIT_HI_REG_OFFSET,
                 0x80001000);
  EXPECT_WRITE32(DMA_DESTINATION_ADDRESS_LIMIT_LO_REG_OFFSET, 0xE0005000);
  EXPECT_WRITE32(DMA_DESTINATION_ADDRESS_LIMIT_HI_REG_OFFSET, 0xF0001000);

  EXPECT_DIF_OK(dif_dma_irq_thresholds_set(&dma_, 0x800010009000F000,
                                           0xF0001000E0005000));
}

TEST_F(IrqThresholdsTest, GetSuccess) {
  EXPECT_READ32(DMA_DESTINATION_ADDRESS_ALMOST_LIMIT_LO_REG_OFFSET, 0x9000F000);
  EXPECT_READ32(DMA_DESTINATION_ADDRESS_ALMOST_LIMIT_HI_REG_OFFSET, 0x80001000);
  EXPECT_READ32(DMA_DESTINATION_ADDRESS_LIMIT_LO_REG_OFFSET, 0xE0005000);
  EXPECT_READ32(DMA_DESTINATION_ADDRESS_LIMIT_HI_REG_OFFSET, 0xF0001000);

  uint64_t almost = 0;
  uint64_t limit = 0;

  EXPECT_DIF_OK(dif_dma_irq_thresholds_get(&dma_, &almost, &limit));
  EXPECT_EQ(almost, 0x800010009000F000);
  EXPECT_EQ(limit, 0xF0001000E0005000);
}

TEST_F(IrqThresholdsTest, SetBadArg) {
  EXPECT_DIF_BADARG(dif_dma_irq_thresholds_set(nullptr, 0, 0));
  EXPECT_DIF_BADARG(dif_dma_irq_thresholds_set(&dma_, 1, 0));
}

TEST_F(IrqThresholdsTest, GetBadArg) {
  uint64_t dummy;
  EXPECT_DIF_BADARG(dif_dma_irq_thresholds_get(nullptr, &dummy, &dummy));
  EXPECT_DIF_BADARG(dif_dma_irq_thresholds_get(&dma_, nullptr, &dummy));
  EXPECT_DIF_BADARG(dif_dma_irq_thresholds_get(&dma_, &dummy, nullptr));
}

// DMA thresholds tests
typedef struct status_reg {
  uint32_t reg;
  dif_dma_status_t status;
} status_reg_t;
class StatusGetTest : public DmaTestInitialized,
                      public testing::WithParamInterface<status_reg_t> {};

TEST_P(StatusGetTest, GetSuccess) {
  status_reg_t status_arg = GetParam();

  EXPECT_READ32(DMA_STATUS_REG_OFFSET, status_arg.reg);

  dif_dma_status_t status;

  EXPECT_DIF_OK(dif_dma_status_get(&dma_, &status));
  EXPECT_EQ(status, status_arg.status);
}

INSTANTIATE_TEST_SUITE_P(
    StatusGetTest, StatusGetTest,
    testing::ValuesIn(std::vector<status_reg_t>{{
        {1 << DMA_STATUS_BUSY_BIT, kDifDmaStatusBusy},
        {1 << DMA_STATUS_DONE_BIT, kDifDmaStatusDone},
        {1 << DMA_STATUS_ABORTED_BIT, kDifDmaStatusAborted},
        {1 << DMA_STATUS_ERROR_BIT, kDifDmaStatusError},
        {1 << DMA_STATUS_SHA2_DIGEST_VALID_BIT, kDifDmaStatusSha2DigestValid},
    }}));

TEST_F(StatusGetTest, GetBadArg) {
  dif_dma_status_t dummy;
  EXPECT_DIF_BADARG(dif_dma_status_get(nullptr, &dummy));
  EXPECT_DIF_BADARG(dif_dma_status_get(&dma_, nullptr));
}

class StatusWriteTest : public DmaTestInitialized,
                        public testing::WithParamInterface<status_reg_t> {};

TEST_P(StatusWriteTest, SetSuccess) {
  status_reg_t status_arg = GetParam();

  EXPECT_WRITE32(DMA_STATUS_REG_OFFSET, status_arg.reg);

  EXPECT_DIF_OK(dif_dma_status_write(&dma_, status_arg.status));
}

INSTANTIATE_TEST_SUITE_P(
    StatusWriteTest, StatusWriteTest,
    testing::ValuesIn(std::vector<status_reg_t>{{
        {1 << DMA_STATUS_DONE_BIT, kDifDmaStatusDone},
        {1 << DMA_STATUS_ABORTED_BIT, kDifDmaStatusAborted},
        {1 << DMA_STATUS_ERROR_BIT, kDifDmaStatusError},
        {1 << DMA_STATUS_SHA2_DIGEST_VALID_BIT, kDifDmaStatusSha2DigestValid},
    }}));

TEST_F(StatusWriteTest, GetBadArg) {
  dif_dma_status_t dummy = kDifDmaStatusDone;
  EXPECT_DIF_BADARG(dif_dma_status_write(nullptr, dummy));
}

class StatusClearTest : public DmaTestInitialized {};

TEST_F(StatusClearTest, SetSuccess) {
  EXPECT_WRITE32(DMA_STATUS_REG_OFFSET,
                 1 << DMA_STATUS_DONE_BIT | 1 << DMA_STATUS_ABORTED_BIT |
                     1 << DMA_STATUS_ERROR_BIT | 1 << DMA_STATUS_ERROR_BIT);

  EXPECT_DIF_OK(dif_dma_status_clear(&dma_));
}

TEST_F(StatusClearTest, GetBadArg) {
  EXPECT_DIF_BADARG(dif_dma_status_clear(nullptr));
}
typedef struct error_code_reg {
  uint32_t reg;
  dif_dma_error_code_t error_code;
} error_code_reg_t;
class ErrorTest : public DmaTestInitialized,
                  public testing::WithParamInterface<error_code_reg_t> {};

TEST_P(ErrorTest, GetSuccess) {
  error_code_reg_t error_code_arg = GetParam();

  EXPECT_READ32(DMA_ERROR_CODE_REG_OFFSET, error_code_arg.reg);

  dif_dma_error_code error_code;

  EXPECT_DIF_OK(dif_dma_error_code_get(&dma_, &error_code));
  EXPECT_EQ(error_code, error_code_arg.error_code);
}

INSTANTIATE_TEST_SUITE_P(
    ErrorTest, ErrorTest,
    testing::ValuesIn(std::vector<error_code_reg_t>{{
        {1 << DMA_ERROR_CODE_SRC_ADDRESS_ERROR_BIT, kDifDmaErrorSourceAddress},
        {1 << DMA_ERROR_CODE_DST_ADDRESS_ERROR_BIT,
         kDifDmaErrorDestinationAddress},
        {1 << DMA_ERROR_CODE_OPCODE_ERROR_BIT, kDifDmaErrorOpcode},
        {1 << DMA_ERROR_CODE_SIZE_ERROR_BIT, kDifDmaErrorSize},
        {1 << DMA_ERROR_CODE_BUS_ERROR_BIT, kDifDmaErrorBus},
        {1 << DMA_ERROR_CODE_BASE_LIMIT_ERROR_BIT,
         kDifDmaErrorEnableMemoryConfig},
        {1 << DMA_ERROR_CODE_RANGE_VALID_ERROR_BIT, kDifDmaErrorRangeValid},
        {1 << DMA_ERROR_CODE_ASID_ERROR_BIT, kDifDmaErrorInvalidAsid},
    }}));

TEST_F(ErrorTest, GetErrorBadArg) {
  dif_dma_error_code_t dummy;
  EXPECT_DIF_BADARG(dif_dma_error_code_get(nullptr, &dummy));
  EXPECT_DIF_BADARG(dif_dma_error_code_get(&dma_, nullptr));
}

typedef struct status_poll_reg {
  uint32_t reg;
  dif_dma_status_code_t status;
} status_poll_reg_t;

class StatusPollTest : public DmaTestInitialized,
                       public testing::WithParamInterface<status_poll_reg_t> {};

TEST_P(StatusPollTest, GetSuccess) {
  status_poll_reg_t status_arg = GetParam();

  EXPECT_READ32(DMA_STATUS_REG_OFFSET, 0);
  EXPECT_READ32(DMA_STATUS_REG_OFFSET, 0);
  EXPECT_READ32(DMA_STATUS_REG_OFFSET, 0);
  EXPECT_READ32(DMA_STATUS_REG_OFFSET, status_arg.reg);

  EXPECT_DIF_OK(dif_dma_status_poll(&dma_, status_arg.status));
}

INSTANTIATE_TEST_SUITE_P(
    StatusPollTest, StatusPollTest,
    testing::ValuesIn(std::vector<status_poll_reg_t>{{
        {1 << DMA_STATUS_BUSY_BIT, kDifDmaStatusBusy},
        {1 << DMA_STATUS_DONE_BIT, kDifDmaStatusDone},
        {1 << DMA_STATUS_ABORTED_BIT, kDifDmaStatusAborted},
        {1 << DMA_STATUS_ERROR_BIT, kDifDmaStatusError},
        {1 << DMA_STATUS_SHA2_DIGEST_VALID_BIT, kDifDmaStatusSha2DigestValid},
    }}));

TEST_F(StatusPollTest, BadArg) {
  EXPECT_DIF_BADARG(dif_dma_status_poll(nullptr, kDifDmaStatusDone));
}

typedef struct digest_reg {
  dif_dma_transaction_opcode_t opcode;
  uint32_t num_digest_regs;
} digest_reg_t;

class GetDigestTest : public DmaTestInitialized,
                      public testing::WithParamInterface<digest_reg_t> {};

TEST_P(GetDigestTest, GetSuccess) {
  digest_reg_t digest_arg = GetParam();
  uint32_t digest[16] = {0};

  for (uint32_t i = 0; i < digest_arg.num_digest_regs; ++i) {
    EXPECT_READ32(DMA_SHA2_DIGEST_0_REG_OFFSET +
                      (ptrdiff_t)i * (ptrdiff_t)sizeof(uint32_t),
                  i * 1024 + i);
  }

  EXPECT_DIF_OK(dif_dma_sha2_digest_get(&dma_, digest_arg.opcode, digest));

  for (uint32_t i = 0; i < 16; ++i) {
    if (i < digest_arg.num_digest_regs) {
      EXPECT_EQ(digest[i], i * 1024 + i);
    } else {
      EXPECT_EQ(digest[i], 0);
    }
  }
}

INSTANTIATE_TEST_SUITE_P(GetDigestTest, GetDigestTest,
                         testing::ValuesIn(std::vector<digest_reg_t>{{
                             {kDifDmaSha256Opcode, 8},
                             {kDifDmaSha384Opcode, 12},
                             {kDifDmaSha512Opcode, 16},
                             {kDifDmaCopyOpcode, 0},
                         }}));

TEST_F(GetDigestTest, BadArg) {
  uint32_t digest[16];
  EXPECT_DIF_BADARG(
      dif_dma_sha2_digest_get(nullptr, kDifDmaSha256Opcode, digest));
  EXPECT_DIF_BADARG(
      dif_dma_sha2_digest_get(&dma_, kDifDmaSha256Opcode, nullptr));
}

// DMA handshake irq enable tests
class HandshakeEnableIrqTest : public DmaTestInitialized {};

TEST_F(HandshakeEnableIrqTest, Success) {
  EXPECT_WRITE32(DMA_HANDSHAKE_INTERRUPT_ENABLE_REG_OFFSET, 0x3);

  EXPECT_DIF_OK(dif_dma_handshake_irq_enable(&dma_, 0x3));
}

TEST_F(HandshakeEnableIrqTest, BadArg) {
  EXPECT_DIF_BADARG(dif_dma_handshake_irq_enable(nullptr, 0x3));
}

// DMA handshake irq clear tests
class HandshakeClearIrqTest : public DmaTestInitialized {};

TEST_F(HandshakeClearIrqTest, Success) {
  EXPECT_WRITE32(DMA_CLEAR_INT_SRC_REG_OFFSET, 0x3);

  EXPECT_DIF_OK(dif_dma_handshake_clear_irq(&dma_, 0x3));
}

TEST_F(HandshakeClearIrqTest, BadArg) {
  EXPECT_DIF_BADARG(dif_dma_handshake_clear_irq(nullptr, 0x3));
}

// DMA handshake irq clear bus tests
class HandshakeClearBusTest : public DmaTestInitialized {};

TEST_F(HandshakeClearBusTest, Success) {
  EXPECT_WRITE32(DMA_CLEAR_INT_BUS_REG_OFFSET, 0x2);

  EXPECT_DIF_OK(dif_dma_handshake_clear_irq_bus(&dma_, 0x2));
}

TEST_F(HandshakeClearBusTest, BadArg) {
  EXPECT_DIF_BADARG(dif_dma_handshake_clear_irq_bus(nullptr, 0x2));
}

typedef struct dma_clear_irq_reg {
  uint32_t reg;
  dif_dma_int_idx_t idx;
} dma_clear_irq_reg_t;

class HandshakeClearAddressTest
    : public DmaTestInitialized,
      public testing::WithParamInterface<dma_clear_irq_reg_t> {};

TEST_P(HandshakeClearAddressTest, GetSuccess) {
  dma_clear_irq_reg_t clear_irq_reg = GetParam();

  EXPECT_WRITE32(clear_irq_reg.reg, 0x123456);

  EXPECT_DIF_OK(dif_dma_int_src_addr(&dma_, clear_irq_reg.idx, 0x123456));
}

INSTANTIATE_TEST_SUITE_P(
    HandshakeClearAddressTest, HandshakeClearAddressTest,
    testing::ValuesIn(std::vector<dma_clear_irq_reg_t>{{
        {DMA_INT_SOURCE_ADDR_0_REG_OFFSET, kDifDmaIntClearIdx0},
        {DMA_INT_SOURCE_ADDR_1_REG_OFFSET, kDifDmaIntClearIdx1},
        {DMA_INT_SOURCE_ADDR_2_REG_OFFSET, kDifDmaIntClearIdx2},
        {DMA_INT_SOURCE_ADDR_3_REG_OFFSET, kDifDmaIntClearIdx3},
        {DMA_INT_SOURCE_ADDR_4_REG_OFFSET, kDifDmaIntClearIdx4},
        {DMA_INT_SOURCE_ADDR_5_REG_OFFSET, kDifDmaIntClearIdx5},
        {DMA_INT_SOURCE_ADDR_6_REG_OFFSET, kDifDmaIntClearIdx6},
        {DMA_INT_SOURCE_ADDR_7_REG_OFFSET, kDifDmaIntClearIdx7},
        {DMA_INT_SOURCE_ADDR_8_REG_OFFSET, kDifDmaIntClearIdx8},
        {DMA_INT_SOURCE_ADDR_9_REG_OFFSET, kDifDmaIntClearIdx9},
        {DMA_INT_SOURCE_ADDR_10_REG_OFFSET, kDifDmaIntClearIdx10},
    }}));

TEST_F(HandshakeClearAddressTest, BadArg) {
  EXPECT_DIF_BADARG(
      dif_dma_int_src_addr(nullptr, kDifDmaIntClearIdx0, 0x12345));
}

class HandshakeClearValueTest
    : public DmaTestInitialized,
      public testing::WithParamInterface<dma_clear_irq_reg_t> {};

TEST_P(HandshakeClearValueTest, GetSuccess) {
  dma_clear_irq_reg_t clear_irq_reg = GetParam();

  EXPECT_WRITE32(clear_irq_reg.reg, 0x123456);

  EXPECT_DIF_OK(dif_dma_int_write_value(&dma_, clear_irq_reg.idx, 0x123456));
}

INSTANTIATE_TEST_SUITE_P(
    HandshakeClearValueTest, HandshakeClearValueTest,
    testing::ValuesIn(std::vector<dma_clear_irq_reg_t>{{
        {DMA_INT_SOURCE_WR_VAL_0_REG_OFFSET, kDifDmaIntClearIdx0},
        {DMA_INT_SOURCE_WR_VAL_1_REG_OFFSET, kDifDmaIntClearIdx1},
        {DMA_INT_SOURCE_WR_VAL_2_REG_OFFSET, kDifDmaIntClearIdx2},
        {DMA_INT_SOURCE_WR_VAL_3_REG_OFFSET, kDifDmaIntClearIdx3},
        {DMA_INT_SOURCE_WR_VAL_4_REG_OFFSET, kDifDmaIntClearIdx4},
        {DMA_INT_SOURCE_WR_VAL_5_REG_OFFSET, kDifDmaIntClearIdx5},
        {DMA_INT_SOURCE_WR_VAL_6_REG_OFFSET, kDifDmaIntClearIdx6},
        {DMA_INT_SOURCE_WR_VAL_7_REG_OFFSET, kDifDmaIntClearIdx7},
        {DMA_INT_SOURCE_WR_VAL_8_REG_OFFSET, kDifDmaIntClearIdx8},
        {DMA_INT_SOURCE_WR_VAL_9_REG_OFFSET, kDifDmaIntClearIdx9},
        {DMA_INT_SOURCE_WR_VAL_10_REG_OFFSET, kDifDmaIntClearIdx10},
    }}));

TEST_F(HandshakeClearValueTest, BadArg) {
  EXPECT_DIF_BADARG(
      dif_dma_int_write_value(nullptr, kDifDmaIntClearIdx0, 0x4567));
}

}  // namespace dif_dma_test
