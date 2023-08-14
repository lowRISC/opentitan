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

  EXPECT_WRITE32(DMA_TOTAL_DATA_SIZE_REG_OFFSET, transaction.size);
  EXPECT_WRITE32(DMA_TRANSFER_WIDTH_REG_OFFSET, transaction.width);

  EXPECT_DIF_OK(dif_dma_configure(&dma_, transaction));
}

INSTANTIATE_TEST_SUITE_P(ConfigureTest, ConfigureTest,
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
                                 .size = 0x1,
                                 .width = kDifDmaTransWidth1Byte,
                             },
                             // Test 1
                             {
                                 .source =
                                     {
                                         .address = 0x34FCA80BC5C5CA67,
                                         .asid = kDifDmaOpentitanExternalFlash,
                                     },
                                 .destination =
                                     {
                                         .address = 0xD0CF2C50,
                                         .asid = kDifDmaSoCControlRegisterBus,
                                     },
                                 .size = 0x2,
                                 .width = kDifDmaTransWidth2Bytes,
                             },
                             // Test 2
                             {
                                 .source =
                                     {
                                         .address = 0x05BA857F8D9C0838,
                                         .asid = kDifDmaOpentitanExternalFlash,
                                     },
                                 .destination =
                                     {
                                         .address = 0x32CD872A12225CCE,
                                         .asid = kDifDmaSoCSystemBus,
                                     },
                                 .size = 0x4,
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
                                         .asid = kDifDmaOpentitanExternalFlash,
                                     },
                                 .size = std::numeric_limits<uint32_t>::max(),
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
  EXPECT_WRITE32(DMA_RANGE_UNLOCK_REGWEN_REG_OFFSET, kMultiBitBool4False);

  EXPECT_DIF_OK(dif_dma_memory_range_lock(&dma_));
}

TEST_F(MemoryRangeLockTest, GetLocked) {
  bool locked = false;
  EXPECT_READ32(DMA_RANGE_UNLOCK_REGWEN_REG_OFFSET, kMultiBitBool4False);

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

}  // namespace dif_dma_test
