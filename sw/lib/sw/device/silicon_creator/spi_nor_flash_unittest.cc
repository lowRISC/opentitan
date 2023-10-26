// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/lib/sw/device/silicon_creator/spi_nor_flash.h"

#include <array>
#include <cstring>

#include "gtest/gtest.h"
#include "sw/device/silicon_creator/lib/drivers/mock_spi_host.h"
#include "sw/lib/sw/device/silicon_creator/testing/rom_test.h"

namespace spi_nor_unittest {
namespace {
using ::testing::_;
using ::testing::DoAll;
using ::testing::Return;
using ::testing::SetArgPointee;

class SpiNorFlashTest : public rom_test::RomTest {
 protected:
  rom_test::MockSpiHost spi_host_;

  void ExpectTransactionSingleCmd(uint32_t csid, uint8_t cmd) {
    EXPECT_CALL(spi_host_, Transaction(csid, _, 1))
        .WillOnce([cmd](auto, const spi_host_segment_t *segments, auto) {
          EXPECT_EQ(segments[0].type, kSpiHostSegmentTypeOpcode);
          EXPECT_EQ(segments[0].opcode.opcode, cmd);
          return kErrorOk;
        });
  }

  template <size_t N>
  void ExpectTransactionCmdWithRead(uint32_t csid, uint8_t cmd,
                                    std::array<uint8_t, N> data) {
    EXPECT_CALL(spi_host_, Transaction(csid, _, 2))
        .WillOnce([cmd, data](auto, const spi_host_segment_t *segments, auto) {
          EXPECT_EQ(segments[0].type, kSpiHostSegmentTypeOpcode);
          EXPECT_EQ(segments[0].opcode.opcode, cmd);
          EXPECT_EQ(segments[1].type, kSpiHostSegmentTypeRx);
          EXPECT_EQ(segments[1].rx.length, N);
          uint8_t *buf = static_cast<uint8_t *>(segments[1].rx.buf);
          std::copy_n(data.begin(), N, buf);
          return kErrorOk;
        });
  }

  void ExpectFlashInit(uint32_t csid, uint32_t exp_jedec_id) {
    std::array<uint8_t, 3> jedec_buf = {
        static_cast<uint8_t>(exp_jedec_id >> 16),
        static_cast<uint8_t>(exp_jedec_id >> 8),
        static_cast<uint8_t>(exp_jedec_id)};

    // Send reset sequence to memory
    ExpectTransactionSingleCmd(csid, 0x66);
    ExpectTransactionSingleCmd(csid, 0x99);

    // Exit 4 byte address mode
    ExpectTransactionSingleCmd(csid, 0xe9);

    // Read JEDEC ID
    ExpectTransactionCmdWithRead(csid, 0x9f, jedec_buf);
  }

  template <size_t N>
  void ExpectTransactionFastRead3b(uint32_t csid, uint32_t addr, uint32_t len,
                                   std::array<uint8_t, N> flash_data) {
    EXPECT_CALL(spi_host_, Transaction(csid, _, 4))
        .WillOnce([addr, len, flash_data](
                      auto, const spi_host_segment_t *segments, auto) {
          EXPECT_LT(addr, N);
          EXPECT_LT(addr + len, N);
          EXPECT_EQ(segments[0].type, kSpiHostSegmentTypeOpcode);
          EXPECT_EQ(segments[0].opcode.opcode, 0x0b);
          EXPECT_EQ(segments[1].type, kSpiHostSegmentTypeAddress);
          EXPECT_EQ(segments[1].address.mode, kSpiHostAddrMode3b);
          EXPECT_EQ(segments[1].address.address, addr);
          EXPECT_EQ(segments[2].type, kSpiHostSegmentTypeDummy);
          EXPECT_EQ(segments[3].type, kSpiHostSegmentTypeRx);
          EXPECT_EQ(segments[3].rx.length, len);
          uint8_t *buf = static_cast<uint8_t *>(segments[3].rx.buf);
          std::copy_n(flash_data.begin() + addr, len, buf);
          return kErrorOk;
        });
  }
};

class SpiNorFlashInitTest : public SpiNorFlashTest {};

TEST_F(SpiNorFlashInitTest, Init) {
  const uint32_t kCsid = 0;
  const uint32_t kJedecId = 0x123456;

  ExpectFlashInit(kCsid, kJedecId);

  uint32_t jedec_id = ~kJedecId;
  EXPECT_EQ(spi_nor_flash_init(kCsid, &jedec_id), kErrorOk);

  // Check that returned JEDEC ID matches
  EXPECT_EQ(jedec_id, kJedecId);
}

TEST_F(SpiNorFlashInitTest, InitFlashNotDetected1) {
  const uint32_t kCsid = 1;
  const uint32_t kJedecId = 0;

  ExpectFlashInit(kCsid, kJedecId);

  uint32_t jedec_id = ~kJedecId;
  EXPECT_EQ(spi_nor_flash_init(kCsid, &jedec_id), kErrorSpiNorFlashNotFound);

  // Check that return variable was not changed
  EXPECT_EQ(jedec_id, ~kJedecId);
}

TEST_F(SpiNorFlashInitTest, InitFlashNotDetected2) {
  const uint32_t kCsid = 1;
  const uint32_t kJedecId = ~0;

  ExpectFlashInit(kCsid, kJedecId);

  uint32_t jedec_id = ~kJedecId;
  EXPECT_EQ(spi_nor_flash_init(kCsid, &jedec_id), kErrorSpiNorFlashNotFound);

  // Check that return variable was not changed
  EXPECT_EQ(jedec_id, ~kJedecId);
}

class SpiNorFlashReadTest : public SpiNorFlashTest {};

TEST_F(SpiNorFlashReadTest, Read) {
  const uint32_t kCsid = 1;
  std::array<uint8_t, 1024> flash_data;
  uint32_t addr, size;

  // Generate random test parameters
  ::srand(0);
  std::generate(flash_data.begin(), flash_data.end(), ::rand);
  addr = ::rand() % flash_data.size();
  size = ::rand() % (flash_data.size() - addr);

  // Fast Read
  ExpectTransactionFastRead3b(kCsid, addr, size, flash_data);

  std::vector<uint8_t> actual(size);
  EXPECT_EQ(spi_nor_flash_read(kCsid, addr, actual.size(), actual.data()),
            kErrorOk);
  EXPECT_THAT(actual, testing::ElementsAreArray(
                          std::vector<int>(flash_data.begin() + addr,
                                           flash_data.begin() + addr + size)));
}

TEST_F(SpiNorFlashReadTest, ReadInvalidAddress) {
  const uint32_t kCsid = 2;
  const uint32_t kAddr = 1 << 24;
  const uint32_t kSize = 1;

  EXPECT_EQ(spi_nor_flash_read(kCsid, kAddr, kSize, NULL),
            kErrorSpiNorFlashInvalidArgument);
}

}  // namespace
}  // namespace spi_nor_unittest
