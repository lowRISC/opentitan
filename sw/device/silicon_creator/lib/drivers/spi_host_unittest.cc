// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/drivers/spi_host.h"

#include <array>
#include <cstring>
#include <limits>

#include "gtest/gtest.h"
#include "sw/lib/sw/device/base/memory.h"
#include "sw/lib/sw/device/base/mock_abs_mmio.h"
#include "sw/lib/sw/device/silicon_creator/error.h"
#include "sw/lib/sw/device/silicon_creator/testing/rom_test.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "spi_host_regs.h"

// Helper macros to make expectations easier to read.
#define EXPECT_COMMAND_REG(length, width, direction, last_segment)       \
  EXPECT_ABS_WRITE32(base_ + SPI_HOST_COMMAND_REG_OFFSET,                \
                     {                                                   \
                         {SPI_HOST_COMMAND_LEN_OFFSET, (length)-1},      \
                         {SPI_HOST_COMMAND_SPEED_OFFSET, width},         \
                         {SPI_HOST_COMMAND_DIRECTION_OFFSET, direction}, \
                         {SPI_HOST_COMMAND_CSAAT_BIT, !(last_segment)},  \
                     })

#define EXPECT_READY(ready)                             \
  EXPECT_ABS_READ32(base_ + SPI_HOST_STATUS_REG_OFFSET, \
                    {{SPI_HOST_STATUS_READY_BIT, ready}})

#define EXPECT_TXQD(txqd)                               \
  EXPECT_ABS_READ32(base_ + SPI_HOST_STATUS_REG_OFFSET, \
                    {{SPI_HOST_STATUS_TXQD_OFFSET, txqd}})

#define EXPECT_RXQD(rxqd)                               \
  EXPECT_ABS_READ32(base_ + SPI_HOST_STATUS_REG_OFFSET, \
                    {{SPI_HOST_STATUS_RXQD_OFFSET, rxqd}})

namespace spi_host_unittest {
namespace {
using ::testing::NotNull;
using ::testing::SetArgPointee;

class SpiHostTest : public rom_test::RomTest {
 protected:
  uint32_t base_ = TOP_DARJEELING_SPI_HOST0_BASE_ADDR;
  rom_test::MockAbsMmio mmio_;
};

class InitTest : public SpiHostTest {};

TEST_F(InitTest, Init) {
  // reset sequence
  EXPECT_ABS_WRITE32(base_ + SPI_HOST_CONTROL_REG_OFFSET,
                     {
                         {SPI_HOST_CONTROL_SW_RST_BIT, true},
                     });

  EXPECT_ABS_READ32(base_ + SPI_HOST_STATUS_REG_OFFSET,
                    {
                        {SPI_HOST_STATUS_ACTIVE_BIT, true},
                    });
  EXPECT_ABS_READ32(base_ + SPI_HOST_STATUS_REG_OFFSET, 0);

  EXPECT_ABS_READ32(base_ + SPI_HOST_STATUS_REG_OFFSET,
                    {
                        {SPI_HOST_STATUS_TXQD_OFFSET, 1},
                        {SPI_HOST_STATUS_RXQD_OFFSET, 1},
                    });
  EXPECT_ABS_READ32(base_ + SPI_HOST_STATUS_REG_OFFSET,
                    {
                        {SPI_HOST_STATUS_RXQD_OFFSET, 1},
                    });
  EXPECT_ABS_READ32(base_ + SPI_HOST_STATUS_REG_OFFSET, 0);

  EXPECT_ABS_WRITE32(base_ + SPI_HOST_CONTROL_REG_OFFSET, 0);

  // clock config
  EXPECT_ABS_WRITE32(base_ + SPI_HOST_CONFIGOPTS_REG_OFFSET,
                     {
                         {SPI_HOST_CONFIGOPTS_CLKDIV_0_OFFSET, 1},
                     });

  // enable sequence
  EXPECT_ABS_READ32(base_ + SPI_HOST_CONTROL_REG_OFFSET, 0);
  EXPECT_ABS_WRITE32(base_ + SPI_HOST_CONTROL_REG_OFFSET,
                     {
                         {SPI_HOST_CONTROL_SPIEN_BIT, true},
                         {SPI_HOST_CONTROL_OUTPUT_EN_BIT, true},
                     });

  spi_host_init(1);
}

class TransactionTest : public SpiHostTest {};

// Checks that an opcode segment is sent correctly.
TEST_F(TransactionTest, IssueOpcode) {
  spi_host_segment_t segment;
  segment.type = kSpiHostSegmentTypeOpcode;
  segment.width = kSpiHostWidthStandard;
  segment.opcode.opcode = 0x5a;

  EXPECT_ABS_WRITE32(base_ + SPI_HOST_CSID_REG_OFFSET, 0);
  EXPECT_READY(true);
  EXPECT_TXQD(0);
  // Opcodes are written directly to the FIFO register.
  EXPECT_ABS_WRITE8(base_ + SPI_HOST_TXDATA_REG_OFFSET, 0x5a);
  EXPECT_COMMAND_REG(/*length=*/1, /*width=*/kSpiHostWidthStandard,
                     /*direction=*/kSpiHostDirectionTx, /*last=*/true);

  EXPECT_EQ(spi_host_transaction(0, &segment, 1), kErrorOk);
}

// Checks that an address segment is sent correctly in 3-byte mode.
TEST_F(TransactionTest, IssueAddressMode3b) {
  spi_host_segment_t segment;
  segment.width = kSpiHostWidthStandard;
  segment.type = kSpiHostSegmentTypeAddress;
  segment.address.mode = kSpiHostAddrMode3b;
  segment.address.address = 0x112233;

  EXPECT_ABS_WRITE32(base_ + SPI_HOST_CSID_REG_OFFSET, 0);
  EXPECT_READY(true);
  EXPECT_TXQD(0);
  // SPI addresses are written directly to the FIFO register.
  EXPECT_ABS_WRITE32(base_ + SPI_HOST_TXDATA_REG_OFFSET, 0x332211);
  EXPECT_COMMAND_REG(/*length=*/3, /*width=*/kSpiHostWidthStandard,
                     /*direction=*/kSpiHostDirectionTx, /*last=*/true);

  EXPECT_EQ(spi_host_transaction(0, &segment, 1), kErrorOk);
}

// Checks that an address segment is sent correctly in 4-byte mode.
TEST_F(TransactionTest, IssueAddressMode4b) {
  spi_host_segment segment;
  segment.type = kSpiHostSegmentTypeAddress;
  segment.width = kSpiHostWidthStandard;
  segment.address.mode = kSpiHostAddrMode4b;
  segment.address.address = 0x11223344;

  EXPECT_ABS_WRITE32(base_ + SPI_HOST_CSID_REG_OFFSET, 0);
  EXPECT_READY(true);
  EXPECT_TXQD(0);
  // SPI addresses are written directly to the FIFO register.
  EXPECT_ABS_WRITE32(base_ + SPI_HOST_TXDATA_REG_OFFSET, 0x44332211);
  EXPECT_COMMAND_REG(/*length=*/4, /*width=*/kSpiHostWidthStandard,
                     /*direction=*/kSpiHostDirectionTx, /*last=*/true);

  EXPECT_EQ(spi_host_transaction(0, &segment, 1), kErrorOk);
}

// Checks that a dummy segment is sent correctly.
TEST_F(TransactionTest, IssueDummy) {
  spi_host_segment segment;
  segment.type = kSpiHostSegmentTypeDummy;
  segment.width = kSpiHostWidthStandard;
  segment.dummy.length = 8;

  EXPECT_ABS_WRITE32(base_ + SPI_HOST_CSID_REG_OFFSET, 0);
  EXPECT_READY(true);
  EXPECT_COMMAND_REG(/*length=*/8, /*width=*/kSpiHostWidthStandard,
                     /*direction=*/kSpiHostDirectionDummy, /*last=*/true);

  EXPECT_EQ(spi_host_transaction(0, &segment, 1), kErrorOk);
}

// Checks that a transmit segment is sent correctly.
TEST_F(TransactionTest, TransmitDual) {
  alignas(4) uint8_t txbuf[12] = {0x12, 0x34, 0x56, 0x78, 0xab, 0xcd,
                                  0xef, 0x01, 0x02, 0x03, 0x04, 0x05};
  spi_host_segment segment;
  segment.type = kSpiHostSegmentTypeTx;
  segment.width = kSpiHostWidthDual;
  segment.tx.buf = txbuf;
  segment.tx.length = sizeof(txbuf);

  EXPECT_ABS_WRITE32(base_ + SPI_HOST_CSID_REG_OFFSET, 0);
  EXPECT_READY(true);
  EXPECT_TXQD(0);
  EXPECT_ABS_WRITE32(base_ + SPI_HOST_TXDATA_REG_OFFSET, read_32(&txbuf[0]));
  EXPECT_TXQD(4);
  EXPECT_ABS_WRITE32(base_ + SPI_HOST_TXDATA_REG_OFFSET, read_32(&txbuf[4]));
  EXPECT_TXQD(8);
  EXPECT_ABS_WRITE32(base_ + SPI_HOST_TXDATA_REG_OFFSET, read_32(&txbuf[8]));
  EXPECT_COMMAND_REG(/*length=*/12, /*width=*/kSpiHostWidthDual,
                     /*direction=*/kSpiHostDirectionTx, /*last=*/true);

  EXPECT_EQ(spi_host_transaction(0, &segment, 1), kErrorOk);
}

// Checks that an unaligned transmit segment is sent correctly.
TEST_F(TransactionTest, TransmitUnalignedQuad) {
  alignas(4) uint8_t txbuf[13] = {0x42, 0x12, 0x34, 0x56, 0x78, 0xab, 0xcd,
                                  0xef, 0x01, 0x02, 0x03, 0x04, 0x05};
  spi_host_segment segment;
  segment.type = kSpiHostSegmentTypeTx;
  segment.width = kSpiHostWidthDual;
  segment.tx.buf = &txbuf[1];
  segment.tx.length = sizeof(txbuf) - 1;

  EXPECT_ABS_WRITE32(base_ + SPI_HOST_CSID_REG_OFFSET, 0);
  EXPECT_READY(true);
  EXPECT_TXQD(0);
  EXPECT_ABS_WRITE8(base_ + SPI_HOST_TXDATA_REG_OFFSET, txbuf[1]);
  EXPECT_TXQD(1);
  EXPECT_ABS_WRITE8(base_ + SPI_HOST_TXDATA_REG_OFFSET, txbuf[2]);
  EXPECT_TXQD(2);
  EXPECT_ABS_WRITE8(base_ + SPI_HOST_TXDATA_REG_OFFSET, txbuf[3]);
  EXPECT_TXQD(3);
  EXPECT_ABS_WRITE32(base_ + SPI_HOST_TXDATA_REG_OFFSET, read_32(&txbuf[4]));
  EXPECT_TXQD(7);
  EXPECT_ABS_WRITE32(base_ + SPI_HOST_TXDATA_REG_OFFSET, read_32(&txbuf[8]));
  EXPECT_TXQD(11);
  EXPECT_ABS_WRITE8(base_ + SPI_HOST_TXDATA_REG_OFFSET, txbuf[12]);
  EXPECT_COMMAND_REG(/*length=*/12, /*width=*/kSpiHostWidthDual,
                     /*direction=*/kSpiHostDirectionTx, /*last=*/true);

  EXPECT_EQ(spi_host_transaction(0, &segment, 1), kErrorOk);
}

// Checks that a receive segment is received correctly.
TEST_F(TransactionTest, ReceiveQuad) {
  uint8_t test_data[12] = {0x12, 0x34, 0x56, 0x78, 0xab, 0xcd,
                           0xef, 0x01, 0x02, 0x03, 0x04, 0x05};
  alignas(4) uint8_t buf[12];
  spi_host_segment_t segment;
  segment.type = kSpiHostSegmentTypeRx;
  segment.width = kSpiHostWidthQuad;
  segment.rx.buf = buf;
  segment.rx.length = sizeof(buf);

  EXPECT_ABS_WRITE32(base_ + SPI_HOST_CSID_REG_OFFSET, 0);
  EXPECT_READY(true);
  EXPECT_COMMAND_REG(/*length=*/12, /*width=*/kSpiHostWidthQuad,
                     /*direction=*/kSpiHostDirectionRx, /*last=*/true);
  EXPECT_RXQD(12);
  EXPECT_ABS_READ32(base_ + SPI_HOST_RXDATA_REG_OFFSET, read_32(&test_data[0]));
  EXPECT_RXQD(8);
  EXPECT_ABS_READ32(base_ + SPI_HOST_RXDATA_REG_OFFSET, read_32(&test_data[4]));
  EXPECT_RXQD(4);
  EXPECT_ABS_READ32(base_ + SPI_HOST_RXDATA_REG_OFFSET, read_32(&test_data[8]));

  EXPECT_EQ(spi_host_transaction(0, &segment, 1), kErrorOk);
  for (unsigned i = 0; i < sizeof(buf); ++i) {
    EXPECT_EQ(buf[i], test_data[i]);
  }
}

// Checks that an unaligned receive segment is received correctly.
TEST_F(TransactionTest, ReceiveUnalignedDual) {
  uint8_t test_data[12] = {0x12, 0x34, 0x56, 0x78, 0xab, 0xcd,
                           0xef, 0x01, 0x02, 0x03, 0x04, 0x05};
  alignas(4) uint8_t buf[13];
  spi_host_segment_t segment;
  segment.type = kSpiHostSegmentTypeRx;
  segment.width = kSpiHostWidthQuad;
  segment.rx.buf = &buf[1];
  segment.rx.length = sizeof(buf) - 1;

  EXPECT_ABS_WRITE32(base_ + SPI_HOST_CSID_REG_OFFSET, 0);
  EXPECT_READY(true);
  EXPECT_COMMAND_REG(/*length=*/12, /*width=*/kSpiHostWidthQuad,
                     /*direction=*/kSpiHostDirectionRx, /*last=*/true);
  EXPECT_RXQD(12);
  EXPECT_ABS_READ32(base_ + SPI_HOST_RXDATA_REG_OFFSET, read_32(&test_data[0]));
  EXPECT_RXQD(8);
  EXPECT_ABS_READ32(base_ + SPI_HOST_RXDATA_REG_OFFSET, read_32(&test_data[4]));
  EXPECT_RXQD(4);
  EXPECT_ABS_READ32(base_ + SPI_HOST_RXDATA_REG_OFFSET, read_32(&test_data[8]));

  EXPECT_EQ(spi_host_transaction(0, &segment, 1), kErrorOk);
  for (unsigned i = 1; i < sizeof(buf); ++i) {
    EXPECT_EQ(buf[i], test_data[i - 1]);
  }
}

// Checks that multiple segments are sent/received correctly.
TEST_F(TransactionTest, MultiSegmentTxRx) {
  uint8_t test_data[12] = {0x12, 0x34, 0x56, 0x78, 0xab, 0xcd,
                           0xef, 0x01, 0x02, 0x03, 0x04, 0x05};
  alignas(4)
      uint8_t txbuf[8] = {0x87, 0x65, 0x43, 0x21, 0xff, 0xee, 0xdd, 0xcc};
  alignas(4) uint8_t rxbuf[12];
  spi_host_segment_t segment[2];

  segment[0].type = kSpiHostSegmentTypeTx;
  segment[0].width = kSpiHostWidthDual;
  segment[0].rx.buf = txbuf;
  segment[0].rx.length = sizeof(txbuf);
  segment[1].type = kSpiHostSegmentTypeRx;
  segment[1].width = kSpiHostWidthDual;
  segment[1].rx.buf = rxbuf;
  segment[1].rx.length = sizeof(rxbuf);

  EXPECT_ABS_WRITE32(base_ + SPI_HOST_CSID_REG_OFFSET, 0);
  EXPECT_READY(true);
  EXPECT_TXQD(0);
  EXPECT_ABS_WRITE32(base_ + SPI_HOST_TXDATA_REG_OFFSET, read_32(&txbuf[0]));
  EXPECT_TXQD(4);
  EXPECT_ABS_WRITE32(base_ + SPI_HOST_TXDATA_REG_OFFSET, read_32(&txbuf[4]));
  EXPECT_COMMAND_REG(/*length=*/8, /*width=*/kSpiHostWidthDual,
                     /*direction=*/kSpiHostDirectionTx, /*last=*/false);
  EXPECT_READY(true);
  EXPECT_COMMAND_REG(/*length=*/12, /*width=*/kSpiHostWidthDual,
                     /*direction=*/kSpiHostDirectionRx, /*last=*/true);
  EXPECT_RXQD(12);
  EXPECT_ABS_READ32(base_ + SPI_HOST_RXDATA_REG_OFFSET, read_32(&test_data[0]));
  EXPECT_RXQD(8);
  EXPECT_ABS_READ32(base_ + SPI_HOST_RXDATA_REG_OFFSET, read_32(&test_data[4]));
  EXPECT_RXQD(4);
  EXPECT_ABS_READ32(base_ + SPI_HOST_RXDATA_REG_OFFSET, read_32(&test_data[8]));

  EXPECT_EQ(spi_host_transaction(0, segment, ARRAYSIZE(segment)), kErrorOk);
  for (unsigned i = 0; i < sizeof(rxbuf); ++i) {
    EXPECT_EQ(rxbuf[i], test_data[i]);
  }
}

}  // namespace
}  // namespace spi_host_unittest
