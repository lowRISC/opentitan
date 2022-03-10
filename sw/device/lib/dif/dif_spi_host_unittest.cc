// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_spi_host.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/global_mock.h"
#include "sw/device/lib/base/testing/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

#include "spi_host_regs.h"  // Generated.

namespace dif_spi_host_unittest {
namespace {

// Mock out the spi_host_fifo functions.
namespace internal {
class MockFifo : public ::global_mock::GlobalMock<MockFifo> {
 public:
  MOCK_METHOD(void, write, (const dif_spi_host_t *, const void *, uint16_t));
  MOCK_METHOD(void, read, (const dif_spi_host_t *, void *, uint16_t));
};
}  // namespace internal
using MockFifo = testing::StrictMock<internal::MockFifo>;
extern "C" {
void spi_host_fifo_write_alias(const dif_spi_host_t *spi_host, const void *src,
                               uint16_t len) {
  MockFifo::Instance().write(spi_host, src, len);
}
void spi_host_fifo_read_alias(const dif_spi_host_t *spi_host, void *dst,
                              uint16_t len) {
  MockFifo::Instance().read(spi_host, dst, len);
}
}

using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::ElementsAre;
using testing::Test;

// Helper macros to make expectations easier to read.
#define EXPECT_COMMAND_REG(length, width, direction, last_segment)   \
  EXPECT_WRITE32(SPI_HOST_COMMAND_REG_OFFSET,                        \
                 {                                                   \
                     {SPI_HOST_COMMAND_LEN_OFFSET, (length)-1},      \
                     {SPI_HOST_COMMAND_SPEED_OFFSET, width},         \
                     {SPI_HOST_COMMAND_DIRECTION_OFFSET, direction}, \
                     {SPI_HOST_COMMAND_CSAAT_BIT, !(last_segment)},  \
                 })

#define EXPECT_READY(ready)                 \
  EXPECT_READ32(SPI_HOST_STATUS_REG_OFFSET, \
                {{SPI_HOST_STATUS_READY_BIT, ready}})

#define EXPECT_TXQD(txqd)                   \
  EXPECT_READ32(SPI_HOST_STATUS_REG_OFFSET, \
                {{SPI_HOST_STATUS_TXQD_OFFSET, txqd}})

#define EXPECT_RXQD(rxqd)                   \
  EXPECT_READ32(SPI_HOST_STATUS_REG_OFFSET, \
                {{SPI_HOST_STATUS_RXQD_OFFSET, rxqd}})

class SpiHostTest : public Test, public MmioTest {
 protected:
  void ExpectDeviceReset() {
    // Place IP into reset.
    EXPECT_WRITE32(SPI_HOST_CONTROL_REG_OFFSET,
                   {
                       {SPI_HOST_CONTROL_SW_RST_BIT, true},
                   });
    // Active bit should be clear.
    EXPECT_READ32(SPI_HOST_STATUS_REG_OFFSET, 0);
    // TXQD and RXQD should be zeros.
    EXPECT_READ32(SPI_HOST_STATUS_REG_OFFSET, 0);
    // Release IP from reset.
    EXPECT_WRITE32(SPI_HOST_CONTROL_REG_OFFSET,
                   {
                       {SPI_HOST_CONTROL_SW_RST_BIT, false},
                   });
  }

  dif_spi_host_t spi_host_ = {
      .base_addr = dev().region(),
  };

  dif_spi_host_config config_ = {
      .spi_clock = 1000000,
      .peripheral_clock_freq_hz = 1000000,
      .chip_select =
          {
              .idle = 0,
              .trail = 0,
              .lead = 0,
          },
      .full_cycle = false,
      .cpha = false,
      .cpol = false,
  };
};

class ConfigTest : public SpiHostTest {};

TEST_F(ConfigTest, NullArgs) {
  EXPECT_EQ(dif_spi_host_configure(nullptr, config_), kDifBadArg);
}

TEST_F(ConfigTest, BadDivider) {
  // A spi_clock faster than the peripheral clock is invalid.
  config_.spi_clock = 1000001;
  EXPECT_EQ(dif_spi_host_configure(&spi_host_, config_), kDifBadArg);

  // A spi_clock of zero is invalid.
  config_.spi_clock = 0;
  EXPECT_EQ(dif_spi_host_configure(&spi_host_, config_), kDifBadArg);
}

// Checks the default configuration.
TEST_F(ConfigTest, Default) {
  ExpectDeviceReset();
  EXPECT_WRITE32(SPI_HOST_CONFIGOPTS_REG_OFFSET,
                 {
                     {SPI_HOST_CONFIGOPTS_CLKDIV_0_OFFSET, 0},
                     {SPI_HOST_CONFIGOPTS_CSNIDLE_0_OFFSET, 0},
                     {SPI_HOST_CONFIGOPTS_CSNTRAIL_0_OFFSET, 0},
                     {SPI_HOST_CONFIGOPTS_CSNLEAD_0_OFFSET, 0},
                     {SPI_HOST_CONFIGOPTS_FULLCYC_0_BIT, false},
                     {SPI_HOST_CONFIGOPTS_CPHA_0_BIT, false},
                     {SPI_HOST_CONFIGOPTS_CPOL_0_BIT, false},
                 });
  EXPECT_WRITE32(SPI_HOST_CONTROL_REG_OFFSET,
                 {
                     {SPI_HOST_CONTROL_SPIEN_BIT, true},
                 });

  EXPECT_DIF_OK(dif_spi_host_configure(&spi_host_, config_));
}

// Checks manipulation of the output enable bit.
TEST_F(ConfigTest, OutputEnable) {
  EXPECT_READ32(SPI_HOST_CONTROL_REG_OFFSET, 0);
  EXPECT_WRITE32(SPI_HOST_CONTROL_REG_OFFSET,
                 {
                     {SPI_HOST_CONTROL_OUTPUT_EN_BIT, true},
                 });
  dif_spi_host_output(&spi_host_, true);
}

// Checks that the clock divider gets calculated correctly.
TEST_F(ConfigTest, ClockRate) {
  config_.spi_clock = 500000;

  ExpectDeviceReset();
  EXPECT_WRITE32(SPI_HOST_CONFIGOPTS_REG_OFFSET,
                 {
                     {SPI_HOST_CONFIGOPTS_CLKDIV_0_OFFSET, 1},
                     {SPI_HOST_CONFIGOPTS_CSNIDLE_0_OFFSET, 0},
                     {SPI_HOST_CONFIGOPTS_CSNTRAIL_0_OFFSET, 0},
                     {SPI_HOST_CONFIGOPTS_CSNLEAD_0_OFFSET, 0},
                     {SPI_HOST_CONFIGOPTS_FULLCYC_0_BIT, false},
                     {SPI_HOST_CONFIGOPTS_CPHA_0_BIT, false},
                     {SPI_HOST_CONFIGOPTS_CPOL_0_BIT, false},
                 });
  EXPECT_WRITE32(SPI_HOST_CONTROL_REG_OFFSET,
                 {
                     {SPI_HOST_CONTROL_SPIEN_BIT, true},
                 });

  EXPECT_DIF_OK(dif_spi_host_configure(&spi_host_, config_));
}

// Checks that the chip select options get written to the appropriate fields in
// the config register.
TEST_F(ConfigTest, ChipSelectOptions) {
  config_.chip_select.idle = 1;
  config_.chip_select.trail = 2;
  config_.chip_select.lead = 3;

  ExpectDeviceReset();
  EXPECT_WRITE32(SPI_HOST_CONFIGOPTS_REG_OFFSET,
                 {
                     {SPI_HOST_CONFIGOPTS_CLKDIV_0_OFFSET, 0},
                     {SPI_HOST_CONFIGOPTS_CSNIDLE_0_OFFSET, 1},
                     {SPI_HOST_CONFIGOPTS_CSNTRAIL_0_OFFSET, 2},
                     {SPI_HOST_CONFIGOPTS_CSNLEAD_0_OFFSET, 3},
                     {SPI_HOST_CONFIGOPTS_FULLCYC_0_BIT, false},
                     {SPI_HOST_CONFIGOPTS_CPHA_0_BIT, false},
                     {SPI_HOST_CONFIGOPTS_CPOL_0_BIT, false},
                 });
  EXPECT_WRITE32(SPI_HOST_CONTROL_REG_OFFSET,
                 {
                     {SPI_HOST_CONTROL_SPIEN_BIT, true},
                 });

  EXPECT_DIF_OK(dif_spi_host_configure(&spi_host_, config_));
}

// Checks that the SPI cycle, polarity and phase options get written to the
// appropriate fields in the config register.
TEST_F(ConfigTest, SpiOptions) {
  config_.full_cycle = true;
  config_.cpol = true;
  config_.cpha = true;

  ExpectDeviceReset();
  EXPECT_WRITE32(SPI_HOST_CONFIGOPTS_REG_OFFSET,
                 {
                     {SPI_HOST_CONFIGOPTS_CLKDIV_0_OFFSET, 0},
                     {SPI_HOST_CONFIGOPTS_CSNIDLE_0_OFFSET, 0},
                     {SPI_HOST_CONFIGOPTS_CSNTRAIL_0_OFFSET, 0},
                     {SPI_HOST_CONFIGOPTS_CSNLEAD_0_OFFSET, 0},
                     {SPI_HOST_CONFIGOPTS_FULLCYC_0_BIT, true},
                     {SPI_HOST_CONFIGOPTS_CPHA_0_BIT, true},
                     {SPI_HOST_CONFIGOPTS_CPOL_0_BIT, true},
                 });
  EXPECT_WRITE32(SPI_HOST_CONTROL_REG_OFFSET,
                 {
                     {SPI_HOST_CONTROL_SPIEN_BIT, true},
                 });

  EXPECT_DIF_OK(dif_spi_host_configure(&spi_host_, config_));
}

class TransactionTest : public SpiHostTest {
 protected:
  MockFifo fifo_;
};

// Checks that an opcode segment is sent correctly.
TEST_F(TransactionTest, IssueOpcode) {
  dif_spi_host_segment segment;
  segment.type = kDifSpiHostSegmentTypeOpcode;
  segment.opcode = 0x5a;

  EXPECT_WRITE32(SPI_HOST_CSID_REG_OFFSET, 0);
  EXPECT_READY(true);
  EXPECT_TXQD(0);
  // Opcodes are written directly to the FIFO register.
  EXPECT_WRITE8(SPI_HOST_TXDATA_REG_OFFSET, 0x5a);
  EXPECT_COMMAND_REG(/*length=*/1, /*width=*/kDifSpiHostWidthStandard,
                     /*direction=*/kDifSpiHostDirectionTx, /*last=*/true);

  EXPECT_DIF_OK(dif_spi_host_transaction(&spi_host_, 0, &segment, 1));
}

// Checks that an address segment is sent correctly in 3-byte mode.
TEST_F(TransactionTest, IssueAddressMode3b) {
  dif_spi_host_segment segment;
  segment.type = kDifSpiHostSegmentTypeAddress;
  segment.address.width = kDifSpiHostWidthStandard;
  segment.address.mode = kDifSpiHostAddrMode3b;
  segment.address.address = 0x112233;

  EXPECT_WRITE32(SPI_HOST_CSID_REG_OFFSET, 0);
  EXPECT_READY(true);
  EXPECT_TXQD(0);
  // SPI addresses are written directly to the FIFO register.
  EXPECT_WRITE32(SPI_HOST_TXDATA_REG_OFFSET, 0x332211);
  EXPECT_COMMAND_REG(/*length=*/3, /*width=*/kDifSpiHostWidthStandard,
                     /*direction=*/kDifSpiHostDirectionTx, /*last=*/true);

  EXPECT_DIF_OK(dif_spi_host_transaction(&spi_host_, 0, &segment, 1));
}

// Checks that an address segment is sent correctly in 4-byte mode.
TEST_F(TransactionTest, IssueAddressMode4b) {
  dif_spi_host_segment segment;
  segment.type = kDifSpiHostSegmentTypeAddress;
  segment.address.width = kDifSpiHostWidthStandard;
  segment.address.mode = kDifSpiHostAddrMode4b;
  segment.address.address = 0x11223344;

  EXPECT_WRITE32(SPI_HOST_CSID_REG_OFFSET, 0);
  EXPECT_READY(true);
  EXPECT_TXQD(0);
  // SPI addresses are written directly to the FIFO register.
  EXPECT_WRITE32(SPI_HOST_TXDATA_REG_OFFSET, 0x44332211);
  EXPECT_COMMAND_REG(/*length=*/4, /*width=*/kDifSpiHostWidthStandard,
                     /*direction=*/kDifSpiHostDirectionTx, /*last=*/true);

  EXPECT_DIF_OK(dif_spi_host_transaction(&spi_host_, 0, &segment, 1));
}

// Checks that a dummy segment is sent correctly.
TEST_F(TransactionTest, IssueDummy) {
  dif_spi_host_segment segment;
  segment.type = kDifSpiHostSegmentTypeDummy;
  segment.dummy.width = kDifSpiHostWidthStandard;
  segment.dummy.length = 8;

  EXPECT_WRITE32(SPI_HOST_CSID_REG_OFFSET, 0);
  EXPECT_READY(true);
  EXPECT_COMMAND_REG(/*length=*/8, /*width=*/kDifSpiHostWidthStandard,
                     /*direction=*/kDifSpiHostDirectionDummy, /*last=*/true);

  EXPECT_DIF_OK(dif_spi_host_transaction(&spi_host_, 0, &segment, 1));
}

// Checks that a transmit segment is sent correctly.
TEST_F(TransactionTest, TransmitDual) {
  uint8_t buf[32];
  dif_spi_host_segment segment;
  segment.type = kDifSpiHostSegmentTypeTx;
  segment.tx.width = kDifSpiHostWidthDual;
  segment.tx.buf = buf;
  segment.tx.length = sizeof(buf);

  EXPECT_WRITE32(SPI_HOST_CSID_REG_OFFSET, 0);
  EXPECT_READY(true);
  EXPECT_CALL(fifo_, write(&spi_host_, buf, sizeof(buf)));
  EXPECT_COMMAND_REG(/*length=*/sizeof(buf), /*width=*/kDifSpiHostWidthDual,
                     /*direction=*/kDifSpiHostDirectionTx, /*last=*/true);

  EXPECT_DIF_OK(dif_spi_host_transaction(&spi_host_, 0, &segment, 1));
}

// Checks that a receive segment is sent correctly.
TEST_F(TransactionTest, ReceiveQuad) {
  uint8_t buf[32];
  dif_spi_host_segment segment;
  segment.type = kDifSpiHostSegmentTypeRx;
  segment.rx.width = kDifSpiHostWidthQuad;
  segment.rx.buf = buf;
  segment.rx.length = sizeof(buf);

  EXPECT_WRITE32(SPI_HOST_CSID_REG_OFFSET, 0);
  EXPECT_READY(true);
  EXPECT_COMMAND_REG(/*length=*/sizeof(buf), /*width=*/kDifSpiHostWidthQuad,
                     /*direction=*/kDifSpiHostDirectionRx, /*last=*/true);
  EXPECT_CALL(fifo_, read(&spi_host_, buf, sizeof(buf)));

  EXPECT_DIF_OK(dif_spi_host_transaction(&spi_host_, 0, &segment, 1));
}

// Checks that a tranceive segment is sent correctly.
TEST_F(TransactionTest, Transceive) {
  uint8_t txbuf[32];
  uint8_t rxbuf[32];
  dif_spi_host_segment segment;
  segment.type = kDifSpiHostSegmentTypeBidirectional;
  segment.bidir.width = kDifSpiHostWidthStandard;
  segment.bidir.txbuf = txbuf;
  segment.bidir.rxbuf = rxbuf;
  segment.bidir.length = sizeof(txbuf);

  EXPECT_WRITE32(SPI_HOST_CSID_REG_OFFSET, 0);
  EXPECT_READY(true);
  EXPECT_CALL(fifo_, write(&spi_host_, txbuf, sizeof(txbuf)));
  EXPECT_COMMAND_REG(
      /*length=*/sizeof(txbuf), /*width=*/kDifSpiHostWidthStandard,
      /*direction=*/kDifSpiHostDirectionBidirectional, /*last=*/true);
  EXPECT_CALL(fifo_, read(&spi_host_, rxbuf, sizeof(rxbuf)));

  EXPECT_DIF_OK(dif_spi_host_transaction(&spi_host_, 0, &segment, 1));
}

// Checks that multiple segments are sent correctly.
TEST_F(TransactionTest, MultiSegmentTxRx) {
  uint8_t txbuf[32];
  uint8_t rxbuf[64];
  dif_spi_host_segment segment[2];

  segment[0].type = kDifSpiHostSegmentTypeTx;
  segment[0].rx.width = kDifSpiHostWidthDual;
  segment[0].rx.buf = txbuf;
  segment[0].rx.length = sizeof(txbuf);
  segment[1].type = kDifSpiHostSegmentTypeRx;
  segment[1].rx.width = kDifSpiHostWidthDual;
  segment[1].rx.buf = rxbuf;
  segment[1].rx.length = sizeof(rxbuf);

  EXPECT_WRITE32(SPI_HOST_CSID_REG_OFFSET, 0);
  EXPECT_READY(true);
  EXPECT_CALL(fifo_, write(&spi_host_, txbuf, sizeof(txbuf)));
  EXPECT_COMMAND_REG(/*length=*/sizeof(txbuf), /*width=*/kDifSpiHostWidthDual,
                     /*direction=*/kDifSpiHostDirectionTx, /*last=*/false);
  EXPECT_READY(true);
  EXPECT_COMMAND_REG(/*length=*/sizeof(rxbuf), /*width=*/kDifSpiHostWidthDual,
                     /*direction=*/kDifSpiHostDirectionRx, /*last=*/true);
  EXPECT_CALL(fifo_, read(&spi_host_, rxbuf, sizeof(rxbuf)));

  EXPECT_DIF_OK(
      dif_spi_host_transaction(&spi_host_, 0, segment, ARRAYSIZE(segment)));
}

class FifoTest : public SpiHostTest {};

// Checks that an aligned source buffer is written as 32-bit words into the
// transmit FIFO.
TEST_F(FifoTest, AlignedWrite) {
  uint32_t buffer[] = {1, 2};

  EXPECT_TXQD(0);
  EXPECT_WRITE32(SPI_HOST_TXDATA_REG_OFFSET, 1);
  EXPECT_TXQD(0);
  EXPECT_WRITE32(SPI_HOST_TXDATA_REG_OFFSET, 2);

  dif_spi_host_fifo_write(&spi_host_, buffer, sizeof(buffer));
}

template <size_t count, size_t align>
struct Aligned {
  alignas(align) uint8_t value[count];
  uint8_t *get() { return &value[0]; }
};

// Checks that a misaligned source buffer is written as bytes into the
// transmit FIFO until alignment is reached and then written as 32-bit words.
TEST_F(FifoTest, MisalignedWrite) {
  // We'll intentionally mis-align the buffer by 1 when calling
  // dif_spi_host_fifo_write.
  Aligned<9, 4> buffer = {0, 1, 2, 3, 4, 5, 6, 7, 8};

  // Because of the misalignment, expect three byte writes.
  EXPECT_TXQD(0);
  EXPECT_WRITE8(SPI_HOST_TXDATA_REG_OFFSET, 1);
  EXPECT_TXQD(0);
  EXPECT_WRITE8(SPI_HOST_TXDATA_REG_OFFSET, 2);
  EXPECT_TXQD(0);
  EXPECT_WRITE8(SPI_HOST_TXDATA_REG_OFFSET, 3);

  // Then a word write when we reach alignment.
  EXPECT_TXQD(0);
  EXPECT_WRITE32(SPI_HOST_TXDATA_REG_OFFSET, 0x07060504);

  // Then a byte write to finish the buffer.
  EXPECT_TXQD(0);
  EXPECT_WRITE8(SPI_HOST_TXDATA_REG_OFFSET, 8);

  dif_spi_host_fifo_write(&spi_host_, buffer.get() + 1, 8);
}

// Checks that an aligned destination buffer receives the contents of the
// recieve FIFO.
TEST_F(FifoTest, AlignedRead) {
  uint32_t buffer[2];

  EXPECT_RXQD(2);
  EXPECT_READ32(SPI_HOST_RXDATA_REG_OFFSET, 1);
  EXPECT_RXQD(1);
  EXPECT_READ32(SPI_HOST_RXDATA_REG_OFFSET, 2);

  dif_spi_host_fifo_read(&spi_host_, buffer, sizeof(buffer));
  EXPECT_THAT(buffer, ElementsAre(1, 2));
}

// Checks that a misaligned destination buffer receives the contents of the
// recieve FIFO.
TEST_F(FifoTest, MisalignedRead) {
  // We'll intentionally mis-align the buffer by 1 when calling
  // dif_spi_host_fifo_read.
  Aligned<9, 4> buffer{};

  EXPECT_RXQD(2);
  EXPECT_READ32(SPI_HOST_RXDATA_REG_OFFSET, 0x04030201);
  EXPECT_RXQD(1);
  EXPECT_READ32(SPI_HOST_RXDATA_REG_OFFSET, 0x08070605);

  dif_spi_host_fifo_read(&spi_host_, buffer.get() + 1, 8);
  EXPECT_THAT(buffer.value, ElementsAre(0, 1, 2, 3, 4, 5, 6, 7, 8));
}

}  // namespace
}  // namespace dif_spi_host_unittest
