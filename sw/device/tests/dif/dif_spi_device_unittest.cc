// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_spi_device.h"

#include <limits>

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/testing/mock_mmio.h"

#include "spi_device_regs.h"  // Generated.

namespace dif_spi_device_unittest {
namespace {
using ::mock_mmio::LeInt;
using ::mock_mmio::MmioTest;
using ::mock_mmio::MockDevice;

// Convenience function for assembling a phased FIFO pointer.
uintptr_t FifoPtr(uintptr_t offset, bool phase) {
  return offset | (static_cast<uintptr_t>(phase) << 12);
}

// Convenience function for generating a vector full of noisy data.
std::vector<char> MakeBlob(size_t len) {
  std::vector<char> buf;
  buf.resize(len);
  uint8_t val = 1;
  for (auto &c : buf) {
    c = val;
    val *= 31;
  }
  return buf;
}

class SpiTest : public testing::Test, public MmioTest {
 protected:
  static const uint16_t kFifoLen = 0x800;

  dif_spi_device_t spi_ = {
      .params = {.base_addr = dev().region()},
      .rx_fifo_len = kFifoLen,
      .tx_fifo_len = kFifoLen,
  };

  dif_spi_device_config_t config_ = {
      .clock_polarity = kDifSpiDeviceEdgePositive,
      .data_phase = kDifSpiDeviceEdgeNegative,
      .tx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .rx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .rx_fifo_timeout = 63,
      .rx_fifo_len = kFifoLen,
      .tx_fifo_len = kFifoLen,
  };
};

class AbortTest : public SpiTest {};

TEST_F(AbortTest, Immediate) {
  EXPECT_MASK32(SPI_DEVICE_CONTROL_REG_OFFSET,
                {{SPI_DEVICE_CONTROL_ABORT_BIT, 0x1, 0x1}});
  EXPECT_READ32(SPI_DEVICE_STATUS_REG_OFFSET,
                {{SPI_DEVICE_STATUS_ABORT_DONE_BIT, 0x1}});

  EXPECT_EQ(dif_spi_device_abort(&spi_), kDifSpiDeviceOk);
}

TEST_F(AbortTest, Delayed) {
  EXPECT_MASK32(SPI_DEVICE_CONTROL_REG_OFFSET,
                {{SPI_DEVICE_CONTROL_ABORT_BIT, 0x1, 0x1}});
  EXPECT_READ32(SPI_DEVICE_STATUS_REG_OFFSET, 0);
  EXPECT_READ32(SPI_DEVICE_STATUS_REG_OFFSET, 0);
  EXPECT_READ32(SPI_DEVICE_STATUS_REG_OFFSET, 0);
  EXPECT_READ32(SPI_DEVICE_STATUS_REG_OFFSET, 0);
  EXPECT_READ32(SPI_DEVICE_STATUS_REG_OFFSET, 0);
  EXPECT_READ32(SPI_DEVICE_STATUS_REG_OFFSET, 0);
  EXPECT_READ32(SPI_DEVICE_STATUS_REG_OFFSET,
                {{SPI_DEVICE_STATUS_ABORT_DONE_BIT, 0x1}});

  EXPECT_EQ(dif_spi_device_abort(&spi_), kDifSpiDeviceOk);
}

TEST_F(AbortTest, NullArgs) {
  EXPECT_EQ(dif_spi_device_abort(nullptr), kDifSpiDeviceBadArg);
}

class ConfigTest : public SpiTest {};

TEST_F(ConfigTest, BasicInit) {
  EXPECT_WRITE32(SPI_DEVICE_CFG_REG_OFFSET,
                 {
                     {SPI_DEVICE_CFG_CPOL_BIT, 0},
                     {SPI_DEVICE_CFG_CPHA_BIT, 0},
                     {SPI_DEVICE_CFG_TX_ORDER_BIT, 0},
                     {SPI_DEVICE_CFG_RX_ORDER_BIT, 0},
                     {SPI_DEVICE_CFG_TIMER_V_OFFSET, config_.rx_fifo_timeout},
                 });
  EXPECT_WRITE32(SPI_DEVICE_RXF_ADDR_REG_OFFSET,
                 {
                     {SPI_DEVICE_RXF_ADDR_BASE_OFFSET, 0x000},
                     {SPI_DEVICE_RXF_ADDR_LIMIT_OFFSET, 0x800 - 1},
                 });
  EXPECT_WRITE32(SPI_DEVICE_TXF_ADDR_REG_OFFSET,
                 {
                     {SPI_DEVICE_TXF_ADDR_BASE_OFFSET, 0x800},
                     {SPI_DEVICE_TXF_ADDR_LIMIT_OFFSET, 0x1000 - 1},
                 });

  EXPECT_EQ(dif_spi_device_configure(&spi_, config_), kDifSpiDeviceOk);
}

TEST_F(ConfigTest, ComplexInit) {
  config_ = {
      .clock_polarity = kDifSpiDeviceEdgeNegative,
      .data_phase = kDifSpiDeviceEdgePositive,
      .tx_order = kDifSpiDeviceBitOrderLsbToMsb,
      .rx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .rx_fifo_timeout = 42,
      .rx_fifo_len = 0x24,
      .tx_fifo_len = kFifoLen,
  };

  EXPECT_WRITE32(SPI_DEVICE_CFG_REG_OFFSET,
                 {
                     {SPI_DEVICE_CFG_CPOL_BIT, 1},
                     {SPI_DEVICE_CFG_CPHA_BIT, 1},
                     {SPI_DEVICE_CFG_TX_ORDER_BIT, 1},
                     {SPI_DEVICE_CFG_RX_ORDER_BIT, 0},
                     {SPI_DEVICE_CFG_TIMER_V_OFFSET, config_.rx_fifo_timeout},
                 });
  EXPECT_WRITE32(SPI_DEVICE_RXF_ADDR_REG_OFFSET,
                 {
                     {SPI_DEVICE_RXF_ADDR_BASE_OFFSET, 0x000},
                     {SPI_DEVICE_RXF_ADDR_LIMIT_OFFSET, 0x023},
                 });
  EXPECT_WRITE32(SPI_DEVICE_TXF_ADDR_REG_OFFSET,
                 {
                     {SPI_DEVICE_TXF_ADDR_BASE_OFFSET, 0x024},
                     {SPI_DEVICE_TXF_ADDR_LIMIT_OFFSET, 0x823},
                 });

  EXPECT_EQ(dif_spi_device_configure(&spi_, config_), kDifSpiDeviceOk);
}

TEST_F(ConfigTest, NullArgs) {
  EXPECT_EQ(dif_spi_device_configure(nullptr, config_), kDifSpiDeviceBadArg);
}

TEST_F(ConfigTest, InitSramOverflow) {
  config_.rx_fifo_len = 0x1000;
  EXPECT_EQ(dif_spi_device_configure(&spi_, config_), kDifSpiDeviceBadArg);
}

class IrqTest : public SpiTest {};

TEST_F(IrqTest, Get) {
  bool out;

  EXPECT_READ32(SPI_DEVICE_INTR_STATE_REG_OFFSET,
                {{SPI_DEVICE_INTR_STATE_RXF_BIT, 1}});
  EXPECT_EQ(dif_spi_device_irq_is_pending(&spi_, kDifSpiDeviceIrqRxFull, &out),
            kDifSpiDeviceOk);
  EXPECT_TRUE(out);

  EXPECT_READ32(SPI_DEVICE_INTR_STATE_REG_OFFSET,
                {{SPI_DEVICE_INTR_STATE_RXERR_BIT, 0},
                 {SPI_DEVICE_INTR_STATE_RXF_BIT, 1}});
  EXPECT_EQ(dif_spi_device_irq_is_pending(&spi_, kDifSpiDeviceIrqRxError, &out),
            kDifSpiDeviceOk);
  EXPECT_FALSE(out);

  EXPECT_READ32(SPI_DEVICE_INTR_STATE_REG_OFFSET,
                {{SPI_DEVICE_INTR_STATE_TXUNDERFLOW_BIT, 1}});
  EXPECT_EQ(
      dif_spi_device_irq_is_pending(&spi_, kDifSpiDeviceIrqTxUnderflow, &out),
      kDifSpiDeviceOk);
  EXPECT_TRUE(out);

  EXPECT_READ32(SPI_DEVICE_INTR_STATE_REG_OFFSET,
                {{SPI_DEVICE_INTR_STATE_TXLVL_BIT, 0}});
  EXPECT_EQ(
      dif_spi_device_irq_is_pending(&spi_, kDifSpiDeviceIrqTxBelowLevel, &out),
      kDifSpiDeviceOk);
  EXPECT_FALSE(out);
}

TEST_F(IrqTest, GetNull) {
  bool out;
  EXPECT_EQ(
      dif_spi_device_irq_is_pending(nullptr, kDifSpiDeviceIrqRxFull, &out),
      kDifSpiDeviceBadArg);
  EXPECT_EQ(
      dif_spi_device_irq_is_pending(&spi_, kDifSpiDeviceIrqRxFull, nullptr),
      kDifSpiDeviceBadArg);
}

TEST_F(IrqTest, Enable) {
  EXPECT_MASK32(SPI_DEVICE_INTR_ENABLE_REG_OFFSET,
                {{SPI_DEVICE_INTR_ENABLE_RXF_BIT, 0x1, 1}});
  EXPECT_EQ(dif_spi_device_irq_set_enabled(&spi_, kDifSpiDeviceIrqRxFull,
                                           kDifSpiDeviceToggleEnabled),
            kDifSpiDeviceOk);

  EXPECT_MASK32(SPI_DEVICE_INTR_ENABLE_REG_OFFSET,
                {{SPI_DEVICE_INTR_ENABLE_RXERR_BIT, 0x1, 0}});
  EXPECT_EQ(dif_spi_device_irq_set_enabled(&spi_, kDifSpiDeviceIrqRxError,
                                           kDifSpiDeviceToggleDisabled),
            kDifSpiDeviceOk);

  EXPECT_MASK32(SPI_DEVICE_INTR_ENABLE_REG_OFFSET,
                {{SPI_DEVICE_INTR_ENABLE_TXUNDERFLOW_BIT, 0x1, 1}});
  EXPECT_EQ(dif_spi_device_irq_set_enabled(&spi_, kDifSpiDeviceIrqTxUnderflow,
                                           kDifSpiDeviceToggleEnabled),
            kDifSpiDeviceOk);

  EXPECT_MASK32(SPI_DEVICE_INTR_ENABLE_REG_OFFSET,
                {{SPI_DEVICE_INTR_ENABLE_TXLVL_BIT, 0x1, 0}});
  EXPECT_EQ(dif_spi_device_irq_set_enabled(&spi_, kDifSpiDeviceIrqTxBelowLevel,
                                           kDifSpiDeviceToggleDisabled),
            kDifSpiDeviceOk);
}

TEST_F(IrqTest, EnableNull) {
  EXPECT_EQ(dif_spi_device_irq_set_enabled(nullptr, kDifSpiDeviceIrqRxFull,
                                           kDifSpiDeviceToggleEnabled),
            kDifSpiDeviceBadArg);
}

TEST_F(IrqTest, Force) {
  EXPECT_WRITE32(SPI_DEVICE_INTR_TEST_REG_OFFSET,
                 {{SPI_DEVICE_INTR_TEST_RXF_BIT, 1}});
  EXPECT_EQ(dif_spi_device_irq_force(&spi_, kDifSpiDeviceIrqRxFull),
            kDifSpiDeviceOk);

  EXPECT_WRITE32(SPI_DEVICE_INTR_TEST_REG_OFFSET,
                 {{SPI_DEVICE_INTR_TEST_RXERR_BIT, 1}});
  EXPECT_EQ(dif_spi_device_irq_force(&spi_, kDifSpiDeviceIrqRxError),
            kDifSpiDeviceOk);

  EXPECT_WRITE32(SPI_DEVICE_INTR_TEST_REG_OFFSET,
                 {{SPI_DEVICE_INTR_TEST_TXUNDERFLOW_BIT, 1}});
  EXPECT_EQ(dif_spi_device_irq_force(&spi_, kDifSpiDeviceIrqTxUnderflow),
            kDifSpiDeviceOk);

  EXPECT_WRITE32(SPI_DEVICE_INTR_TEST_REG_OFFSET,
                 {{SPI_DEVICE_INTR_TEST_TXLVL_BIT, 1}});
  EXPECT_EQ(dif_spi_device_irq_force(&spi_, kDifSpiDeviceIrqTxBelowLevel),
            kDifSpiDeviceOk);
}

TEST_F(IrqTest, ForceNull) {
  EXPECT_EQ(dif_spi_device_irq_force(nullptr, kDifSpiDeviceIrqRxFull),
            kDifSpiDeviceBadArg);
}

TEST_F(IrqTest, Levels) {
  EXPECT_WRITE32(SPI_DEVICE_FIFO_LEVEL_REG_OFFSET,
                 {{SPI_DEVICE_FIFO_LEVEL_RXLVL_OFFSET, 42},
                  {SPI_DEVICE_FIFO_LEVEL_TXLVL_OFFSET, 123}});
  EXPECT_EQ(dif_spi_device_set_irq_levels(&spi_, 42, 123), kDifSpiDeviceOk);
}

TEST_F(IrqTest, LevelsNull) {
  EXPECT_EQ(dif_spi_device_set_irq_levels(nullptr, 123, 456),
            kDifSpiDeviceBadArg);
}

class RxPendingTest : public SpiTest {};

TEST_F(RxPendingTest, BothZero) {
  EXPECT_READ32(SPI_DEVICE_RXF_PTR_REG_OFFSET,
                {{SPI_DEVICE_RXF_PTR_WPTR_OFFSET, 0x0},
                 {SPI_DEVICE_RXF_PTR_RPTR_OFFSET, 0x0}});
  size_t bytes_remaining;
  EXPECT_EQ(dif_spi_device_rx_pending(&spi_, &bytes_remaining),
            kDifSpiDeviceOk);
  EXPECT_EQ(bytes_remaining, 0);
}

TEST_F(RxPendingTest, InPhaseEmpty) {
  EXPECT_READ32(SPI_DEVICE_RXF_PTR_REG_OFFSET,
                {{SPI_DEVICE_RXF_PTR_WPTR_OFFSET, FifoPtr(0x42, true)},
                 {SPI_DEVICE_RXF_PTR_RPTR_OFFSET, FifoPtr(0x42, true)}});
  size_t bytes_remaining;
  EXPECT_EQ(dif_spi_device_rx_pending(&spi_, &bytes_remaining),
            kDifSpiDeviceOk);
  EXPECT_EQ(bytes_remaining, 0);
}

TEST_F(RxPendingTest, InPhase) {
  EXPECT_READ32(SPI_DEVICE_RXF_PTR_REG_OFFSET,
                {{SPI_DEVICE_RXF_PTR_WPTR_OFFSET, FifoPtr(0x57, true)},
                 {SPI_DEVICE_RXF_PTR_RPTR_OFFSET, FifoPtr(0x42, true)}});
  size_t bytes_remaining;
  EXPECT_EQ(dif_spi_device_rx_pending(&spi_, &bytes_remaining),
            kDifSpiDeviceOk);
  EXPECT_EQ(bytes_remaining, 0x15);
}

TEST_F(RxPendingTest, OutOfPhaseFull) {
  EXPECT_READ32(SPI_DEVICE_RXF_PTR_REG_OFFSET,
                {{SPI_DEVICE_RXF_PTR_WPTR_OFFSET, FifoPtr(0x42, false)},
                 {SPI_DEVICE_RXF_PTR_RPTR_OFFSET, FifoPtr(0x42, true)}});
  size_t bytes_remaining;
  EXPECT_EQ(dif_spi_device_rx_pending(&spi_, &bytes_remaining),
            kDifSpiDeviceOk);
  EXPECT_EQ(bytes_remaining, 0x800);
}

TEST_F(RxPendingTest, OutOfPhase) {
  EXPECT_READ32(SPI_DEVICE_RXF_PTR_REG_OFFSET,
                {{SPI_DEVICE_RXF_PTR_WPTR_OFFSET, FifoPtr(0x42, false)},
                 {SPI_DEVICE_RXF_PTR_RPTR_OFFSET, FifoPtr(0x57, true)}});
  size_t bytes_remaining;
  EXPECT_EQ(dif_spi_device_rx_pending(&spi_, &bytes_remaining),
            kDifSpiDeviceOk);
  EXPECT_EQ(bytes_remaining, 0x7eb);
}

TEST_F(RxPendingTest, NullArgs) {
  size_t bytes_remaining;
  EXPECT_EQ(dif_spi_device_rx_pending(nullptr, &bytes_remaining),
            kDifSpiDeviceBadArg);
  EXPECT_EQ(dif_spi_device_rx_pending(&spi_, nullptr), kDifSpiDeviceBadArg);
}

class TxPendingTest : public SpiTest {};

TEST_F(TxPendingTest, BothZero) {
  EXPECT_READ32(SPI_DEVICE_TXF_PTR_REG_OFFSET,
                {{SPI_DEVICE_TXF_PTR_WPTR_OFFSET, 0x0},
                 {SPI_DEVICE_TXF_PTR_RPTR_OFFSET, 0x0}});
  size_t bytes_remaining;
  EXPECT_EQ(dif_spi_device_tx_pending(&spi_, &bytes_remaining),
            kDifSpiDeviceOk);
  EXPECT_EQ(bytes_remaining, 0);
}

TEST_F(TxPendingTest, InPhaseEmpty) {
  EXPECT_READ32(SPI_DEVICE_TXF_PTR_REG_OFFSET,
                {{SPI_DEVICE_TXF_PTR_WPTR_OFFSET, FifoPtr(0x42, true)},
                 {SPI_DEVICE_TXF_PTR_RPTR_OFFSET, FifoPtr(0x42, true)}});
  size_t bytes_remaining;
  EXPECT_EQ(dif_spi_device_tx_pending(&spi_, &bytes_remaining),
            kDifSpiDeviceOk);
  EXPECT_EQ(bytes_remaining, 0);
}

TEST_F(TxPendingTest, InPhase) {
  EXPECT_READ32(SPI_DEVICE_TXF_PTR_REG_OFFSET,
                {{SPI_DEVICE_TXF_PTR_WPTR_OFFSET, FifoPtr(0x57, true)},
                 {SPI_DEVICE_TXF_PTR_RPTR_OFFSET, FifoPtr(0x42, true)}});
  size_t bytes_remaining;
  EXPECT_EQ(dif_spi_device_tx_pending(&spi_, &bytes_remaining),
            kDifSpiDeviceOk);
  EXPECT_EQ(bytes_remaining, 0x15);
}

TEST_F(TxPendingTest, OutOfPhaseFull) {
  EXPECT_READ32(SPI_DEVICE_TXF_PTR_REG_OFFSET,
                {{SPI_DEVICE_TXF_PTR_WPTR_OFFSET, FifoPtr(0x42, false)},
                 {SPI_DEVICE_TXF_PTR_RPTR_OFFSET, FifoPtr(0x42, true)}});
  size_t bytes_remaining;
  EXPECT_EQ(dif_spi_device_tx_pending(&spi_, &bytes_remaining),
            kDifSpiDeviceOk);
  EXPECT_EQ(bytes_remaining, 0x800);
}

TEST_F(TxPendingTest, OutOfPhase) {
  EXPECT_READ32(SPI_DEVICE_TXF_PTR_REG_OFFSET,
                {{SPI_DEVICE_TXF_PTR_WPTR_OFFSET, FifoPtr(0x42, false)},
                 {SPI_DEVICE_TXF_PTR_RPTR_OFFSET, FifoPtr(0x57, true)}});
  size_t bytes_remaining;
  EXPECT_EQ(dif_spi_device_tx_pending(&spi_, &bytes_remaining),
            kDifSpiDeviceOk);
  EXPECT_EQ(bytes_remaining, 0x7eb);
}

TEST_F(TxPendingTest, NullArgs) {
  size_t bytes_remaining;
  EXPECT_EQ(dif_spi_device_tx_pending(nullptr, &bytes_remaining),
            kDifSpiDeviceBadArg);
  EXPECT_EQ(dif_spi_device_tx_pending(&spi_, nullptr), kDifSpiDeviceBadArg);
}

class RecvTest : public SpiTest {};

TEST_F(RecvTest, EmptyFifo) {
  EXPECT_READ32(SPI_DEVICE_RXF_PTR_REG_OFFSET,
                {{SPI_DEVICE_RXF_PTR_WPTR_OFFSET, FifoPtr(0x5a, false)},
                 {SPI_DEVICE_RXF_PTR_RPTR_OFFSET, FifoPtr(0x5a, false)}});

  std::string buf(16, '\0');
  size_t recv_len = 0;
  EXPECT_EQ(dif_spi_device_recv(&spi_, const_cast<char *>(buf.data()),
                                buf.size(), &recv_len),
            kDifSpiDeviceOk);
  EXPECT_EQ(recv_len, 0);
  buf.resize(recv_len);
  EXPECT_EQ(buf, "");
}

TEST_F(RecvTest, FullFifoAligned) {
  EXPECT_READ32(SPI_DEVICE_RXF_PTR_REG_OFFSET,
                {{SPI_DEVICE_RXF_PTR_WPTR_OFFSET, FifoPtr(0x50, true)},
                 {SPI_DEVICE_RXF_PTR_RPTR_OFFSET, FifoPtr(0x50, false)}});

  auto message = MakeBlob(kFifoLen);
  auto fifo_base = SPI_DEVICE_BUFFER_REG_OFFSET;
  for (int i = 0; i < kFifoLen; i += 4) {
    auto idx = fifo_base + (i + 0x50) % kFifoLen;
    EXPECT_READ32(idx, LeInt(&message[i]));
  }

  EXPECT_WRITE32(SPI_DEVICE_RXF_PTR_REG_OFFSET,
                 {{SPI_DEVICE_RXF_PTR_WPTR_OFFSET, FifoPtr(0x50, true)},
                  {SPI_DEVICE_RXF_PTR_RPTR_OFFSET, FifoPtr(0x50, true)}});

  std::vector<char> buf;
  buf.resize(message.size() * 2);
  size_t recv_len = 0;
  EXPECT_EQ(dif_spi_device_recv(&spi_, buf.data(), buf.size(), &recv_len),
            kDifSpiDeviceOk);
  EXPECT_EQ(recv_len, message.size());
  buf.resize(recv_len);
  EXPECT_EQ(buf, message);
}

TEST_F(RecvTest, FullFifoSmallBuf) {
  size_t buf_len = 0x22;

  EXPECT_READ32(SPI_DEVICE_RXF_PTR_REG_OFFSET,
                {{SPI_DEVICE_RXF_PTR_WPTR_OFFSET, FifoPtr(0x50, true)},
                 {SPI_DEVICE_RXF_PTR_RPTR_OFFSET, FifoPtr(0x50, false)}});

  auto message = MakeBlob(kFifoLen);
  auto fifo_base = SPI_DEVICE_BUFFER_REG_OFFSET;
  for (size_t i = 0; i < buf_len; i += 4) {
    auto idx = fifo_base + (i + 0x50) % kFifoLen;
    EXPECT_READ32(idx, LeInt(&message[i]));
  }

  EXPECT_WRITE32(
      SPI_DEVICE_RXF_PTR_REG_OFFSET,
      {{SPI_DEVICE_RXF_PTR_WPTR_OFFSET, FifoPtr(0x50, true)},
       {SPI_DEVICE_RXF_PTR_RPTR_OFFSET, FifoPtr(0x50 + buf_len, false)}});

  std::vector<char> buf;
  buf.resize(buf_len);
  size_t recv_len = 0;
  EXPECT_EQ(dif_spi_device_recv(&spi_, buf.data(), buf.size(), &recv_len),
            kDifSpiDeviceOk);
  EXPECT_EQ(recv_len, buf_len);
  buf.resize(recv_len);
  message.resize(recv_len);
  EXPECT_EQ(buf, message);
}

TEST_F(RecvTest, FullyAligned) {
  std::string message = "Hello, SPI!!";
  ASSERT_EQ(message.size() % 4, 0);

  EXPECT_READ32(
      SPI_DEVICE_RXF_PTR_REG_OFFSET,
      {{SPI_DEVICE_RXF_PTR_WPTR_OFFSET, FifoPtr(message.size(), false)},
       {SPI_DEVICE_RXF_PTR_RPTR_OFFSET, FifoPtr(0x00, false)}});

  auto fifo_base = SPI_DEVICE_BUFFER_REG_OFFSET;
  EXPECT_READ32(fifo_base + 0x0, LeInt(&message[0x0]));
  EXPECT_READ32(fifo_base + 0x4, LeInt(&message[0x4]));
  EXPECT_READ32(fifo_base + 0x8, LeInt(&message[0x8]));

  EXPECT_WRITE32(
      SPI_DEVICE_RXF_PTR_REG_OFFSET,
      {{SPI_DEVICE_RXF_PTR_WPTR_OFFSET, FifoPtr(message.size(), false)},
       {SPI_DEVICE_RXF_PTR_RPTR_OFFSET, FifoPtr(message.size(), false)}});

  std::string buf(message.size() * 2, '\0');
  size_t recv_len = 0;
  EXPECT_EQ(dif_spi_device_recv(&spi_, const_cast<char *>(buf.data()),
                                buf.size(), &recv_len),
            kDifSpiDeviceOk);
  EXPECT_EQ(recv_len, message.size());
  buf.resize(recv_len);
  EXPECT_EQ(buf, message);
}

TEST_F(RecvTest, UnalignedMessage) {
  std::string message = "Hello, SPI!!";
  ASSERT_EQ(message.size() % 4, 0);

  uintptr_t cropped_len = 9;
  EXPECT_READ32(SPI_DEVICE_RXF_PTR_REG_OFFSET,
                {{SPI_DEVICE_RXF_PTR_WPTR_OFFSET, FifoPtr(cropped_len, false)},
                 {SPI_DEVICE_RXF_PTR_RPTR_OFFSET, FifoPtr(0x00, false)}});

  auto fifo_base = SPI_DEVICE_BUFFER_REG_OFFSET;
  EXPECT_READ32(fifo_base + 0x0, LeInt(&message[0x0]));
  EXPECT_READ32(fifo_base + 0x4, LeInt(&message[0x4]));
  EXPECT_READ32(fifo_base + 0x8, LeInt(&message[0x8]));

  EXPECT_WRITE32(
      SPI_DEVICE_RXF_PTR_REG_OFFSET,
      {{SPI_DEVICE_RXF_PTR_WPTR_OFFSET, FifoPtr(cropped_len, false)},
       {SPI_DEVICE_RXF_PTR_RPTR_OFFSET, FifoPtr(cropped_len, false)}});

  std::string buf(message.size() * 2, '\0');
  size_t recv_len = 0;
  EXPECT_EQ(dif_spi_device_recv(&spi_, const_cast<char *>(buf.data()),
                                buf.size(), &recv_len),
            kDifSpiDeviceOk);
  EXPECT_EQ(recv_len, cropped_len);

  buf.resize(message.size());
  EXPECT_NE(buf, message);

  buf.resize(recv_len);
  EXPECT_EQ(buf, message.substr(0, cropped_len));
}

TEST_F(RecvTest, UnalignedStart) {
  std::string message = "Hello, SPI!!";
  ASSERT_EQ(message.size() % 4, 0);

  uintptr_t cropped_start = 1;
  uintptr_t cropped_len = 9;
  EXPECT_READ32(
      SPI_DEVICE_RXF_PTR_REG_OFFSET,
      {{SPI_DEVICE_RXF_PTR_WPTR_OFFSET, FifoPtr(cropped_len, false)},
       {SPI_DEVICE_RXF_PTR_RPTR_OFFSET, FifoPtr(cropped_start, false)}});

  auto fifo_base = SPI_DEVICE_BUFFER_REG_OFFSET;
  EXPECT_READ32(fifo_base + 0x0, LeInt(&message[0x0]));
  EXPECT_READ32(fifo_base + 0x4, LeInt(&message[0x4]));
  EXPECT_READ32(fifo_base + 0x8, LeInt(&message[0x8]));

  EXPECT_WRITE32(
      SPI_DEVICE_RXF_PTR_REG_OFFSET,
      {{SPI_DEVICE_RXF_PTR_WPTR_OFFSET, FifoPtr(cropped_len, false)},
       {SPI_DEVICE_RXF_PTR_RPTR_OFFSET, FifoPtr(cropped_len, false)}});

  std::string buf(message.size() * 2, '\0');
  size_t recv_len = 0;
  EXPECT_EQ(dif_spi_device_recv(&spi_, const_cast<char *>(buf.data()),
                                buf.size(), &recv_len),
            kDifSpiDeviceOk);
  EXPECT_EQ(recv_len, cropped_len - cropped_start);

  buf.resize(message.size());
  EXPECT_NE(buf, message);

  buf.resize(recv_len);
  EXPECT_EQ(buf, message.substr(cropped_start, cropped_len - cropped_start));
}

TEST_F(RecvTest, UnalignedSmall) {
  std::string message = "Hello, SPI!!";
  ASSERT_EQ(message.size() % 4, 0);

  uintptr_t cropped_start = 1;
  uintptr_t cropped_len = 3;
  EXPECT_READ32(
      SPI_DEVICE_RXF_PTR_REG_OFFSET,
      {{SPI_DEVICE_RXF_PTR_WPTR_OFFSET, FifoPtr(cropped_len, false)},
       {SPI_DEVICE_RXF_PTR_RPTR_OFFSET, FifoPtr(cropped_start, false)}});

  auto fifo_base = SPI_DEVICE_BUFFER_REG_OFFSET;
  EXPECT_READ32(fifo_base + 0x0, LeInt(&message[0x0]));

  EXPECT_WRITE32(
      SPI_DEVICE_RXF_PTR_REG_OFFSET,
      {{SPI_DEVICE_RXF_PTR_WPTR_OFFSET, FifoPtr(cropped_len, false)},
       {SPI_DEVICE_RXF_PTR_RPTR_OFFSET, FifoPtr(cropped_len, false)}});

  std::string buf(message.size() * 2, '\0');
  size_t recv_len = 0;
  EXPECT_EQ(dif_spi_device_recv(&spi_, const_cast<char *>(buf.data()),
                                buf.size(), &recv_len),
            kDifSpiDeviceOk);
  EXPECT_EQ(recv_len, cropped_len - cropped_start);

  buf.resize(message.size());
  EXPECT_NE(buf, message);

  buf.resize(recv_len);
  EXPECT_EQ(buf, message.substr(cropped_start, cropped_len - cropped_start));
}

TEST_F(RecvTest, NullArgs) {
  std::string buf(16, '\0');
  size_t recv_len;

  EXPECT_EQ(dif_spi_device_recv(nullptr, const_cast<char *>(buf.data()),
                                buf.size(), &recv_len),
            kDifSpiDeviceBadArg);
  EXPECT_EQ(dif_spi_device_recv(&spi_, nullptr, buf.size(), &recv_len),
            kDifSpiDeviceBadArg);

  EXPECT_READ32(SPI_DEVICE_RXF_PTR_REG_OFFSET,
                {{SPI_DEVICE_RXF_PTR_WPTR_OFFSET, FifoPtr(0x5a, false)},
                 {SPI_DEVICE_RXF_PTR_RPTR_OFFSET, FifoPtr(0x5a, false)}});
  EXPECT_EQ(dif_spi_device_recv(&spi_, const_cast<char *>(buf.data()),
                                buf.size(), nullptr),
            kDifSpiDeviceOk);
}

class SendTest : public SpiTest {};

TEST_F(SendTest, FullFifo) {
  EXPECT_READ32(SPI_DEVICE_TXF_PTR_REG_OFFSET,
                {{SPI_DEVICE_TXF_PTR_WPTR_OFFSET, FifoPtr(0x5a, true)},
                 {SPI_DEVICE_TXF_PTR_RPTR_OFFSET, FifoPtr(0x5a, false)}});

  std::string message = "Hello, SPI!!";
  size_t send_len = 0;
  EXPECT_EQ(
      dif_spi_device_send(&spi_, message.data(), message.size(), &send_len),
      kDifSpiDeviceOk);
  EXPECT_EQ(send_len, 0);
}

TEST_F(SendTest, EmptyToFull) {
  EXPECT_READ32(SPI_DEVICE_TXF_PTR_REG_OFFSET,
                {{SPI_DEVICE_TXF_PTR_WPTR_OFFSET, FifoPtr(0x50, true)},
                 {SPI_DEVICE_TXF_PTR_RPTR_OFFSET, FifoPtr(0x50, true)}});

  auto message = MakeBlob(kFifoLen);
  auto fifo_base = SPI_DEVICE_BUFFER_REG_OFFSET + spi_.rx_fifo_len;
  for (int i = 0; i < kFifoLen; i += 4) {
    auto idx = fifo_base + (i + 0x50) % kFifoLen;
    EXPECT_WRITE32(idx, LeInt(&message[i]));
  }

  EXPECT_WRITE32(SPI_DEVICE_TXF_PTR_REG_OFFSET,
                 {{SPI_DEVICE_TXF_PTR_WPTR_OFFSET, FifoPtr(0x50, false)},
                  {SPI_DEVICE_TXF_PTR_RPTR_OFFSET, FifoPtr(0x50, true)}});

  size_t sent_len = 0;
  EXPECT_EQ(
      dif_spi_device_send(&spi_, message.data(), message.size(), &sent_len),
      kDifSpiDeviceOk);
  EXPECT_EQ(sent_len, message.size());
}

TEST_F(SendTest, AlmostFull) {
  EXPECT_READ32(SPI_DEVICE_TXF_PTR_REG_OFFSET,
                {{SPI_DEVICE_TXF_PTR_WPTR_OFFSET, FifoPtr(0x4e, true)},
                 {SPI_DEVICE_TXF_PTR_RPTR_OFFSET, FifoPtr(0x50, false)}});

  std::string message = "Hello, world!";
  uintptr_t value = 0;
  memcpy(&value, message.data(), 2);

  auto fifo_base = SPI_DEVICE_BUFFER_REG_OFFSET + spi_.rx_fifo_len;
  EXPECT_MASK32(fifo_base + 0x4c, {{0x10, 0xffff, value}});

  EXPECT_WRITE32(SPI_DEVICE_TXF_PTR_REG_OFFSET,
                 {{SPI_DEVICE_TXF_PTR_WPTR_OFFSET, FifoPtr(0x50, true)},
                  {SPI_DEVICE_TXF_PTR_RPTR_OFFSET, FifoPtr(0x50, false)}});

  size_t sent_len = 0;
  EXPECT_EQ(
      dif_spi_device_send(&spi_, message.data(), message.size(), &sent_len),
      kDifSpiDeviceOk);
  EXPECT_EQ(sent_len, 2);
}

TEST_F(SendTest, FullyAligned) {
  std::string message = "Hello, SPI!!";
  ASSERT_EQ(message.size() % 4, 0);

  EXPECT_READ32(SPI_DEVICE_TXF_PTR_REG_OFFSET,
                {{SPI_DEVICE_TXF_PTR_WPTR_OFFSET, FifoPtr(0x00, false)},
                 {SPI_DEVICE_TXF_PTR_RPTR_OFFSET, FifoPtr(0x00, false)}});

  auto fifo_base = SPI_DEVICE_BUFFER_REG_OFFSET + spi_.rx_fifo_len;
  EXPECT_WRITE32(fifo_base + 0x0, LeInt(&message[0x0]));
  EXPECT_WRITE32(fifo_base + 0x4, LeInt(&message[0x4]));
  EXPECT_WRITE32(fifo_base + 0x8, LeInt(&message[0x8]));

  EXPECT_WRITE32(
      SPI_DEVICE_TXF_PTR_REG_OFFSET,
      {{SPI_DEVICE_TXF_PTR_WPTR_OFFSET, FifoPtr(message.size(), false)},
       {SPI_DEVICE_TXF_PTR_RPTR_OFFSET, FifoPtr(0x0, false)}});

  size_t send_len = 0;
  EXPECT_EQ(
      dif_spi_device_send(&spi_, message.data(), message.size(), &send_len),
      kDifSpiDeviceOk);
  EXPECT_EQ(send_len, message.size());
}

TEST_F(SendTest, UnalignedMessage) {
  std::string message = "Hello, SPI!!";
  ASSERT_EQ(message.size() % 4, 0);

  uintptr_t cropped_len = 9;
  EXPECT_READ32(SPI_DEVICE_TXF_PTR_REG_OFFSET,
                {{SPI_DEVICE_TXF_PTR_WPTR_OFFSET, FifoPtr(0x00, false)},
                 {SPI_DEVICE_TXF_PTR_RPTR_OFFSET, FifoPtr(0x00, false)}});

  auto fifo_base = SPI_DEVICE_BUFFER_REG_OFFSET + spi_.rx_fifo_len;
  EXPECT_WRITE32(fifo_base + 0x0, LeInt(&message[0x0]));
  EXPECT_WRITE32(fifo_base + 0x4, LeInt(&message[0x4]));

  uintptr_t value = 0;
  memcpy(&value, &message[0x8], 1);
  EXPECT_MASK32(fifo_base + 0x8, {{0x0, 0xff, value}});

  EXPECT_WRITE32(SPI_DEVICE_TXF_PTR_REG_OFFSET,
                 {{SPI_DEVICE_TXF_PTR_WPTR_OFFSET, FifoPtr(cropped_len, false)},
                  {SPI_DEVICE_TXF_PTR_RPTR_OFFSET, FifoPtr(0x0, false)}});

  size_t send_len = 0;
  EXPECT_EQ(dif_spi_device_send(&spi_, message.data(), cropped_len, &send_len),
            kDifSpiDeviceOk);
  EXPECT_EQ(send_len, cropped_len);
}

TEST_F(SendTest, UnalignedStart) {
  std::string message = "Hello, SPI!!";
  ASSERT_EQ(message.size() % 4, 0);

  uintptr_t cropped_start = 1;
  uintptr_t cropped_len = 9;
  EXPECT_READ32(
      SPI_DEVICE_TXF_PTR_REG_OFFSET,
      {{SPI_DEVICE_TXF_PTR_WPTR_OFFSET, FifoPtr(cropped_start, false)},
       {SPI_DEVICE_TXF_PTR_RPTR_OFFSET, FifoPtr(cropped_start, false)}});

  auto fifo_base = SPI_DEVICE_BUFFER_REG_OFFSET + spi_.rx_fifo_len;

  uintptr_t start_value = 0;
  memcpy(&start_value, &message[0x0], 3);
  EXPECT_MASK32(fifo_base + 0x0, {{0x8, 0xffffff, start_value}});
  EXPECT_WRITE32(fifo_base + 0x4, LeInt(&message[0x3]));

  uintptr_t end_value = 0;
  memcpy(&end_value, &message[0x7], 2);
  EXPECT_MASK32(fifo_base + 0x8, {{0x0, 0xffff, end_value}});

  EXPECT_WRITE32(
      SPI_DEVICE_TXF_PTR_REG_OFFSET,
      {{SPI_DEVICE_TXF_PTR_WPTR_OFFSET,
        FifoPtr(cropped_len + cropped_start, false)},
       {SPI_DEVICE_TXF_PTR_RPTR_OFFSET, FifoPtr(cropped_start, false)}});

  size_t send_len = 0;
  EXPECT_EQ(dif_spi_device_send(&spi_, message.data(), cropped_len, &send_len),
            kDifSpiDeviceOk);
  EXPECT_EQ(send_len, cropped_len);
}

TEST_F(SendTest, UnalignedSmall) {
  std::string message = "Hello, SPI!!";
  ASSERT_EQ(message.size() % 4, 0);

  uintptr_t cropped_start = 1;
  uintptr_t cropped_len = 2;
  EXPECT_READ32(
      SPI_DEVICE_TXF_PTR_REG_OFFSET,
      {{SPI_DEVICE_TXF_PTR_WPTR_OFFSET, FifoPtr(cropped_start, false)},
       {SPI_DEVICE_TXF_PTR_RPTR_OFFSET, FifoPtr(cropped_start, false)}});

  auto fifo_base = SPI_DEVICE_BUFFER_REG_OFFSET + spi_.rx_fifo_len;

  uintptr_t start_value = 0;
  memcpy(&start_value, &message[0x0], 2);
  EXPECT_MASK32(fifo_base + 0x0, {{0x8, 0xffff, start_value}});

  EXPECT_WRITE32(
      SPI_DEVICE_TXF_PTR_REG_OFFSET,
      {{SPI_DEVICE_TXF_PTR_WPTR_OFFSET,
        FifoPtr(cropped_len + cropped_start, false)},
       {SPI_DEVICE_TXF_PTR_RPTR_OFFSET, FifoPtr(cropped_start, false)}});

  size_t send_len = 0;
  EXPECT_EQ(dif_spi_device_send(&spi_, message.data(), cropped_len, &send_len),
            kDifSpiDeviceOk);
  EXPECT_EQ(send_len, cropped_len);
}

TEST_F(SendTest, NullArgs) {
  std::string buf(16, '\0');
  size_t recv_len;

  EXPECT_EQ(dif_spi_device_send(nullptr, buf.data(), buf.size(), &recv_len),
            kDifSpiDeviceBadArg);
  EXPECT_EQ(dif_spi_device_send(&spi_, nullptr, buf.size(), &recv_len),
            kDifSpiDeviceBadArg);

  EXPECT_READ32(SPI_DEVICE_TXF_PTR_REG_OFFSET,
                {{SPI_DEVICE_TXF_PTR_WPTR_OFFSET, FifoPtr(0x5a, true)},
                 {SPI_DEVICE_TXF_PTR_RPTR_OFFSET, FifoPtr(0x5a, false)}});
  EXPECT_EQ(dif_spi_device_send(&spi_, buf.data(), buf.size(), nullptr),
            kDifSpiDeviceOk);
}
}  // namespace
}  // namespace dif_spi_device_unittest
