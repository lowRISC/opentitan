// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_uart.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/testing/mock_mmio.h"

#include "uart_regs.h"  // Generated.

namespace dif_uart_unittest {
namespace {
using mock_mmio::MmioTest;
using mock_mmio::MockDevice;
using testing::Each;
using testing::Eq;
using testing::Test;

const std::vector<uint8_t> kBytesArray = {
    '0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'a',
    'b', 'c', 'd', 'e', 'f', 'g', 'h', 'i', 'j', 'k', 'l',
    'm', 'n', 'o', 'p', 'q', 'r', 's', 't', 'u', 'v',
};

class UartTest : public Test, public MmioTest {
 protected:
  void ExpectDeviceReset() {
    EXPECT_WRITE32(UART_CTRL_REG_OFFSET, 0);
    EXPECT_WRITE32(UART_FIFO_CTRL_REG_OFFSET,
                   {
                       {UART_FIFO_CTRL_RXRST_BIT, true},
                       {UART_FIFO_CTRL_TXRST_BIT, true},
                   });
    EXPECT_WRITE32(UART_OVRD_REG_OFFSET, 0);
    EXPECT_WRITE32(UART_TIMEOUT_CTRL_REG_OFFSET, 0);
    EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);
    EXPECT_WRITE32(UART_INTR_STATE_REG_OFFSET,
                   std::numeric_limits<uint32_t>::max());
  }

  dif_uart_t uart_ = {
      .base_addr = dev().region(),
  };

  // NCO is calculated as NCO = 2^20 * fbaud / fpclk, so the following values
  // should result in NCO of 1. This is the default configuration, which will
  // be used unless the values are overridden.
  dif_uart_config_t config_ = {
      .baudrate = 1,
      .clk_freq_hz = 1048576,
      .parity_enable = kDifToggleDisabled,
      .parity = kDifUartParityEven,
  };
};

class ConfigTest : public UartTest {};

TEST_F(ConfigTest, NullArgs) {
  EXPECT_EQ(dif_uart_configure(nullptr, config_), kDifBadArg);
}

TEST_F(ConfigTest, Default) {
  ExpectDeviceReset();

  EXPECT_WRITE32(UART_CTRL_REG_OFFSET, {
                                           {UART_CTRL_TX_BIT, true},
                                           {UART_CTRL_RX_BIT, true},
                                           {UART_CTRL_NCO_OFFSET, 1},
                                       });

  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);

  EXPECT_EQ(dif_uart_configure(&uart_, config_), kDifOk);
}

TEST_F(ConfigTest, ParityEven) {
  config_.parity_enable = kDifToggleEnabled;
  config_.parity = kDifUartParityEven;

  ExpectDeviceReset();

  EXPECT_WRITE32(UART_CTRL_REG_OFFSET, {
                                           {UART_CTRL_TX_BIT, true},
                                           {UART_CTRL_RX_BIT, true},
                                           {UART_CTRL_PARITY_EN_BIT, true},
                                           {UART_CTRL_NCO_OFFSET, 1},
                                       });

  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);

  EXPECT_EQ(dif_uart_configure(&uart_, config_), kDifOk);
}

TEST_F(ConfigTest, ParityOdd) {
  config_.parity_enable = kDifToggleEnabled;
  config_.parity = kDifUartParityOdd;

  ExpectDeviceReset();

  EXPECT_WRITE32(UART_CTRL_REG_OFFSET, {
                                           {UART_CTRL_TX_BIT, true},
                                           {UART_CTRL_RX_BIT, true},
                                           {UART_CTRL_PARITY_EN_BIT, true},
                                           {UART_CTRL_PARITY_ODD_BIT, true},
                                           {UART_CTRL_NCO_OFFSET, 1},
                                       });

  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);

  EXPECT_EQ(dif_uart_configure(&uart_, config_), kDifOk);
}

class WatermarkRxSetTest : public UartTest {};

TEST_F(WatermarkRxSetTest, UartNull) {
  dif_result_t result =
      dif_uart_watermark_rx_set(nullptr, kDifUartWatermarkByte1);
  EXPECT_EQ(result, kDifBadArg);
}

/**
 * Tests the first and the last RX watermark variants.
 */
TEST_F(WatermarkRxSetTest, Success) {
  EXPECT_MASK32(UART_FIFO_CTRL_REG_OFFSET,
                {
                    {UART_FIFO_CTRL_RXILVL_OFFSET, UART_FIFO_CTRL_RXILVL_MASK,
                     UART_FIFO_CTRL_RXILVL_VALUE_RXLVL1},
                });
  EXPECT_EQ(dif_uart_watermark_rx_set(&uart_, kDifUartWatermarkByte1), kDifOk);

  EXPECT_MASK32(UART_FIFO_CTRL_REG_OFFSET,
                {
                    {UART_FIFO_CTRL_RXILVL_OFFSET, UART_FIFO_CTRL_RXILVL_MASK,
                     UART_FIFO_CTRL_RXILVL_VALUE_RXLVL30},
                });
  EXPECT_EQ(dif_uart_watermark_rx_set(&uart_, kDifUartWatermarkByte30), kDifOk);
}

class WatermarkTxSetTest : public UartTest {};

TEST_F(WatermarkTxSetTest, NullArgs) {
  EXPECT_EQ(dif_uart_watermark_tx_set(nullptr, kDifUartWatermarkByte1),
            kDifBadArg);
}

TEST_F(WatermarkTxSetTest, InvalidWatermark) {
  EXPECT_EQ(dif_uart_watermark_tx_set(&uart_, kDifUartWatermarkByte30),
            kDifError);
}

/**
 * Tests the first and the last TX watermark variants.
 */
TEST_F(WatermarkTxSetTest, Success) {
  EXPECT_MASK32(UART_FIFO_CTRL_REG_OFFSET,
                {
                    {UART_FIFO_CTRL_TXILVL_OFFSET, UART_FIFO_CTRL_TXILVL_MASK,
                     UART_FIFO_CTRL_TXILVL_VALUE_TXLVL1},
                });
  EXPECT_EQ(dif_uart_watermark_tx_set(&uart_, kDifUartWatermarkByte1), kDifOk);

  EXPECT_MASK32(UART_FIFO_CTRL_REG_OFFSET,
                {
                    {UART_FIFO_CTRL_TXILVL_OFFSET, UART_FIFO_CTRL_TXILVL_MASK,
                     UART_FIFO_CTRL_TXILVL_VALUE_TXLVL16},
                });
  EXPECT_EQ(dif_uart_watermark_tx_set(&uart_, kDifUartWatermarkByte16), kDifOk);
}

class BytesSendTest : public UartTest {
 protected:
  /**
   * Sets TX bytes expectations.
   *
   * Every sent byte by the "send bytes" routine is expected to result in the
   * STATUS read of 0 (FIFO not full), and write to WDATA.
   */
  void ExpectSendBytes(int num_elements = kBytesArray.size()) {
    ASSERT_LE(num_elements, kBytesArray.size());
    for (int i = 0; i < num_elements; ++i) {
      uint32_t value = static_cast<uint32_t>(kBytesArray[i]);
      EXPECT_READ32(UART_STATUS_REG_OFFSET, 0);
      EXPECT_WRITE32(UART_WDATA_REG_OFFSET, value);
    }
  }
};

TEST_F(BytesSendTest, NullArgs) {
  EXPECT_EQ(dif_uart_bytes_send(nullptr, kBytesArray.data(), 1, nullptr),
            kDifBadArg);

  EXPECT_EQ(dif_uart_bytes_send(&uart_, nullptr, 1, nullptr), kDifBadArg);

  EXPECT_EQ(dif_uart_bytes_send(nullptr, nullptr, 1, nullptr), kDifBadArg);
}

TEST_F(BytesSendTest, TxFifoEmptyBytesWrittenNull) {
  ExpectSendBytes();
  EXPECT_EQ(dif_uart_bytes_send(&uart_, kBytesArray.data(), kBytesArray.size(),
                                nullptr),
            kDifOk);
}

TEST_F(BytesSendTest, TxFifoEmpty) {
  ExpectSendBytes();

  size_t bytes_written;
  EXPECT_EQ(dif_uart_bytes_send(&uart_, kBytesArray.data(), kBytesArray.size(),
                                &bytes_written),
            kDifOk);
  EXPECT_EQ(bytes_written, kBytesArray.size());
}

TEST_F(BytesSendTest, TxFifoFull) {
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_TXFULL_BIT, true}});

  size_t bytes_written;
  EXPECT_EQ(dif_uart_bytes_send(&uart_, kBytesArray.data(), kBytesArray.size(),
                                &bytes_written),
            kDifOk);
  EXPECT_EQ(bytes_written, 0);
}

class BytesReceiveTest : public UartTest {
 protected:
  /**
   * Sets RX bytes expectations.
   *
   * Every read byte by the "receive bytes" routine is expected to result in the
   * STATUS read of 0 (FIFO not empty), and read of RDATA.
   */
  void ExpectReceiveBytes(int num_elements) {
    for (int i = 0; i < num_elements; ++i) {
      uint32_t value = static_cast<uint32_t>(kBytesArray[i]);
      EXPECT_READ32(UART_STATUS_REG_OFFSET, 0);
      EXPECT_READ32(UART_RDATA_REG_OFFSET, value);
    }
  }
};

TEST_F(BytesReceiveTest, UartNull) {
  std::vector<uint8_t> receive_bytes(1);

  EXPECT_EQ(dif_uart_bytes_receive(nullptr, 1, receive_bytes.data(), nullptr),
            kDifBadArg);
  EXPECT_THAT(receive_bytes, Each(Eq(0)));

  EXPECT_EQ(dif_uart_bytes_receive(&uart_, 1, nullptr, nullptr), kDifBadArg);

  EXPECT_EQ(dif_uart_bytes_receive(nullptr, 1, nullptr, nullptr), kDifBadArg);
}

TEST_F(BytesReceiveTest, RxFifoFullBytesWrittenNull) {
  uint8_t num_bytes = kBytesArray.size();
  ExpectReceiveBytes(num_bytes);

  std::vector<uint8_t> receive_bytes(num_bytes);
  EXPECT_EQ(
      dif_uart_bytes_receive(&uart_, num_bytes, receive_bytes.data(), nullptr),
      kDifOk);
  EXPECT_EQ(receive_bytes, kBytesArray);
}

TEST_F(BytesReceiveTest, RxFifoFull) {
  uint8_t num_bytes = kBytesArray.size();
  ExpectReceiveBytes(num_bytes);

  size_t bytes_read;
  std::vector<uint8_t> receive_bytes(num_bytes);
  EXPECT_EQ(dif_uart_bytes_receive(&uart_, num_bytes, receive_bytes.data(),
                                   &bytes_read),
            kDifOk);
  EXPECT_EQ(bytes_read, num_bytes);
  EXPECT_EQ(receive_bytes, kBytesArray);
}

TEST_F(BytesReceiveTest, RxFifoEmpty) {
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_RXEMPTY_BIT, true}});

  uint8_t num_bytes = kBytesArray.size();

  size_t bytes_read;
  std::vector<uint8_t> receive_bytes(num_bytes);
  EXPECT_EQ(dif_uart_bytes_receive(&uart_, num_bytes, receive_bytes.data(),
                                   &bytes_read),
            kDifOk);
  EXPECT_EQ(bytes_read, 0);
  EXPECT_THAT(receive_bytes, Each(Eq(0)));
}

class BytesSendPolledTest : public UartTest {};

TEST_F(BytesSendPolledTest, NullArgs) {
  dif_result_t result = dif_uart_byte_send_polled(nullptr, 'X');
  EXPECT_EQ(result, kDifBadArg);
}

TEST_F(BytesSendPolledTest, Success) {
  // Busy loop 1 iteration (waiting for TX FIFO to free up)
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_TXFULL_BIT, true}});
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_TXFULL_BIT, false}});

  // Set expectations for the byte to be set
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_TXFULL_BIT, false}});
  EXPECT_WRITE32(UART_WDATA_REG_OFFSET, 'X');

  // Busy loop 1 iteration (waiting for the byte to be sent out by the HW)
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_TXIDLE_BIT, false}});
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_TXIDLE_BIT, true}});

  EXPECT_EQ(dif_uart_byte_send_polled(&uart_, 'X'), kDifOk);
}

class BytesReceivePolledTest : public UartTest {};

TEST_F(BytesReceivePolledTest, NullArgs) {
  uint8_t byte;
  EXPECT_EQ(dif_uart_byte_receive_polled(nullptr, &byte), kDifBadArg);

  EXPECT_EQ(dif_uart_byte_receive_polled(&uart_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_uart_byte_receive_polled(nullptr, nullptr), kDifBadArg);
}

TEST_F(BytesReceivePolledTest, Success) {
  // Busy loop 1 iteration (waiting for RX FIFO to fill up)
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_RXEMPTY_BIT, true}});
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_RXEMPTY_BIT, false}});

  // Set expectations for the byte to be read
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_RXEMPTY_BIT, false}});
  EXPECT_READ32(UART_RDATA_REG_OFFSET, 'X');

  uint8_t byte = 'Y';
  EXPECT_EQ(dif_uart_byte_receive_polled(&uart_, &byte), kDifOk);
  EXPECT_EQ(byte, 'X');
}

class RxBytesAvailableTest : public UartTest {};

TEST_F(RxBytesAvailableTest, NullArgs) {
  size_t num_bytes;
  EXPECT_EQ(dif_uart_rx_bytes_available(nullptr, &num_bytes), kDifBadArg);

  EXPECT_EQ(dif_uart_rx_bytes_available(&uart_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_uart_rx_bytes_available(nullptr, nullptr), kDifBadArg);
}

TEST_F(RxBytesAvailableTest, FifoFull) {
  // kDifUartFifoSizeBytes bytes available to read.
  EXPECT_READ32(UART_FIFO_STATUS_REG_OFFSET,
                {{UART_FIFO_STATUS_RXLVL_OFFSET, kDifUartFifoSizeBytes}});

  size_t num_bytes;
  EXPECT_EQ(dif_uart_rx_bytes_available(&uart_, &num_bytes), kDifOk);
  EXPECT_EQ(num_bytes, kDifUartFifoSizeBytes);
}

TEST_F(RxBytesAvailableTest, FifoEmpty) {
  // 0 bytes available to read.
  EXPECT_READ32(UART_FIFO_STATUS_REG_OFFSET,
                {{UART_FIFO_STATUS_RXLVL_OFFSET, 0}});

  size_t num_bytes;
  EXPECT_EQ(dif_uart_rx_bytes_available(&uart_, &num_bytes), kDifOk);
  EXPECT_EQ(num_bytes, 0);
}

class TxBytesAvailableTest : public UartTest {};

TEST_F(TxBytesAvailableTest, NullArgs) {
  size_t num_bytes;
  EXPECT_EQ(dif_uart_tx_bytes_available(nullptr, &num_bytes), kDifBadArg);

  EXPECT_EQ(dif_uart_tx_bytes_available(&uart_, nullptr), kDifBadArg);

  EXPECT_EQ(dif_uart_tx_bytes_available(nullptr, nullptr), kDifBadArg);
}

TEST_F(TxBytesAvailableTest, FifoFull) {
  // 0 bytes available to write.
  EXPECT_READ32(UART_FIFO_STATUS_REG_OFFSET,
                {{UART_FIFO_STATUS_TXLVL_OFFSET, kDifUartFifoSizeBytes}});

  size_t num_bytes;
  EXPECT_EQ(dif_uart_tx_bytes_available(&uart_, &num_bytes), kDifOk);
  EXPECT_EQ(num_bytes, 0);
}

TEST_F(TxBytesAvailableTest, FifoEmpty) {
  // kDifUartFifoSizeBytes available to write.
  EXPECT_READ32(UART_FIFO_STATUS_REG_OFFSET,
                {{UART_FIFO_STATUS_TXLVL_OFFSET, 0}});

  size_t num_bytes;
  EXPECT_EQ(dif_uart_tx_bytes_available(&uart_, &num_bytes), kDifOk);
  EXPECT_EQ(num_bytes, kDifUartFifoSizeBytes);
}

class FifoResetTest : public UartTest {};

TEST_F(FifoResetTest, NullArgs) {
  dif_result_t result = dif_uart_fifo_reset(nullptr, kDifUartFifoResetRx);
  EXPECT_EQ(result, kDifBadArg);
}

TEST_F(FifoResetTest, Success) {
  EXPECT_READ32(UART_FIFO_CTRL_REG_OFFSET, 0);
  EXPECT_WRITE32(UART_FIFO_CTRL_REG_OFFSET, {{UART_FIFO_CTRL_RXRST_BIT, true}});
  EXPECT_EQ(dif_uart_fifo_reset(&uart_, kDifUartFifoResetRx), kDifOk);

  EXPECT_READ32(UART_FIFO_CTRL_REG_OFFSET, 0);
  EXPECT_WRITE32(UART_FIFO_CTRL_REG_OFFSET, {{UART_FIFO_CTRL_TXRST_BIT, true}});
  EXPECT_EQ(dif_uart_fifo_reset(&uart_, kDifUartFifoResetTx), kDifOk);

  EXPECT_READ32(UART_FIFO_CTRL_REG_OFFSET, 0);
  EXPECT_WRITE32(UART_FIFO_CTRL_REG_OFFSET,
                 {
                     {UART_FIFO_CTRL_RXRST_BIT, true},
                     {UART_FIFO_CTRL_TXRST_BIT, true},
                 });
  EXPECT_EQ(dif_uart_fifo_reset(&uart_, kDifUartFifoResetAll), kDifOk);
}

class LoopbackSetTest : public UartTest {};

TEST_F(LoopbackSetTest, NullArgs) {
  EXPECT_EQ(
      dif_uart_loopback_set(nullptr, kDifUartLoopbackSystem, kDifToggleEnabled),
      kDifBadArg);
}

TEST_F(LoopbackSetTest, Success) {
  EXPECT_MASK32(UART_CTRL_REG_OFFSET, {{UART_CTRL_SLPBK_BIT, 0x1, true}});
  EXPECT_EQ(
      dif_uart_loopback_set(&uart_, kDifUartLoopbackSystem, kDifToggleEnabled),
      kDifOk);

  EXPECT_MASK32(UART_CTRL_REG_OFFSET, {{UART_CTRL_SLPBK_BIT, 0x1, false}});
  EXPECT_EQ(
      dif_uart_loopback_set(&uart_, kDifUartLoopbackSystem, kDifToggleDisabled),
      kDifOk);

  EXPECT_MASK32(UART_CTRL_REG_OFFSET, {{UART_CTRL_LLPBK_BIT, 0x1, true}});
  EXPECT_EQ(
      dif_uart_loopback_set(&uart_, kDifUartLoopbackLine, kDifToggleEnabled),
      kDifOk);

  EXPECT_MASK32(UART_CTRL_REG_OFFSET, {{UART_CTRL_LLPBK_BIT, 0x1, false}});
  EXPECT_EQ(
      dif_uart_loopback_set(&uart_, kDifUartLoopbackLine, kDifToggleDisabled),
      kDifOk);
}

class RxTimeoutTest : public UartTest {};

TEST_F(RxTimeoutTest, NullArgs) {
  EXPECT_EQ(dif_uart_enable_rx_timeout(nullptr, 1), kDifBadArg);
  EXPECT_EQ(dif_uart_disable_rx_timeout(nullptr), kDifBadArg);

  uint32_t value;       // optional
  dif_toggle_t status;  // mandatory
  EXPECT_EQ(dif_uart_get_rx_timeout(nullptr, &status, &value), kDifBadArg);
  EXPECT_EQ(dif_uart_get_rx_timeout(&uart_, nullptr, &value), kDifBadArg);
}

TEST_F(RxTimeoutTest, OutOfRange) {
  // RX timeout value must be in the range [0,0xffffff].
  EXPECT_EQ(dif_uart_enable_rx_timeout(&uart_, 0x01000000), kDifBadArg);
  EXPECT_EQ(dif_uart_enable_rx_timeout(&uart_, 0xffffffff), kDifBadArg);
}

TEST_F(RxTimeoutTest, Enable) {
  // Enable RX timeout and set to 0x123.
  const uint32_t duration = 0x123;
  EXPECT_WRITE32(UART_TIMEOUT_CTRL_REG_OFFSET,
                 {{UART_TIMEOUT_CTRL_VAL_OFFSET, duration},
                  {UART_TIMEOUT_CTRL_EN_BIT, true}});
  EXPECT_EQ(dif_uart_enable_rx_timeout(&uart_, duration), kDifOk);
}

TEST_F(RxTimeoutTest, Disable) {
  // Disable RX timeout.
  EXPECT_WRITE32(
      UART_TIMEOUT_CTRL_REG_OFFSET,
      {{UART_TIMEOUT_CTRL_VAL_OFFSET, 0}, {UART_TIMEOUT_CTRL_EN_BIT, false}});
  EXPECT_EQ(dif_uart_disable_rx_timeout(&uart_), kDifOk);
}

TEST_F(RxTimeoutTest, GetStatusOnly) {
  // Enable RX timeout and set to 0x800000.
  const uint32_t duration = 0x800000;
  EXPECT_WRITE32(UART_TIMEOUT_CTRL_REG_OFFSET,
                 {{UART_TIMEOUT_CTRL_VAL_OFFSET, duration},
                  {UART_TIMEOUT_CTRL_EN_BIT, true}});
  EXPECT_EQ(dif_uart_enable_rx_timeout(&uart_, duration), kDifOk);

  // Read out status only.
  dif_toggle_t status = kDifToggleDisabled;
  EXPECT_READ32(UART_TIMEOUT_CTRL_REG_OFFSET,
                {{UART_TIMEOUT_CTRL_VAL_OFFSET, duration},
                 {UART_TIMEOUT_CTRL_EN_BIT, true}});
  EXPECT_EQ(dif_uart_get_rx_timeout(&uart_, &status, nullptr), kDifOk);
  EXPECT_EQ(status, kDifToggleEnabled);
}

TEST_F(RxTimeoutTest, GetAll) {
  // Enable RX timeout and set to 0xf0f0f0.
  const uint32_t duration = 0xf0f0f0;
  EXPECT_WRITE32(UART_TIMEOUT_CTRL_REG_OFFSET,
                 {{UART_TIMEOUT_CTRL_VAL_OFFSET, duration},
                  {UART_TIMEOUT_CTRL_EN_BIT, true}});
  EXPECT_EQ(dif_uart_enable_rx_timeout(&uart_, duration), kDifOk);

  // Read out duration and status.
  uint32_t out = 0;
  dif_toggle_t status = kDifToggleDisabled;
  EXPECT_READ32(UART_TIMEOUT_CTRL_REG_OFFSET,
                {{UART_TIMEOUT_CTRL_VAL_OFFSET, duration},
                 {UART_TIMEOUT_CTRL_EN_BIT, true}});
  EXPECT_EQ(dif_uart_get_rx_timeout(&uart_, &status, &out), kDifOk);
  EXPECT_EQ(status, kDifToggleEnabled);
  EXPECT_EQ(out, duration);
}

}  // namespace
}  // namespace dif_uart_unittest
