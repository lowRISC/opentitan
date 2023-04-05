// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_uart.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/mock_mmio.h"
#include "sw/device/lib/dif/dif_test_base.h"

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
      .tx_enable = kDifToggleEnabled,
      .rx_enable = kDifToggleEnabled,
  };
};

class ConfigTest : public UartTest {};

TEST_F(ConfigTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_uart_configure(nullptr, config_));
}

TEST_F(ConfigTest, DefaultTxRxEnabled) {
  ExpectDeviceReset();
  EXPECT_WRITE32(UART_CTRL_REG_OFFSET, {
                                           {UART_CTRL_TX_BIT, true},
                                           {UART_CTRL_RX_BIT, true},
                                           {UART_CTRL_NCO_OFFSET, 1},
                                       });
  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_DIF_OK(dif_uart_configure(&uart_, config_));
}

TEST_F(ConfigTest, DefaultTxEnabled) {
  ExpectDeviceReset();
  EXPECT_WRITE32(UART_CTRL_REG_OFFSET, {
                                           {UART_CTRL_TX_BIT, true},
                                           {UART_CTRL_NCO_OFFSET, 1},
                                       });
  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);
  config_.rx_enable = kDifToggleDisabled;
  EXPECT_DIF_OK(dif_uart_configure(&uart_, config_));
}

TEST_F(ConfigTest, DefaultRxEnabled) {
  ExpectDeviceReset();
  EXPECT_WRITE32(UART_CTRL_REG_OFFSET, {
                                           {UART_CTRL_RX_BIT, true},
                                           {UART_CTRL_NCO_OFFSET, 1},
                                       });
  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);
  config_.tx_enable = kDifToggleDisabled;
  EXPECT_DIF_OK(dif_uart_configure(&uart_, config_));
}

TEST_F(ConfigTest, DefaultTxRxDisabled) {
  ExpectDeviceReset();
  EXPECT_WRITE32(UART_CTRL_REG_OFFSET, {{UART_CTRL_NCO_OFFSET, 1}});
  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);
  config_.tx_enable = kDifToggleDisabled;
  config_.rx_enable = kDifToggleDisabled;
  EXPECT_DIF_OK(dif_uart_configure(&uart_, config_));
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

  EXPECT_DIF_OK(dif_uart_configure(&uart_, config_));
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

  EXPECT_DIF_OK(dif_uart_configure(&uart_, config_));
}

class WatermarkRxSetTest : public UartTest {};

TEST_F(WatermarkRxSetTest, UartNull) {
  dif_result_t result =
      dif_uart_watermark_rx_set(nullptr, kDifUartWatermarkByte1);
  EXPECT_DIF_BADARG(result);
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
  EXPECT_DIF_OK(dif_uart_watermark_rx_set(&uart_, kDifUartWatermarkByte1));

  EXPECT_MASK32(UART_FIFO_CTRL_REG_OFFSET,
                {
                    {UART_FIFO_CTRL_RXILVL_OFFSET, UART_FIFO_CTRL_RXILVL_MASK,
                     UART_FIFO_CTRL_RXILVL_VALUE_RXLVL126},
                });
  EXPECT_DIF_OK(dif_uart_watermark_rx_set(&uart_, kDifUartWatermarkByte126));
}

class WatermarkTxSetTest : public UartTest {};

TEST_F(WatermarkTxSetTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_uart_watermark_tx_set(nullptr, kDifUartWatermarkByte1));
}

TEST_F(WatermarkTxSetTest, InvalidWatermark) {
  EXPECT_EQ(dif_uart_watermark_tx_set(&uart_, kDifUartWatermarkByte126),
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
  EXPECT_DIF_OK(dif_uart_watermark_tx_set(&uart_, kDifUartWatermarkByte1));

  EXPECT_MASK32(UART_FIFO_CTRL_REG_OFFSET,
                {
                    {UART_FIFO_CTRL_TXILVL_OFFSET, UART_FIFO_CTRL_TXILVL_MASK,
                     UART_FIFO_CTRL_TXILVL_VALUE_TXLVL64},
                });
  EXPECT_DIF_OK(dif_uart_watermark_tx_set(&uart_, kDifUartWatermarkByte64));
}

class SetEnableTest : public UartTest {};

TEST_F(SetEnableTest, NullArg) {
  EXPECT_DIF_BADARG(
      dif_uart_set_enable(nullptr, kDifUartDatapathAll, kDifToggleEnabled));
}

TEST_F(SetEnableTest, BadEnabled) {
  EXPECT_DIF_BADARG(dif_uart_set_enable(&uart_, kDifUartDatapathAll,
                                        static_cast<dif_toggle_t>(2)));
}

TEST_F(SetEnableTest, BadDatapath) {
  EXPECT_READ32(UART_CTRL_REG_OFFSET, 0);
  EXPECT_DIF_BADARG(dif_uart_set_enable(
      &uart_, static_cast<dif_uart_datapath_t>(kDifUartDatapathAll + 1),
      kDifToggleEnabled));
}

TEST_F(SetEnableTest, SuccessRxEnabledDisabled) {
  EXPECT_READ32(UART_CTRL_REG_OFFSET, {
                                          {UART_CTRL_RX_BIT, 0},
                                          {UART_CTRL_TX_BIT, 1},
                                      });
  EXPECT_WRITE32(UART_CTRL_REG_OFFSET, {
                                           {UART_CTRL_RX_BIT, 1},
                                           {UART_CTRL_TX_BIT, 1},
                                       });
  EXPECT_DIF_OK(
      dif_uart_set_enable(&uart_, kDifUartDatapathRx, kDifToggleEnabled));

  EXPECT_READ32(UART_CTRL_REG_OFFSET, {
                                          {UART_CTRL_RX_BIT, 1},
                                          {UART_CTRL_TX_BIT, 1},
                                      });
  EXPECT_WRITE32(UART_CTRL_REG_OFFSET, {
                                           {UART_CTRL_RX_BIT, 0},
                                           {UART_CTRL_TX_BIT, 1},
                                       });
  EXPECT_DIF_OK(
      dif_uart_set_enable(&uart_, kDifUartDatapathRx, kDifToggleDisabled));
}

TEST_F(SetEnableTest, SuccessTxEnabledDisabled) {
  EXPECT_READ32(UART_CTRL_REG_OFFSET, {
                                          {UART_CTRL_RX_BIT, 1},
                                          {UART_CTRL_TX_BIT, 0},
                                      });
  EXPECT_WRITE32(UART_CTRL_REG_OFFSET, {
                                           {UART_CTRL_RX_BIT, 1},
                                           {UART_CTRL_TX_BIT, 1},
                                       });
  EXPECT_DIF_OK(
      dif_uart_set_enable(&uart_, kDifUartDatapathTx, kDifToggleEnabled));

  EXPECT_READ32(UART_CTRL_REG_OFFSET, {
                                          {UART_CTRL_RX_BIT, 1},
                                          {UART_CTRL_TX_BIT, 1},
                                      });
  EXPECT_WRITE32(UART_CTRL_REG_OFFSET, {
                                           {UART_CTRL_RX_BIT, 1},
                                           {UART_CTRL_TX_BIT, 0},
                                       });
  EXPECT_DIF_OK(
      dif_uart_set_enable(&uart_, kDifUartDatapathTx, kDifToggleDisabled));
}

TEST_F(SetEnableTest, SuccessRxTxEnabledDisabled) {
  EXPECT_READ32(UART_CTRL_REG_OFFSET, {
                                          {UART_CTRL_RX_BIT, 0},
                                          {UART_CTRL_TX_BIT, 0},
                                      });
  EXPECT_WRITE32(UART_CTRL_REG_OFFSET, {
                                           {UART_CTRL_RX_BIT, 1},
                                           {UART_CTRL_TX_BIT, 1},
                                       });
  EXPECT_DIF_OK(
      dif_uart_set_enable(&uart_, kDifUartDatapathAll, kDifToggleEnabled));

  EXPECT_READ32(UART_CTRL_REG_OFFSET, {
                                          {UART_CTRL_RX_BIT, 1},
                                          {UART_CTRL_TX_BIT, 1},
                                      });
  EXPECT_WRITE32(UART_CTRL_REG_OFFSET, {
                                           {UART_CTRL_RX_BIT, 0},
                                           {UART_CTRL_TX_BIT, 0},
                                       });
  EXPECT_DIF_OK(
      dif_uart_set_enable(&uart_, kDifUartDatapathAll, kDifToggleDisabled));
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
  EXPECT_DIF_BADARG(
      dif_uart_bytes_send(nullptr, kBytesArray.data(), 1, nullptr));

  EXPECT_DIF_BADARG(dif_uart_bytes_send(&uart_, nullptr, 1, nullptr));

  EXPECT_DIF_BADARG(dif_uart_bytes_send(nullptr, nullptr, 1, nullptr));
}

TEST_F(BytesSendTest, TxFifoEmptyBytesWrittenNull) {
  ExpectSendBytes();
  EXPECT_DIF_OK(dif_uart_bytes_send(&uart_, kBytesArray.data(),
                                    kBytesArray.size(), nullptr));
}

TEST_F(BytesSendTest, TxFifoEmpty) {
  ExpectSendBytes();

  size_t bytes_written;
  EXPECT_DIF_OK(dif_uart_bytes_send(&uart_, kBytesArray.data(),
                                    kBytesArray.size(), &bytes_written));
  EXPECT_EQ(bytes_written, kBytesArray.size());
}

TEST_F(BytesSendTest, TxFifoFull) {
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_TXFULL_BIT, true}});

  size_t bytes_written;
  EXPECT_DIF_OK(dif_uart_bytes_send(&uart_, kBytesArray.data(),
                                    kBytesArray.size(), &bytes_written));
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

  EXPECT_DIF_BADARG(
      dif_uart_bytes_receive(nullptr, 1, receive_bytes.data(), nullptr));
  EXPECT_THAT(receive_bytes, Each(Eq(0)));

  EXPECT_DIF_BADARG(dif_uart_bytes_receive(&uart_, 1, nullptr, nullptr));

  EXPECT_DIF_BADARG(dif_uart_bytes_receive(nullptr, 1, nullptr, nullptr));
}

TEST_F(BytesReceiveTest, RxFifoFullBytesWrittenNull) {
  uint8_t num_bytes = kBytesArray.size();
  ExpectReceiveBytes(num_bytes);

  std::vector<uint8_t> receive_bytes(num_bytes);
  EXPECT_DIF_OK(
      dif_uart_bytes_receive(&uart_, num_bytes, receive_bytes.data(), nullptr));
  EXPECT_EQ(receive_bytes, kBytesArray);
}

TEST_F(BytesReceiveTest, RxFifoFull) {
  uint8_t num_bytes = kBytesArray.size();
  ExpectReceiveBytes(num_bytes);

  size_t bytes_read;
  std::vector<uint8_t> receive_bytes(num_bytes);
  EXPECT_DIF_OK(dif_uart_bytes_receive(&uart_, num_bytes, receive_bytes.data(),
                                       &bytes_read));
  EXPECT_EQ(bytes_read, num_bytes);
  EXPECT_EQ(receive_bytes, kBytesArray);
}

TEST_F(BytesReceiveTest, RxFifoEmpty) {
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_RXEMPTY_BIT, true}});

  uint8_t num_bytes = kBytesArray.size();

  size_t bytes_read;
  std::vector<uint8_t> receive_bytes(num_bytes);
  EXPECT_DIF_OK(dif_uart_bytes_receive(&uart_, num_bytes, receive_bytes.data(),
                                       &bytes_read));
  EXPECT_EQ(bytes_read, 0);
  EXPECT_THAT(receive_bytes, Each(Eq(0)));
}

class BytesSendPolledTest : public UartTest {};

TEST_F(BytesSendPolledTest, NullArgs) {
  dif_result_t result = dif_uart_byte_send_polled(nullptr, 'X');
  EXPECT_DIF_BADARG(result);
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

  EXPECT_DIF_OK(dif_uart_byte_send_polled(&uart_, 'X'));
}

class BytesReceivePolledTest : public UartTest {};

TEST_F(BytesReceivePolledTest, NullArgs) {
  uint8_t byte;
  EXPECT_DIF_BADARG(dif_uart_byte_receive_polled(nullptr, &byte));

  EXPECT_DIF_BADARG(dif_uart_byte_receive_polled(&uart_, nullptr));

  EXPECT_DIF_BADARG(dif_uart_byte_receive_polled(nullptr, nullptr));
}

TEST_F(BytesReceivePolledTest, Success) {
  // Busy loop 1 iteration (waiting for RX FIFO to fill up)
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_RXEMPTY_BIT, true}});
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_RXEMPTY_BIT, false}});

  // Set expectations for the byte to be read
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_RXEMPTY_BIT, false}});
  EXPECT_READ32(UART_RDATA_REG_OFFSET, 'X');

  uint8_t byte = 'Y';
  EXPECT_DIF_OK(dif_uart_byte_receive_polled(&uart_, &byte));
  EXPECT_EQ(byte, 'X');
}

class RxBytesAvailableTest : public UartTest {};

TEST_F(RxBytesAvailableTest, NullArgs) {
  size_t num_bytes;
  EXPECT_DIF_BADARG(dif_uart_rx_bytes_available(nullptr, &num_bytes));

  EXPECT_DIF_BADARG(dif_uart_rx_bytes_available(&uart_, nullptr));

  EXPECT_DIF_BADARG(dif_uart_rx_bytes_available(nullptr, nullptr));
}

TEST_F(RxBytesAvailableTest, FifoFull) {
  // kDifUartFifoSizeBytes bytes available to read.
  EXPECT_READ32(UART_FIFO_STATUS_REG_OFFSET,
                {{UART_FIFO_STATUS_RXLVL_OFFSET, kDifUartFifoSizeBytes}});

  size_t num_bytes;
  EXPECT_DIF_OK(dif_uart_rx_bytes_available(&uart_, &num_bytes));
  EXPECT_EQ(num_bytes, kDifUartFifoSizeBytes);
}

TEST_F(RxBytesAvailableTest, FifoEmpty) {
  // 0 bytes available to read.
  EXPECT_READ32(UART_FIFO_STATUS_REG_OFFSET,
                {{UART_FIFO_STATUS_RXLVL_OFFSET, 0}});

  size_t num_bytes;
  EXPECT_DIF_OK(dif_uart_rx_bytes_available(&uart_, &num_bytes));
  EXPECT_EQ(num_bytes, 0);
}

class TxBytesAvailableTest : public UartTest {};

TEST_F(TxBytesAvailableTest, NullArgs) {
  size_t num_bytes;
  EXPECT_DIF_BADARG(dif_uart_tx_bytes_available(nullptr, &num_bytes));

  EXPECT_DIF_BADARG(dif_uart_tx_bytes_available(&uart_, nullptr));

  EXPECT_DIF_BADARG(dif_uart_tx_bytes_available(nullptr, nullptr));
}

TEST_F(TxBytesAvailableTest, FifoFull) {
  // 0 bytes available to write.
  EXPECT_READ32(UART_FIFO_STATUS_REG_OFFSET,
                {{UART_FIFO_STATUS_TXLVL_OFFSET, kDifUartFifoSizeBytes}});

  size_t num_bytes;
  EXPECT_DIF_OK(dif_uart_tx_bytes_available(&uart_, &num_bytes));
  EXPECT_EQ(num_bytes, 0);
}

TEST_F(TxBytesAvailableTest, FifoEmpty) {
  // kDifUartFifoSizeBytes available to write.
  EXPECT_READ32(UART_FIFO_STATUS_REG_OFFSET,
                {{UART_FIFO_STATUS_TXLVL_OFFSET, 0}});

  size_t num_bytes;
  EXPECT_DIF_OK(dif_uart_tx_bytes_available(&uart_, &num_bytes));
  EXPECT_EQ(num_bytes, kDifUartFifoSizeBytes);
}

class FifoResetTest : public UartTest {};

TEST_F(FifoResetTest, NullArgs) {
  dif_result_t result = dif_uart_fifo_reset(nullptr, kDifUartDatapathRx);
  EXPECT_DIF_BADARG(result);
}

TEST_F(FifoResetTest, Success) {
  EXPECT_READ32(UART_FIFO_CTRL_REG_OFFSET, 0);
  EXPECT_WRITE32(UART_FIFO_CTRL_REG_OFFSET, {{UART_FIFO_CTRL_RXRST_BIT, true}});
  EXPECT_DIF_OK(dif_uart_fifo_reset(&uart_, kDifUartDatapathRx));

  EXPECT_READ32(UART_FIFO_CTRL_REG_OFFSET, 0);
  EXPECT_WRITE32(UART_FIFO_CTRL_REG_OFFSET, {{UART_FIFO_CTRL_TXRST_BIT, true}});
  EXPECT_DIF_OK(dif_uart_fifo_reset(&uart_, kDifUartDatapathTx));

  EXPECT_READ32(UART_FIFO_CTRL_REG_OFFSET, 0);
  EXPECT_WRITE32(UART_FIFO_CTRL_REG_OFFSET,
                 {
                     {UART_FIFO_CTRL_RXRST_BIT, true},
                     {UART_FIFO_CTRL_TXRST_BIT, true},
                 });
  EXPECT_DIF_OK(dif_uart_fifo_reset(&uart_, kDifUartDatapathAll));
}

class LoopbackSetTest : public UartTest {};

TEST_F(LoopbackSetTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_uart_loopback_set(nullptr, kDifUartLoopbackSystem,
                                          kDifToggleEnabled));
}

TEST_F(LoopbackSetTest, Success) {
  EXPECT_MASK32(UART_CTRL_REG_OFFSET, {{UART_CTRL_SLPBK_BIT, 0x1, true}});
  EXPECT_DIF_OK(
      dif_uart_loopback_set(&uart_, kDifUartLoopbackSystem, kDifToggleEnabled));

  EXPECT_MASK32(UART_CTRL_REG_OFFSET, {{UART_CTRL_SLPBK_BIT, 0x1, false}});
  EXPECT_DIF_OK(dif_uart_loopback_set(&uart_, kDifUartLoopbackSystem,
                                      kDifToggleDisabled));

  EXPECT_MASK32(UART_CTRL_REG_OFFSET, {{UART_CTRL_LLPBK_BIT, 0x1, true}});
  EXPECT_DIF_OK(
      dif_uart_loopback_set(&uart_, kDifUartLoopbackLine, kDifToggleEnabled));

  EXPECT_MASK32(UART_CTRL_REG_OFFSET, {{UART_CTRL_LLPBK_BIT, 0x1, false}});
  EXPECT_DIF_OK(
      dif_uart_loopback_set(&uart_, kDifUartLoopbackLine, kDifToggleDisabled));
}

class RxTimeoutTest : public UartTest {};

TEST_F(RxTimeoutTest, NullArgs) {
  EXPECT_DIF_BADARG(dif_uart_enable_rx_timeout(nullptr, 1));
  EXPECT_DIF_BADARG(dif_uart_disable_rx_timeout(nullptr));

  uint32_t value;       // optional
  dif_toggle_t status;  // mandatory
  EXPECT_DIF_BADARG(dif_uart_get_rx_timeout(nullptr, &status, &value));
  EXPECT_DIF_BADARG(dif_uart_get_rx_timeout(&uart_, nullptr, &value));
}

TEST_F(RxTimeoutTest, OutOfRange) {
  // RX timeout value must be in the range [0,0xffffff].
  EXPECT_DIF_BADARG(dif_uart_enable_rx_timeout(&uart_, 0x01000000));
  EXPECT_DIF_BADARG(dif_uart_enable_rx_timeout(&uart_, 0xffffffff));
}

TEST_F(RxTimeoutTest, Enable) {
  // Enable RX timeout and set to 0x123.
  const uint32_t duration = 0x123;
  EXPECT_WRITE32(UART_TIMEOUT_CTRL_REG_OFFSET,
                 {{UART_TIMEOUT_CTRL_VAL_OFFSET, duration},
                  {UART_TIMEOUT_CTRL_EN_BIT, true}});
  EXPECT_DIF_OK(dif_uart_enable_rx_timeout(&uart_, duration));
}

TEST_F(RxTimeoutTest, Disable) {
  // Disable RX timeout.
  EXPECT_WRITE32(
      UART_TIMEOUT_CTRL_REG_OFFSET,
      {{UART_TIMEOUT_CTRL_VAL_OFFSET, 0}, {UART_TIMEOUT_CTRL_EN_BIT, false}});
  EXPECT_DIF_OK(dif_uart_disable_rx_timeout(&uart_));
}

TEST_F(RxTimeoutTest, GetStatusOnly) {
  // Enable RX timeout and set to 0x800000.
  const uint32_t duration = 0x800000;
  EXPECT_WRITE32(UART_TIMEOUT_CTRL_REG_OFFSET,
                 {{UART_TIMEOUT_CTRL_VAL_OFFSET, duration},
                  {UART_TIMEOUT_CTRL_EN_BIT, true}});
  EXPECT_DIF_OK(dif_uart_enable_rx_timeout(&uart_, duration));

  // Read out status only.
  dif_toggle_t status = kDifToggleDisabled;
  EXPECT_READ32(UART_TIMEOUT_CTRL_REG_OFFSET,
                {{UART_TIMEOUT_CTRL_VAL_OFFSET, duration},
                 {UART_TIMEOUT_CTRL_EN_BIT, true}});
  EXPECT_DIF_OK(dif_uart_get_rx_timeout(&uart_, &status, nullptr));
  EXPECT_EQ(status, kDifToggleEnabled);
}

TEST_F(RxTimeoutTest, GetAll) {
  // Enable RX timeout and set to 0xf0f0f0.
  const uint32_t duration = 0xf0f0f0;
  EXPECT_WRITE32(UART_TIMEOUT_CTRL_REG_OFFSET,
                 {{UART_TIMEOUT_CTRL_VAL_OFFSET, duration},
                  {UART_TIMEOUT_CTRL_EN_BIT, true}});
  EXPECT_DIF_OK(dif_uart_enable_rx_timeout(&uart_, duration));

  // Read out duration and status.
  uint32_t out = 0;
  dif_toggle_t status = kDifToggleDisabled;
  EXPECT_READ32(UART_TIMEOUT_CTRL_REG_OFFSET,
                {{UART_TIMEOUT_CTRL_VAL_OFFSET, duration},
                 {UART_TIMEOUT_CTRL_EN_BIT, true}});
  EXPECT_DIF_OK(dif_uart_get_rx_timeout(&uart_, &status, &out));
  EXPECT_EQ(status, kDifToggleEnabled);
  EXPECT_EQ(out, duration);
}

}  // namespace
}  // namespace dif_uart_unittest
