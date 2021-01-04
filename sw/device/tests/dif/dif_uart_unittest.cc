// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/dif/dif_uart.h"

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/testing/mock_mmio.h"

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
      .params = {.base_addr = dev().region()},
  };

  // NCO is calculated as NCO = 2^20 * fbaud / fpclk, so the following values
  // should result in NCO of 1. This is the default configuration, which will
  // be used unless the values are overridden.
  dif_uart_config_t config_ = {
      .baudrate = 1,
      .clk_freq_hz = 1048576,
      .parity_enable = kDifUartToggleDisabled,
      .parity = kDifUartParityEven,
  };
};

class InitTest : public UartTest {};

TEST_F(InitTest, NullArgs) {
  EXPECT_EQ(dif_uart_init({.base_addr = dev().region()}, nullptr),
            kDifUartBadArg);
}

class ConfigTest : public UartTest {};

TEST_F(ConfigTest, NullArgs) {
  EXPECT_EQ(dif_uart_configure(nullptr, config_), kDifUartConfigBadArg);
}

TEST_F(ConfigTest, Default) {
  ExpectDeviceReset();

  EXPECT_WRITE32(UART_CTRL_REG_OFFSET, {
                                           {UART_CTRL_TX_BIT, true},
                                           {UART_CTRL_RX_BIT, true},
                                           {UART_CTRL_NCO_OFFSET, 1},
                                       });

  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);

  EXPECT_EQ(dif_uart_configure(&uart_, config_), kDifUartConfigOk);
}

TEST_F(ConfigTest, ParityEven) {
  config_.parity_enable = kDifUartToggleEnabled;
  config_.parity = kDifUartParityEven;

  ExpectDeviceReset();

  EXPECT_WRITE32(UART_CTRL_REG_OFFSET, {
                                           {UART_CTRL_TX_BIT, true},
                                           {UART_CTRL_RX_BIT, true},
                                           {UART_CTRL_PARITY_EN_BIT, true},
                                           {UART_CTRL_NCO_OFFSET, 1},
                                       });

  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);

  EXPECT_EQ(dif_uart_configure(&uart_, config_), kDifUartConfigOk);
}

TEST_F(ConfigTest, ParityOdd) {
  config_.parity_enable = kDifUartToggleEnabled;
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

  EXPECT_EQ(dif_uart_configure(&uart_, config_), kDifUartConfigOk);
}

class WatermarkRxSetTest : public UartTest {};

TEST_F(WatermarkRxSetTest, UartNull) {
  dif_uart_result_t result =
      dif_uart_watermark_rx_set(nullptr, kDifUartWatermarkByte1);
  EXPECT_EQ(result, kDifUartBadArg);
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
  EXPECT_EQ(dif_uart_watermark_rx_set(&uart_, kDifUartWatermarkByte1),
            kDifUartOk);

  EXPECT_MASK32(UART_FIFO_CTRL_REG_OFFSET,
                {
                    {UART_FIFO_CTRL_RXILVL_OFFSET, UART_FIFO_CTRL_RXILVL_MASK,
                     UART_FIFO_CTRL_RXILVL_VALUE_RXLVL30},
                });
  EXPECT_EQ(dif_uart_watermark_rx_set(&uart_, kDifUartWatermarkByte30),
            kDifUartOk);
}

class WatermarkTxSetTest : public UartTest {};

TEST_F(WatermarkTxSetTest, NullArgs) {
  EXPECT_EQ(dif_uart_watermark_tx_set(nullptr, kDifUartWatermarkByte1),
            kDifUartBadArg);
}

TEST_F(WatermarkTxSetTest, InvalidWatermark) {
  EXPECT_EQ(dif_uart_watermark_tx_set(&uart_, kDifUartWatermarkByte30),
            kDifUartError);
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
  EXPECT_EQ(dif_uart_watermark_tx_set(&uart_, kDifUartWatermarkByte1),
            kDifUartOk);

  EXPECT_MASK32(UART_FIFO_CTRL_REG_OFFSET,
                {
                    {UART_FIFO_CTRL_TXILVL_OFFSET, UART_FIFO_CTRL_TXILVL_MASK,
                     UART_FIFO_CTRL_TXILVL_VALUE_TXLVL16},
                });
  EXPECT_EQ(dif_uart_watermark_tx_set(&uart_, kDifUartWatermarkByte16),
            kDifUartOk);
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
            kDifUartBadArg);

  EXPECT_EQ(dif_uart_bytes_send(&uart_, nullptr, 1, nullptr), kDifUartBadArg);

  EXPECT_EQ(dif_uart_bytes_send(nullptr, nullptr, 1, nullptr), kDifUartBadArg);
}

TEST_F(BytesSendTest, TxFifoEmptyBytesWrittenNull) {
  ExpectSendBytes();
  EXPECT_EQ(dif_uart_bytes_send(&uart_, kBytesArray.data(), kBytesArray.size(),
                                nullptr),
            kDifUartOk);
}

TEST_F(BytesSendTest, TxFifoEmpty) {
  ExpectSendBytes();

  size_t bytes_written;
  EXPECT_EQ(dif_uart_bytes_send(&uart_, kBytesArray.data(), kBytesArray.size(),
                                &bytes_written),
            kDifUartOk);
  EXPECT_EQ(bytes_written, kBytesArray.size());
}

TEST_F(BytesSendTest, TxFifoFull) {
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_TXFULL_BIT, true}});

  size_t bytes_written;
  EXPECT_EQ(dif_uart_bytes_send(&uart_, kBytesArray.data(), kBytesArray.size(),
                                &bytes_written),
            kDifUartOk);
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
            kDifUartBadArg);
  EXPECT_THAT(receive_bytes, Each(Eq(0)));

  EXPECT_EQ(dif_uart_bytes_receive(&uart_, 1, nullptr, nullptr),
            kDifUartBadArg);

  EXPECT_EQ(dif_uart_bytes_receive(nullptr, 1, nullptr, nullptr),
            kDifUartBadArg);
}

TEST_F(BytesReceiveTest, RxFifoFullBytesWrittenNull) {
  uint8_t num_bytes = kBytesArray.size();
  ExpectReceiveBytes(num_bytes);

  std::vector<uint8_t> receive_bytes(num_bytes);
  EXPECT_EQ(
      dif_uart_bytes_receive(&uart_, num_bytes, receive_bytes.data(), nullptr),
      kDifUartOk);
  EXPECT_EQ(receive_bytes, kBytesArray);
}

TEST_F(BytesReceiveTest, RxFifoFull) {
  uint8_t num_bytes = kBytesArray.size();
  ExpectReceiveBytes(num_bytes);

  size_t bytes_read;
  std::vector<uint8_t> receive_bytes(num_bytes);
  EXPECT_EQ(dif_uart_bytes_receive(&uart_, num_bytes, receive_bytes.data(),
                                   &bytes_read),
            kDifUartOk);
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
            kDifUartOk);
  EXPECT_EQ(bytes_read, 0);
  EXPECT_THAT(receive_bytes, Each(Eq(0)));
}

class BytesSendPolledTest : public UartTest {};

TEST_F(BytesSendPolledTest, NullArgs) {
  dif_uart_result_t result = dif_uart_byte_send_polled(nullptr, 'X');
  EXPECT_EQ(result, kDifUartBadArg);
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

  EXPECT_EQ(dif_uart_byte_send_polled(&uart_, 'X'), kDifUartOk);
}

class BytesReceivePolledTest : public UartTest {};

TEST_F(BytesReceivePolledTest, NullArgs) {
  uint8_t byte;
  EXPECT_EQ(dif_uart_byte_receive_polled(nullptr, &byte), kDifUartBadArg);

  EXPECT_EQ(dif_uart_byte_receive_polled(&uart_, nullptr), kDifUartBadArg);

  EXPECT_EQ(dif_uart_byte_receive_polled(nullptr, nullptr), kDifUartBadArg);
}

TEST_F(BytesReceivePolledTest, Success) {
  // Busy loop 1 iteration (waiting for RX FIFO to fill up)
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_RXEMPTY_BIT, true}});
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_RXEMPTY_BIT, false}});

  // Set expectations for the byte to be read
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_RXEMPTY_BIT, false}});
  EXPECT_READ32(UART_RDATA_REG_OFFSET, 'X');

  uint8_t byte = 'Y';
  EXPECT_EQ(dif_uart_byte_receive_polled(&uart_, &byte), kDifUartOk);
  EXPECT_EQ(byte, 'X');
}

class IrqStateGetTest : public UartTest {};

TEST_F(IrqStateGetTest, NullArgs) {
  bool state;
  EXPECT_EQ(dif_uart_irq_is_pending(nullptr, kDifUartIrqTxWatermark, &state),
            kDifUartBadArg);

  EXPECT_EQ(dif_uart_irq_is_pending(&uart_, kDifUartIrqTxWatermark, nullptr),
            kDifUartBadArg);

  EXPECT_EQ(dif_uart_irq_is_pending(nullptr, kDifUartIrqTxWatermark, nullptr),
            kDifUartBadArg);
}

TEST_F(IrqStateGetTest, Success) {
  // Get the first IRQ state.
  EXPECT_READ32(UART_INTR_STATE_REG_OFFSET,
                {{UART_INTR_STATE_TX_WATERMARK_BIT, true}});

  bool tx_watermark_state;
  EXPECT_EQ(dif_uart_irq_is_pending(&uart_, kDifUartIrqTxWatermark,
                                    &tx_watermark_state),
            kDifUartOk);
  EXPECT_TRUE(tx_watermark_state);

  // Get the last IRQ state.
  EXPECT_READ32(UART_INTR_STATE_REG_OFFSET,
                {{UART_INTR_STATE_RX_PARITY_ERR_BIT, false}});

  bool rx_parity_error_state;
  EXPECT_EQ(dif_uart_irq_is_pending(&uart_, kDifUartIrqRxParityErr,
                                    &rx_parity_error_state),
            kDifUartOk);
  EXPECT_FALSE(rx_parity_error_state);
}

class IrqStateClearTest : public UartTest {};

TEST_F(IrqStateClearTest, NullArgs) {
  EXPECT_EQ(dif_uart_irq_acknowledge(nullptr, kDifUartIrqTxWatermark),
            kDifUartBadArg);
}

TEST_F(IrqStateClearTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(UART_INTR_STATE_REG_OFFSET,
                 {{UART_INTR_STATE_TX_WATERMARK_BIT, 1}});

  EXPECT_EQ(dif_uart_irq_acknowledge(&uart_, kDifUartIrqTxWatermark),
            kDifUartOk);

  // Clear the last IRQ state.
  EXPECT_WRITE32(UART_INTR_STATE_REG_OFFSET,
                 {{UART_INTR_STATE_RX_PARITY_ERR_BIT, 1}});

  EXPECT_EQ(dif_uart_irq_acknowledge(&uart_, kDifUartIrqRxParityErr),
            kDifUartOk);
}

class IrqsDisableTest : public UartTest {};

TEST_F(IrqsDisableTest, NullArgs) {
  dif_uart_irq_snapshot_t state;
  EXPECT_EQ(dif_uart_irq_disable_all(nullptr, &state), kDifUartBadArg);

  EXPECT_EQ(dif_uart_irq_disable_all(nullptr, nullptr), kDifUartBadArg);
}

TEST_F(IrqsDisableTest, Success) {
  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);

  EXPECT_EQ(dif_uart_irq_disable_all(&uart_, nullptr), kDifUartOk);
}

TEST_F(IrqsDisableTest, AllDisabled) {
  // IRQs disabled
  EXPECT_READ32(UART_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);

  dif_uart_irq_snapshot_t state;
  EXPECT_EQ(dif_uart_irq_disable_all(&uart_, &state), kDifUartOk);
  EXPECT_EQ(state, 0);
}

TEST_F(IrqsDisableTest, AllEnabled) {
  // IRQs enabled
  EXPECT_READ32(UART_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);

  dif_uart_irq_snapshot_t state;
  EXPECT_EQ(dif_uart_irq_disable_all(&uart_, &state), kDifUartOk);
  EXPECT_EQ(state, std::numeric_limits<uint32_t>::max());
}

class IrqsRestoreTest : public UartTest {};

TEST_F(IrqsRestoreTest, NullArgs) {
  dif_uart_irq_snapshot_t state = 0;
  EXPECT_EQ(dif_uart_irq_restore_all(nullptr, &state), kDifUartBadArg);

  EXPECT_EQ(dif_uart_irq_restore_all(&uart_, nullptr), kDifUartBadArg);

  EXPECT_EQ(dif_uart_irq_restore_all(nullptr, nullptr), kDifUartBadArg);
}

TEST_F(IrqsRestoreTest, AllEnabled) {
  dif_uart_irq_snapshot_t state = std::numeric_limits<uint32_t>::max();
  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, state);

  EXPECT_EQ(dif_uart_irq_restore_all(&uart_, &state), kDifUartOk);
}

TEST_F(IrqsRestoreTest, NoneEnabled) {
  dif_uart_irq_snapshot_t state = 0;
  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, state);

  EXPECT_EQ(dif_uart_irq_restore_all(&uart_, &state), kDifUartOk);
}

class IrqEnableTest : public UartTest {};

TEST_F(IrqEnableTest, NullArgs) {
  EXPECT_EQ(dif_uart_irq_set_enabled(nullptr, kDifUartIrqTxWatermark,
                                     kDifUartToggleEnabled),
            kDifUartBadArg);
}

TEST_F(IrqEnableTest, Success) {
  // Enable first IRQ.
  EXPECT_MASK32(UART_INTR_ENABLE_REG_OFFSET,
                {{UART_INTR_ENABLE_TX_WATERMARK_BIT, 0x1, true}});

  EXPECT_EQ(dif_uart_irq_set_enabled(&uart_, kDifUartIrqTxWatermark,
                                     kDifUartToggleEnabled),
            kDifUartOk);

  // Disable last IRQ.
  EXPECT_MASK32(UART_INTR_ENABLE_REG_OFFSET,
                {{UART_INTR_ENABLE_RX_PARITY_ERR_BIT, 0x1, false}});

  EXPECT_EQ(dif_uart_irq_set_enabled(&uart_, kDifUartIrqRxParityErr,
                                     kDifUartToggleDisabled),
            kDifUartOk);
}

class IrqForceTest : public UartTest {};

TEST_F(IrqForceTest, NullArgs) {
  EXPECT_EQ(dif_uart_irq_force(nullptr, kDifUartIrqTxWatermark),
            kDifUartBadArg);
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_WRITE32(UART_INTR_TEST_REG_OFFSET,
                 {{UART_INTR_TEST_TX_WATERMARK_BIT, true}});

  EXPECT_EQ(dif_uart_irq_force(&uart_, kDifUartIrqTxWatermark), kDifUartOk);

  // Force last IRQ.
  EXPECT_WRITE32(UART_INTR_TEST_REG_OFFSET,
                 {{UART_INTR_TEST_RX_PARITY_ERR_BIT, true}});

  EXPECT_EQ(dif_uart_irq_force(&uart_, kDifUartIrqRxParityErr), kDifUartOk);
}

class RxBytesAvailableTest : public UartTest {};

TEST_F(RxBytesAvailableTest, NullArgs) {
  size_t num_bytes;
  EXPECT_EQ(dif_uart_rx_bytes_available(nullptr, &num_bytes), kDifUartBadArg);

  EXPECT_EQ(dif_uart_rx_bytes_available(&uart_, nullptr), kDifUartBadArg);

  EXPECT_EQ(dif_uart_rx_bytes_available(nullptr, nullptr), kDifUartBadArg);
}

TEST_F(RxBytesAvailableTest, FifoFull) {
  // kDifUartFifoSizeBytes bytes available to read.
  EXPECT_READ32(UART_FIFO_STATUS_REG_OFFSET,
                {{UART_FIFO_STATUS_RXLVL_OFFSET, kDifUartFifoSizeBytes}});

  size_t num_bytes;
  EXPECT_EQ(dif_uart_rx_bytes_available(&uart_, &num_bytes), kDifUartOk);
  EXPECT_EQ(num_bytes, kDifUartFifoSizeBytes);
}

TEST_F(RxBytesAvailableTest, FifoEmpty) {
  // 0 bytes available to read.
  EXPECT_READ32(UART_FIFO_STATUS_REG_OFFSET,
                {{UART_FIFO_STATUS_RXLVL_OFFSET, 0}});

  size_t num_bytes;
  EXPECT_EQ(dif_uart_rx_bytes_available(&uart_, &num_bytes), kDifUartOk);
  EXPECT_EQ(num_bytes, 0);
}

class TxBytesAvailableTest : public UartTest {};

TEST_F(TxBytesAvailableTest, NullArgs) {
  size_t num_bytes;
  EXPECT_EQ(dif_uart_tx_bytes_available(nullptr, &num_bytes), kDifUartBadArg);

  EXPECT_EQ(dif_uart_tx_bytes_available(&uart_, nullptr), kDifUartBadArg);

  EXPECT_EQ(dif_uart_tx_bytes_available(nullptr, nullptr), kDifUartBadArg);
}

TEST_F(TxBytesAvailableTest, FifoFull) {
  // 0 bytes available to write.
  EXPECT_READ32(UART_FIFO_STATUS_REG_OFFSET,
                {{UART_FIFO_STATUS_TXLVL_OFFSET, kDifUartFifoSizeBytes}});

  size_t num_bytes;
  EXPECT_EQ(dif_uart_tx_bytes_available(&uart_, &num_bytes), kDifUartOk);
  EXPECT_EQ(num_bytes, 0);
}

TEST_F(TxBytesAvailableTest, FifoEmpty) {
  // kDifUartFifoSizeBytes available to write.
  EXPECT_READ32(UART_FIFO_STATUS_REG_OFFSET,
                {{UART_FIFO_STATUS_TXLVL_OFFSET, 0}});

  size_t num_bytes;
  EXPECT_EQ(dif_uart_tx_bytes_available(&uart_, &num_bytes), kDifUartOk);
  EXPECT_EQ(num_bytes, kDifUartFifoSizeBytes);
}

class FifoResetTest : public UartTest {};

TEST_F(FifoResetTest, NullArgs) {
  dif_uart_result_t result = dif_uart_fifo_reset(nullptr, kDifUartFifoResetRx);
  EXPECT_EQ(result, kDifUartBadArg);
}

TEST_F(FifoResetTest, Success) {
  EXPECT_READ32(UART_FIFO_CTRL_REG_OFFSET, 0);
  EXPECT_WRITE32(UART_FIFO_CTRL_REG_OFFSET, {{UART_FIFO_CTRL_RXRST_BIT, true}});
  EXPECT_EQ(dif_uart_fifo_reset(&uart_, kDifUartFifoResetRx), kDifUartOk);

  EXPECT_READ32(UART_FIFO_CTRL_REG_OFFSET, 0);
  EXPECT_WRITE32(UART_FIFO_CTRL_REG_OFFSET, {{UART_FIFO_CTRL_TXRST_BIT, true}});
  EXPECT_EQ(dif_uart_fifo_reset(&uart_, kDifUartFifoResetTx), kDifUartOk);

  EXPECT_READ32(UART_FIFO_CTRL_REG_OFFSET, 0);
  EXPECT_WRITE32(UART_FIFO_CTRL_REG_OFFSET,
                 {
                     {UART_FIFO_CTRL_RXRST_BIT, true},
                     {UART_FIFO_CTRL_TXRST_BIT, true},
                 });
  EXPECT_EQ(dif_uart_fifo_reset(&uart_, kDifUartFifoResetAll), kDifUartOk);
}

class LoopbackSetTest : public UartTest {};

TEST_F(LoopbackSetTest, NullArgs) {
  EXPECT_EQ(dif_uart_loopback_set(nullptr, kDifUartLoopbackSystem,
                                  kDifUartToggleEnabled),
            kDifUartBadArg);
}

TEST_F(LoopbackSetTest, Success) {
  EXPECT_MASK32(UART_CTRL_REG_OFFSET, {{UART_CTRL_SLPBK_BIT, 0x1, true}});
  EXPECT_EQ(dif_uart_loopback_set(&uart_, kDifUartLoopbackSystem,
                                  kDifUartToggleEnabled),
            kDifUartOk);

  EXPECT_MASK32(UART_CTRL_REG_OFFSET, {{UART_CTRL_SLPBK_BIT, 0x1, false}});
  EXPECT_EQ(dif_uart_loopback_set(&uart_, kDifUartLoopbackSystem,
                                  kDifUartToggleDisabled),
            kDifUartOk);

  EXPECT_MASK32(UART_CTRL_REG_OFFSET, {{UART_CTRL_LLPBK_BIT, 0x1, true}});
  EXPECT_EQ(dif_uart_loopback_set(&uart_, kDifUartLoopbackLine,
                                  kDifUartToggleEnabled),
            kDifUartOk);

  EXPECT_MASK32(UART_CTRL_REG_OFFSET, {{UART_CTRL_LLPBK_BIT, 0x1, false}});
  EXPECT_EQ(dif_uart_loopback_set(&uart_, kDifUartLoopbackLine,
                                  kDifUartToggleDisabled),
            kDifUartOk);
}

class RxTimeoutTest : public UartTest {};

TEST_F(RxTimeoutTest, NullArgs) {
  EXPECT_EQ(dif_uart_enable_rx_timeout(nullptr, 1), kDifUartBadArg);
  EXPECT_EQ(dif_uart_disable_rx_timeout(nullptr), kDifUartBadArg);

  uint32_t value;            // optional
  dif_uart_toggle_t status;  // mandatory
  EXPECT_EQ(dif_uart_get_rx_timeout(nullptr, &status, &value), kDifUartBadArg);
  EXPECT_EQ(dif_uart_get_rx_timeout(&uart_, nullptr, &value), kDifUartBadArg);
}

TEST_F(RxTimeoutTest, OutOfRange) {
  // RX timeout value must be in the range [0,0xffffff].
  EXPECT_EQ(dif_uart_enable_rx_timeout(&uart_, 0x01000000), kDifUartBadArg);
  EXPECT_EQ(dif_uart_enable_rx_timeout(&uart_, 0xffffffff), kDifUartBadArg);
}

TEST_F(RxTimeoutTest, Enable) {
  // Enable RX timeout and set to 0x123.
  const uint32_t duration = 0x123;
  EXPECT_WRITE32(UART_TIMEOUT_CTRL_REG_OFFSET,
                 {{UART_TIMEOUT_CTRL_VAL_OFFSET, duration},
                  {UART_TIMEOUT_CTRL_EN_BIT, true}});
  EXPECT_EQ(dif_uart_enable_rx_timeout(&uart_, duration), kDifUartOk);
}

TEST_F(RxTimeoutTest, Disable) {
  // Disable RX timeout.
  EXPECT_WRITE32(
      UART_TIMEOUT_CTRL_REG_OFFSET,
      {{UART_TIMEOUT_CTRL_VAL_OFFSET, 0}, {UART_TIMEOUT_CTRL_EN_BIT, false}});
  EXPECT_EQ(dif_uart_disable_rx_timeout(&uart_), kDifUartOk);
}

TEST_F(RxTimeoutTest, GetStatusOnly) {
  // Enable RX timeout and set to 0x800000.
  const uint32_t duration = 0x800000;
  EXPECT_WRITE32(UART_TIMEOUT_CTRL_REG_OFFSET,
                 {{UART_TIMEOUT_CTRL_VAL_OFFSET, duration},
                  {UART_TIMEOUT_CTRL_EN_BIT, true}});
  EXPECT_EQ(dif_uart_enable_rx_timeout(&uart_, duration), kDifUartOk);

  // Read out status only.
  dif_uart_toggle_t status = kDifUartToggleDisabled;
  EXPECT_READ32(UART_TIMEOUT_CTRL_REG_OFFSET,
                {{UART_TIMEOUT_CTRL_VAL_OFFSET, duration},
                 {UART_TIMEOUT_CTRL_EN_BIT, true}});
  EXPECT_EQ(dif_uart_get_rx_timeout(&uart_, &status, nullptr), kDifUartOk);
  EXPECT_EQ(status, kDifUartToggleEnabled);
}

TEST_F(RxTimeoutTest, GetAll) {
  // Enable RX timeout and set to 0xf0f0f0.
  const uint32_t duration = 0xf0f0f0;
  EXPECT_WRITE32(UART_TIMEOUT_CTRL_REG_OFFSET,
                 {{UART_TIMEOUT_CTRL_VAL_OFFSET, duration},
                  {UART_TIMEOUT_CTRL_EN_BIT, true}});
  EXPECT_EQ(dif_uart_enable_rx_timeout(&uart_, duration), kDifUartOk);

  // Read out duration and status.
  uint32_t out = 0;
  dif_uart_toggle_t status = kDifUartToggleDisabled;
  EXPECT_READ32(UART_TIMEOUT_CTRL_REG_OFFSET,
                {{UART_TIMEOUT_CTRL_VAL_OFFSET, duration},
                 {UART_TIMEOUT_CTRL_EN_BIT, true}});
  EXPECT_EQ(dif_uart_get_rx_timeout(&uart_, &status, &out), kDifUartOk);
  EXPECT_EQ(status, kDifUartToggleEnabled);
  EXPECT_EQ(out, duration);
}

}  // namespace
}  // namespace dif_uart_unittest
