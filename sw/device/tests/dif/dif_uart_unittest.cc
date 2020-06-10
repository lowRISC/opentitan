// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "gtest/gtest.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/testing/mock_mmio.h"

extern "C" {
#include "sw/device/lib/dif/dif_uart.h"
#include "uart_regs.h"  // Generated.
}  // extern "C"

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
    EXPECT_WRITE32(UART_FIFO_CTRL_REG_OFFSET, {
                                                  {UART_FIFO_CTRL_RXRST, true},
                                                  {UART_FIFO_CTRL_TXRST, true},
                                              });
    EXPECT_WRITE32(UART_OVRD_REG_OFFSET, 0);
    EXPECT_WRITE32(UART_TIMEOUT_CTRL_REG_OFFSET, 0);
    EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);
    EXPECT_WRITE32(UART_INTR_STATE_REG_OFFSET,
                   std::numeric_limits<uint32_t>::max());
  }

  mmio_region_t base_addr_ = dev().region();
  dif_uart_t dif_uart_ = {
      /* base_addr = */ base_addr_,
  };

  // NCO is calculated as NCO = 2^20 * fbaud / fpclk, so the following values
  // should result in NCO of 1. This is the default configuration, which will
  // be used unless the values are overriden.
  dif_uart_config_t dif_uart_config_ = {
      /* baudrate = */ 1,
      /* clk_freq_hz = */ 1048576,
      /* parity_enable = */ kDifUartDisable,
      /* parity = */ kDifUartParityEven,
  };
};

class InitTest : public UartTest {};

TEST_F(InitTest, NullArgs) {
  dif_uart_config_result_t result = kDifUartConfigOk;
  result = dif_uart_init(base_addr_, &dif_uart_config_, nullptr);
  EXPECT_EQ(result, kDifUartConfigBadArg);

  result = dif_uart_init(base_addr_, nullptr, &dif_uart_);
  EXPECT_EQ(result, kDifUartConfigBadArg);

  result = dif_uart_init(base_addr_, nullptr, nullptr);
  EXPECT_EQ(result, kDifUartConfigBadArg);
}

TEST_F(InitTest, Default) {
  ExpectDeviceReset();

  EXPECT_WRITE32(
      UART_CTRL_REG_OFFSET,
      {
          {UART_CTRL_TX, true}, {UART_CTRL_RX, true}, {UART_CTRL_NCO_OFFSET, 1},
      });

  EXPECT_WRITE32(UART_FIFO_CTRL_REG_OFFSET,
                 {
                     {UART_FIFO_CTRL_RXRST, true}, {UART_FIFO_CTRL_TXRST, true},
                 });

  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);

  dif_uart_config_result_t result =
      dif_uart_init(base_addr_, &dif_uart_config_, &dif_uart_);
  EXPECT_EQ(result, kDifUartConfigOk);
}

TEST_F(InitTest, ParityEven) {
  dif_uart_config_.parity_enable = kDifUartEnable;
  dif_uart_config_.parity = kDifUartParityEven;

  ExpectDeviceReset();

  EXPECT_WRITE32(UART_CTRL_REG_OFFSET, {
                                           {UART_CTRL_TX, true},
                                           {UART_CTRL_RX, true},
                                           {UART_CTRL_PARITY_EN, true},
                                           {UART_CTRL_NCO_OFFSET, 1},
                                       });

  EXPECT_WRITE32(UART_FIFO_CTRL_REG_OFFSET,
                 {
                     {UART_FIFO_CTRL_RXRST, true}, {UART_FIFO_CTRL_TXRST, true},
                 });

  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);

  dif_uart_config_result_t result =
      dif_uart_init(base_addr_, &dif_uart_config_, &dif_uart_);
  EXPECT_EQ(result, kDifUartConfigOk);
}

TEST_F(InitTest, ParityOdd) {
  dif_uart_config_.parity_enable = kDifUartEnable;
  dif_uart_config_.parity = kDifUartParityOdd;

  ExpectDeviceReset();

  EXPECT_WRITE32(UART_CTRL_REG_OFFSET, {
                                           {UART_CTRL_TX, true},
                                           {UART_CTRL_RX, true},
                                           {UART_CTRL_PARITY_EN, true},
                                           {UART_CTRL_PARITY_ODD, true},
                                           {UART_CTRL_NCO_OFFSET, 1},
                                       });

  EXPECT_WRITE32(UART_FIFO_CTRL_REG_OFFSET,
                 {
                     {UART_FIFO_CTRL_RXRST, true}, {UART_FIFO_CTRL_TXRST, true},
                 });

  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);

  dif_uart_config_result_t result =
      dif_uart_init(base_addr_, &dif_uart_config_, &dif_uart_);
  EXPECT_EQ(result, kDifUartConfigOk);
}

class ConfigTest : public UartTest {};

TEST_F(ConfigTest, NullArgs) {
  dif_uart_config_result_t result = kDifUartConfigOk;
  result = dif_uart_configure(nullptr, &dif_uart_config_);
  EXPECT_EQ(result, kDifUartConfigBadArg);

  result = dif_uart_configure(&dif_uart_, nullptr);
  EXPECT_EQ(result, kDifUartConfigBadArg);

  result = dif_uart_configure(nullptr, nullptr);
  EXPECT_EQ(result, kDifUartConfigBadArg);
}

TEST_F(ConfigTest, Default) {
  ExpectDeviceReset();

  EXPECT_WRITE32(
      UART_CTRL_REG_OFFSET,
      {
          {UART_CTRL_TX, true}, {UART_CTRL_RX, true}, {UART_CTRL_NCO_OFFSET, 1},
      });

  EXPECT_WRITE32(UART_FIFO_CTRL_REG_OFFSET,
                 {
                     {UART_FIFO_CTRL_RXRST, true}, {UART_FIFO_CTRL_TXRST, true},
                 });

  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);

  dif_uart_config_result_t result =
      dif_uart_configure(&dif_uart_, &dif_uart_config_);
  EXPECT_EQ(result, kDifUartConfigOk);
}

TEST_F(ConfigTest, ParityEven) {
  ExpectDeviceReset();

  dif_uart_config_.parity_enable = kDifUartEnable;
  dif_uart_config_.parity = kDifUartParityEven;

  EXPECT_WRITE32(UART_CTRL_REG_OFFSET, {
                                           {UART_CTRL_TX, true},
                                           {UART_CTRL_RX, true},
                                           {UART_CTRL_PARITY_EN, true},
                                           {UART_CTRL_NCO_OFFSET, 1},
                                       });

  EXPECT_WRITE32(UART_FIFO_CTRL_REG_OFFSET,
                 {
                     {UART_FIFO_CTRL_RXRST, true}, {UART_FIFO_CTRL_TXRST, true},
                 });

  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);

  dif_uart_config_result_t result =
      dif_uart_configure(&dif_uart_, &dif_uart_config_);
  EXPECT_EQ(result, kDifUartConfigOk);
}

TEST_F(ConfigTest, ParityOdd) {
  ExpectDeviceReset();

  dif_uart_config_.parity_enable = kDifUartEnable;
  dif_uart_config_.parity = kDifUartParityOdd;

  EXPECT_WRITE32(UART_CTRL_REG_OFFSET, {
                                           {UART_CTRL_TX, true},
                                           {UART_CTRL_RX, true},
                                           {UART_CTRL_PARITY_EN, true},
                                           {UART_CTRL_PARITY_ODD, true},
                                           {UART_CTRL_NCO_OFFSET, 1},
                                       });

  EXPECT_WRITE32(UART_FIFO_CTRL_REG_OFFSET,
                 {
                     {UART_FIFO_CTRL_RXRST, true}, {UART_FIFO_CTRL_TXRST, true},
                 });

  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);

  dif_uart_config_result_t result =
      dif_uart_configure(&dif_uart_, &dif_uart_config_);
  EXPECT_EQ(result, kDifUartConfigOk);
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
                     UART_FIFO_CTRL_RXILVL_RXLVL1},
                });

  dif_uart_result_t result =
      dif_uart_watermark_rx_set(&dif_uart_, kDifUartWatermarkByte1);
  EXPECT_EQ(result, kDifUartOk);

  EXPECT_MASK32(UART_FIFO_CTRL_REG_OFFSET,
                {
                    {UART_FIFO_CTRL_RXILVL_OFFSET, UART_FIFO_CTRL_RXILVL_MASK,
                     UART_FIFO_CTRL_RXILVL_RXLVL30},
                });

  result = dif_uart_watermark_rx_set(&dif_uart_, kDifUartWatermarkByte30);
  EXPECT_EQ(result, kDifUartOk);
}

class WatermarkTxSetTest : public UartTest {};

TEST_F(WatermarkTxSetTest, NullArgs) {
  dif_uart_result_t result =
      dif_uart_watermark_tx_set(nullptr, kDifUartWatermarkByte1);
  EXPECT_EQ(result, kDifUartBadArg);
}

TEST_F(WatermarkTxSetTest, InvalidWatermark) {
  dif_uart_result_t result =
      dif_uart_watermark_tx_set(&dif_uart_, kDifUartWatermarkByte30);
  EXPECT_EQ(result, kDifUartError);
}

/**
 * Tests the first and the last TX watermark variants.
 */
TEST_F(WatermarkTxSetTest, Success) {
  EXPECT_MASK32(UART_FIFO_CTRL_REG_OFFSET,
                {
                    {UART_FIFO_CTRL_TXILVL_OFFSET, UART_FIFO_CTRL_TXILVL_MASK,
                     UART_FIFO_CTRL_TXILVL_TXLVL1},
                });

  dif_uart_result_t result =
      dif_uart_watermark_tx_set(&dif_uart_, kDifUartWatermarkByte1);
  EXPECT_EQ(result, kDifUartOk);

  EXPECT_MASK32(UART_FIFO_CTRL_REG_OFFSET,
                {
                    {UART_FIFO_CTRL_TXILVL_OFFSET, UART_FIFO_CTRL_TXILVL_MASK,
                     UART_FIFO_CTRL_TXILVL_TXLVL16},
                });

  result = dif_uart_watermark_tx_set(&dif_uart_, kDifUartWatermarkByte16);
  EXPECT_EQ(result, kDifUartOk);
}

class BytesSendTest : public UartTest {
 protected:
  /**
   * Sets TX bytes expectations.
   *
   * Every sent byte by the "send bytes" routine is expected to result in the
   * STATUS read of 0 (FIFO not full), and write to WDATA.
   */
  void ExpectSendBytes(int num_elements) {
    ASSERT_LE(num_elements, kBytesArray.size());
    for (int i = 0; i < num_elements; ++i) {
      uint32_t value = static_cast<uint32_t>(kBytesArray[i]);
      EXPECT_READ32(UART_STATUS_REG_OFFSET, 0);
      EXPECT_WRITE32(UART_WDATA_REG_OFFSET, value);
    }
  }
};

TEST_F(BytesSendTest, NullArgs) {
  dif_uart_result_t result =
      dif_uart_bytes_send(nullptr, kBytesArray.data(), 1, nullptr);
  EXPECT_EQ(result, kDifUartBadArg);

  result = dif_uart_bytes_send(&dif_uart_, nullptr, 1, nullptr);
  EXPECT_EQ(result, kDifUartBadArg);

  result = dif_uart_bytes_send(nullptr, nullptr, 1, nullptr);
  EXPECT_EQ(result, kDifUartBadArg);
}

TEST_F(BytesSendTest, TxFifoEmptyBytesWrittenNull) {
  uint8_t num_bytes = kBytesArray.size();
  ExpectSendBytes(num_bytes);

  dif_uart_result_t result =
      dif_uart_bytes_send(&dif_uart_, kBytesArray.data(), num_bytes, nullptr);
  EXPECT_EQ(result, kDifUartOk);
}

TEST_F(BytesSendTest, TxFifoEmpty) {
  uint8_t num_bytes = kBytesArray.size();
  ExpectSendBytes(num_bytes);

  size_t bytes_written = 0;
  dif_uart_result_t result = dif_uart_bytes_send(&dif_uart_, kBytesArray.data(),
                                                 num_bytes, &bytes_written);
  EXPECT_EQ(result, kDifUartOk);
  EXPECT_EQ(bytes_written, num_bytes);
}

TEST_F(BytesSendTest, TxFifoFull) {
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_TXFULL, true}});

  uint8_t num_bytes = kBytesArray.size();
  size_t bytes_written = std::numeric_limits<size_t>::max();
  dif_uart_result_t result = dif_uart_bytes_send(&dif_uart_, kBytesArray.data(),
                                                 num_bytes, &bytes_written);
  EXPECT_EQ(result, kDifUartOk);
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

  dif_uart_result_t result =
      dif_uart_bytes_receive(nullptr, 1, receive_bytes.data(), nullptr);
  EXPECT_EQ(result, kDifUartBadArg);
  EXPECT_THAT(receive_bytes, Each(Eq(0)));

  result = dif_uart_bytes_receive(&dif_uart_, 1, nullptr, nullptr);
  EXPECT_EQ(result, kDifUartBadArg);

  result = dif_uart_bytes_receive(nullptr, 1, nullptr, nullptr);
  EXPECT_EQ(result, kDifUartBadArg);
}

TEST_F(BytesReceiveTest, RxFifoFullBytesWrittenNull) {
  uint8_t num_bytes = kBytesArray.size();
  ExpectReceiveBytes(num_bytes);

  std::vector<uint8_t> receive_bytes(num_bytes);
  dif_uart_result_t result = dif_uart_bytes_receive(
      &dif_uart_, num_bytes, receive_bytes.data(), nullptr);
  EXPECT_EQ(result, kDifUartOk);
  EXPECT_EQ(kBytesArray, receive_bytes);
}

TEST_F(BytesReceiveTest, RxFifoFull) {
  uint8_t num_bytes = kBytesArray.size();
  ExpectReceiveBytes(num_bytes);

  size_t bytes_read = 0;
  std::vector<uint8_t> receive_bytes(num_bytes);
  dif_uart_result_t result = dif_uart_bytes_receive(
      &dif_uart_, num_bytes, receive_bytes.data(), &bytes_read);
  EXPECT_EQ(result, kDifUartOk);
  EXPECT_EQ(bytes_read, num_bytes);
  EXPECT_EQ(kBytesArray, receive_bytes);
}

TEST_F(BytesReceiveTest, RxFifoEmpty) {
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_RXEMPTY, true}});

  uint8_t num_bytes = kBytesArray.size();
  size_t bytes_read = std::numeric_limits<size_t>::max();
  std::vector<uint8_t> receive_bytes(num_bytes);
  dif_uart_result_t result = dif_uart_bytes_receive(
      &dif_uart_, num_bytes, receive_bytes.data(), &bytes_read);
  EXPECT_EQ(result, kDifUartOk);
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
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_TXFULL, true}});
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_TXFULL, false}});

  // Set expectations for the byte to be set
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_TXFULL, false}});
  EXPECT_WRITE32(UART_WDATA_REG_OFFSET, 'X');

  // Busy loop 1 iteration (waiting for the byte to be sent out by the HW)
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_TXIDLE, false}});
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_TXIDLE, true}});

  dif_uart_result_t result = dif_uart_byte_send_polled(&dif_uart_, 'X');
  EXPECT_EQ(result, kDifUartOk);
}

class BytesReceivePolledTest : public UartTest {};

TEST_F(BytesReceivePolledTest, NullArgs) {
  uint8_t byte;
  dif_uart_result_t result = dif_uart_byte_receive_polled(nullptr, &byte);
  EXPECT_EQ(result, kDifUartBadArg);

  result = dif_uart_byte_receive_polled(&dif_uart_, nullptr);
  EXPECT_EQ(result, kDifUartBadArg);

  result = dif_uart_byte_receive_polled(nullptr, nullptr);
  EXPECT_EQ(result, kDifUartBadArg);
}

TEST_F(BytesReceivePolledTest, Success) {
  // Busy loop 1 iteration (waiting for RX FIFO to fill up)
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_RXEMPTY, true}});
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_RXEMPTY, false}});

  // Set expectations for the byte to be read
  EXPECT_READ32(UART_STATUS_REG_OFFSET, {{UART_STATUS_RXEMPTY, false}});
  EXPECT_READ32(UART_RDATA_REG_OFFSET, 'X');

  uint8_t byte = 'Y';
  dif_uart_result_t result = dif_uart_byte_receive_polled(&dif_uart_, &byte);
  EXPECT_EQ(result, kDifUartOk);
  EXPECT_EQ('X', byte);
}

class IrqStateGetTest : public UartTest {};

TEST_F(IrqStateGetTest, NullArgs) {
  dif_uart_enable_t state;
  dif_uart_result_t result =
      dif_uart_irq_state_get(nullptr, kDifUartInterruptTxWatermark, &state);
  EXPECT_EQ(result, kDifUartBadArg);

  result =
      dif_uart_irq_state_get(&dif_uart_, kDifUartInterruptTxWatermark, nullptr);
  EXPECT_EQ(result, kDifUartBadArg);

  result =
      dif_uart_irq_state_get(nullptr, kDifUartInterruptTxWatermark, nullptr);
  EXPECT_EQ(result, kDifUartBadArg);
}

TEST_F(IrqStateGetTest, Success) {
  // Get the first IRQ state.
  EXPECT_READ32(UART_INTR_STATE_REG_OFFSET,
                {{UART_INTR_STATE_TX_WATERMARK, true}});

  dif_uart_enable_t tx_watermark_state = kDifUartDisable;
  dif_uart_result_t result = dif_uart_irq_state_get(
      &dif_uart_, kDifUartInterruptTxWatermark, &tx_watermark_state);
  EXPECT_EQ(result, kDifUartOk);
  EXPECT_EQ(tx_watermark_state, kDifUartEnable);

  // Get the last IRQ state.
  EXPECT_READ32(UART_INTR_STATE_REG_OFFSET,
                {{UART_INTR_STATE_RX_PARITY_ERR, false}});

  dif_uart_enable_t rx_parity_error_state = kDifUartEnable;
  result = dif_uart_irq_state_get(&dif_uart_, kDifUartInterruptRxParityErr,
                                  &rx_parity_error_state);
  EXPECT_EQ(result, kDifUartOk);
  EXPECT_EQ(rx_parity_error_state, kDifUartDisable);
}

class IrqStateClearTest : public UartTest {};

TEST_F(IrqStateClearTest, NullArgs) {
  dif_uart_result_t result =
      dif_uart_irq_state_clear(nullptr, kDifUartInterruptTxWatermark);
  EXPECT_EQ(result, kDifUartBadArg);
}

TEST_F(IrqStateClearTest, Success) {
  // Clear the first IRQ state.
  EXPECT_WRITE32(UART_INTR_STATE_REG_OFFSET,
                 {{UART_INTR_STATE_TX_WATERMARK, 1}});

  dif_uart_result_t result =
      dif_uart_irq_state_clear(&dif_uart_, kDifUartInterruptTxWatermark);
  EXPECT_EQ(result, kDifUartOk);

  // Clear the last IRQ state.
  EXPECT_WRITE32(UART_INTR_STATE_REG_OFFSET,
                 {{UART_INTR_STATE_RX_PARITY_ERR, 1}});

  result = dif_uart_irq_state_clear(&dif_uart_, kDifUartInterruptRxParityErr);
  EXPECT_EQ(result, kDifUartOk);
}

class IrqsDisableTest : public UartTest {};

TEST_F(IrqsDisableTest, NullArgs) {
  uint32_t state;
  dif_uart_result_t result = dif_uart_irqs_disable(nullptr, &state);
  EXPECT_EQ(result, kDifUartBadArg);

  result = dif_uart_irqs_disable(nullptr, nullptr);
  EXPECT_EQ(result, kDifUartBadArg);
}

TEST_F(IrqsDisableTest, Success) {
  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);

  dif_uart_result_t result = dif_uart_irqs_disable(&dif_uart_, nullptr);
  EXPECT_EQ(result, kDifUartOk);
}

TEST_F(IrqsDisableTest, AllDisabled) {
  // IRQs disabled
  EXPECT_READ32(UART_INTR_ENABLE_REG_OFFSET, 0);
  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);

  uint32_t state = std::numeric_limits<uint32_t>::max();
  dif_uart_result_t result = dif_uart_irqs_disable(&dif_uart_, &state);
  EXPECT_EQ(result, kDifUartOk);
  EXPECT_EQ(state, 0);
}

TEST_F(IrqsDisableTest, AllEnabled) {
  // IRQs enabled
  EXPECT_READ32(UART_INTR_ENABLE_REG_OFFSET,
                std::numeric_limits<uint32_t>::max());
  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, 0);

  uint32_t state = 0;
  dif_uart_result_t result = dif_uart_irqs_disable(&dif_uart_, &state);
  EXPECT_EQ(result, kDifUartOk);
  EXPECT_EQ(state, std::numeric_limits<uint32_t>::max());
}

class IrqsRestoreTest : public UartTest {};

TEST_F(IrqsRestoreTest, NullArgs) {
  dif_uart_result_t result =
      dif_uart_irqs_restore(nullptr, std::numeric_limits<uint32_t>::max());
  EXPECT_EQ(result, kDifUartBadArg);
}

TEST_F(IrqsRestoreTest, AllEnabled) {
  uint32_t state = std::numeric_limits<uint32_t>::max();
  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, state);

  dif_uart_result_t result = dif_uart_irqs_restore(&dif_uart_, state);
  EXPECT_EQ(result, kDifUartOk);
}

TEST_F(IrqsRestoreTest, NoneEnabled) {
  uint32_t state = 0;
  EXPECT_WRITE32(UART_INTR_ENABLE_REG_OFFSET, state);

  dif_uart_result_t result = dif_uart_irqs_restore(&dif_uart_, state);
  EXPECT_EQ(result, kDifUartOk);
}

class IrqEnableTest : public UartTest {};

TEST_F(IrqEnableTest, NullArgs) {
  dif_uart_result_t result = dif_uart_irq_enable(
      nullptr, kDifUartInterruptTxWatermark, kDifUartEnable);
  EXPECT_EQ(result, kDifUartBadArg);
}

TEST_F(IrqEnableTest, Success) {
  // Enable first IRQ.
  EXPECT_MASK32(UART_INTR_ENABLE_REG_OFFSET,
                {{UART_INTR_ENABLE_TX_WATERMARK, 0x1, true}});

  dif_uart_result_t result = dif_uart_irq_enable(
      &dif_uart_, kDifUartInterruptTxWatermark, kDifUartEnable);
  EXPECT_EQ(result, kDifUartOk);

  // Disable last IRQ.
  EXPECT_MASK32(UART_INTR_ENABLE_REG_OFFSET,
                {{UART_INTR_STATE_RX_PARITY_ERR, 0x1, false}});

  result = dif_uart_irq_enable(&dif_uart_, kDifUartInterruptRxParityErr,
                               kDifUartDisable);
  EXPECT_EQ(result, kDifUartOk);
}

class IrqForceTest : public UartTest {};

TEST_F(IrqForceTest, NullArgs) {
  dif_uart_result_t result =
      dif_uart_irq_force(nullptr, kDifUartInterruptTxWatermark);
  EXPECT_EQ(result, kDifUartBadArg);
}

TEST_F(IrqForceTest, Success) {
  // Force first IRQ.
  EXPECT_MASK32(UART_INTR_TEST_REG_OFFSET,
                {{UART_INTR_TEST_TX_WATERMARK, 0x1, true}});

  dif_uart_result_t result =
      dif_uart_irq_force(&dif_uart_, kDifUartInterruptTxWatermark);
  EXPECT_EQ(result, kDifUartOk);

  // Force last IRQ.
  EXPECT_MASK32(UART_INTR_TEST_REG_OFFSET,
                {{UART_INTR_ENABLE_RX_PARITY_ERR, 0x1, true}});

  result = dif_uart_irq_force(&dif_uart_, kDifUartInterruptRxParityErr);
  EXPECT_EQ(result, kDifUartOk);
}

class RxBytesAvailableTest : public UartTest {};

TEST_F(RxBytesAvailableTest, NullArgs) {
  size_t num_bytes;
  dif_uart_result_t result = dif_uart_rx_bytes_available(nullptr, &num_bytes);
  EXPECT_EQ(result, kDifUartBadArg);

  result = dif_uart_rx_bytes_available(&dif_uart_, nullptr);
  EXPECT_EQ(result, kDifUartBadArg);

  result = dif_uart_rx_bytes_available(nullptr, nullptr);
  EXPECT_EQ(result, kDifUartBadArg);
}

TEST_F(RxBytesAvailableTest, FifoFull) {
  // kDifUartFifoSizeBytes bytes available to read.
  EXPECT_READ32(UART_FIFO_STATUS_REG_OFFSET,
                {{UART_FIFO_STATUS_RXLVL_OFFSET, kDifUartFifoSizeBytes}});

  size_t num_bytes = 0;
  dif_uart_result_t result =
      dif_uart_rx_bytes_available(&dif_uart_, &num_bytes);
  EXPECT_EQ(result, kDifUartOk);
  EXPECT_EQ(num_bytes, kDifUartFifoSizeBytes);
}

TEST_F(RxBytesAvailableTest, FifoEmpty) {
  // 0 bytes available to read.
  EXPECT_READ32(UART_FIFO_STATUS_REG_OFFSET,
                {{UART_FIFO_STATUS_RXLVL_OFFSET, 0}});

  size_t num_bytes = kDifUartFifoSizeBytes;
  dif_uart_result_t result =
      dif_uart_rx_bytes_available(&dif_uart_, &num_bytes);
  EXPECT_EQ(result, kDifUartOk);
  EXPECT_EQ(num_bytes, 0);
}

class TxBytesAvailableTest : public UartTest {};

TEST_F(TxBytesAvailableTest, NullArgs) {
  size_t num_bytes;
  dif_uart_result_t result = dif_uart_tx_bytes_available(nullptr, &num_bytes);
  EXPECT_EQ(result, kDifUartBadArg);

  result = dif_uart_tx_bytes_available(&dif_uart_, nullptr);
  EXPECT_EQ(result, kDifUartBadArg);

  result = dif_uart_tx_bytes_available(nullptr, nullptr);
  EXPECT_EQ(result, kDifUartBadArg);
}

TEST_F(TxBytesAvailableTest, FifoFull) {
  // 0 bytes available to write.
  EXPECT_READ32(UART_FIFO_STATUS_REG_OFFSET,
                {{UART_FIFO_STATUS_TXLVL_OFFSET, kDifUartFifoSizeBytes}});

  size_t num_bytes = kDifUartFifoSizeBytes;
  dif_uart_result_t result =
      dif_uart_tx_bytes_available(&dif_uart_, &num_bytes);
  EXPECT_EQ(result, kDifUartOk);
  EXPECT_EQ(num_bytes, 0);
}

TEST_F(TxBytesAvailableTest, FifoEmpty) {
  // kDifUartFifoSizeBytes available to write.
  EXPECT_READ32(UART_FIFO_STATUS_REG_OFFSET,
                {{UART_FIFO_STATUS_TXLVL_OFFSET, 0}});

  size_t num_bytes = 0;
  dif_uart_result_t result =
      dif_uart_tx_bytes_available(&dif_uart_, &num_bytes);
  EXPECT_EQ(result, kDifUartOk);
  EXPECT_EQ(num_bytes, kDifUartFifoSizeBytes);
}

}  // namespace
}  // namespace dif_uart_unittest
