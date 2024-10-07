// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_framework/ottf_console.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/dif/dif_uart.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/print.h"
#include "sw/device/lib/testing/spi_device_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_isrs.h"
#include "sw/device/lib/testing/test_framework/ottf_test_config.h"

#include "devicetables.h"
#include "spi_device_regs.h"  // Generated.

static const dt_rv_plic_t *kRvPlicDt = &kDtRvPlic[0];
static const dt_uart_t *kUart0Dt = &kDtUart[0];

#define MODULE_ID MAKE_MODULE_ID('o', 't', 'c')

/**
 * OTTF console configuration parameters.
 */
enum {
  /**
   * SPI device console configuration parameters.
   */
  kSpiDeviceRxCommitWait = 63,  // clock cycles
  /**
   * Flow control parameters.
   */
  kFlowControlLowWatermark = 4,   // bytes
  kFlowControlHighWatermark = 8,  // bytes
  kFlowControlRxWatermark = kDifUartWatermarkByte8,
  /**
   * HART PLIC Target.
   */
  kPlicTarget = 0,
};

// Potential DIF handles for OTTF console communication.
static dif_spi_device_handle_t ottf_console_spi_device;
static dif_uart_t ottf_console_uart;

// Function pointer to the currently active data sink.
static sink_func_ptr sink;
// Function pointer to a function that retrieves a single character.
static status_t (*getc)(void *);

// The `flow_control_state` and `flow_control_irqs` variables are shared between
// the interrupt service handler and user code.
static volatile ottf_console_flow_control_t flow_control_state;
static volatile uint32_t flow_control_irqs;

void *ottf_console_get(void) {
  switch (kOttfTestConfig.console.type) {
    case kOttfConsoleSpiDevice:
      return &ottf_console_spi_device;
    default:
      return &ottf_console_uart;
  }
}

static status_t uart_getc(void *io) {
  const dif_uart_t *uart = (const dif_uart_t *)io;
  uint8_t byte;
  TRY(dif_uart_byte_receive_polled(uart, &byte));
  TRY(ottf_console_flow_control(uart, kOttfConsoleFlowControlAuto));
  return OK_STATUS(byte);
}

/*
 * The user of this function needs to be aware of the following:
 * 1. The exact amount of data expected to be sent from the host side must be
 * known in advance.
 * 2. Characters should be retrieved from the console as soon as they become
 * available. Failure to do so may result in an SPI transaction timeout.
 */
static status_t spi_device_getc(void *io) {
  static size_t index = 0;
  static upload_info_t info = {0};
  dif_spi_device_handle_t *spi_device = (dif_spi_device_handle_t *)io;
  if (index == info.data_len) {
    memset(&info, 0, sizeof(upload_info_t));
    CHECK_STATUS_OK(spi_device_testutils_wait_for_upload(spi_device, &info));
    index = 0;
    CHECK_DIF_OK(dif_spi_device_set_flash_status_registers(spi_device, 0x00));
  }

  return OK_STATUS(info.data[index++]);
}

static void spi_device_wait_for_sync(dif_spi_device_handle_t *spi_device) {
  const uint8_t kBootMagicPattern[4] = {0x02, 0xb0, 0xfe, 0xca};
  const uint8_t kEmptyPattern[4] = {0};

  for (size_t i = 0; i < SPI_DEVICE_PARAM_SRAM_READ_BUFFER_DEPTH; i++) {
    CHECK_DIF_OK(dif_spi_device_write_flash_buffer(
        spi_device, kDifSpiDeviceFlashBufferTypeEFlash,
        i * ARRAYSIZE(kBootMagicPattern), ARRAYSIZE(kBootMagicPattern),
        kBootMagicPattern));
  }

  upload_info_t info = {0};
  CHECK_STATUS_OK(spi_device_testutils_wait_for_upload(spi_device, &info));
  // Clear the boot magic in the read buffer.
  for (size_t i = 0; i < SPI_DEVICE_PARAM_SRAM_READ_BUFFER_DEPTH; i++) {
    CHECK_DIF_OK(dif_spi_device_write_flash_buffer(
        spi_device, kDifSpiDeviceFlashBufferTypeEFlash,
        i * ARRAYSIZE(kEmptyPattern), ARRAYSIZE(kEmptyPattern), kEmptyPattern));
  }
  CHECK_DIF_OK(dif_spi_device_set_flash_status_registers(spi_device, 0x00));
}

void ottf_console_init(void) {
  // Initialize/Configure the console device.
  uintptr_t base_addr = kOttfTestConfig.console.base_addr;
  switch (kOttfTestConfig.console.type) {
    case kOttfConsoleUart:
      // Set a default for the console base address if the base address is not
      // configured. The default is to use UART0.
      if (base_addr == 0) {
        CHECK(kOttfTestConfig.console.type == kOttfConsoleUart);
        base_addr = dt_uart_reg_block(kUart0Dt, kDtUartRegBlockCore);
      }

      ottf_console_configure_uart(base_addr);
      sink = get_uart_sink();
      getc = uart_getc;
      break;
    case (kOttfConsoleSpiDevice):
      ottf_console_configure_spi_device(base_addr);
      sink = get_spi_device_sink();
      getc = spi_device_getc;
      break;
    default:
      CHECK(false, "unsupported OTTF console interface.");
      break;
  }
}

void ottf_console_configure_uart(uintptr_t base_addr) {
  CHECK_DIF_OK(
      dif_uart_init(mmio_region_from_addr(base_addr), &ottf_console_uart));
  CHECK(kUartBaudrate <= UINT32_MAX, "kUartBaudrate must fit in uint32_t");
  CHECK(kClockFreqPeripheralHz <= UINT32_MAX,
        "kClockFreqPeripheralHz must fit in uint32_t");
  CHECK_DIF_OK(dif_uart_configure(
      &ottf_console_uart, (dif_uart_config_t){
                              .baudrate = (uint32_t)kUartBaudrate,
                              .clk_freq_hz = (uint32_t)kClockFreqPeripheralHz,
                              .parity_enable = kDifToggleDisabled,
                              .parity = kDifUartParityEven,
                              .tx_enable = kDifToggleEnabled,
                              .rx_enable = kDifToggleEnabled,
                          }));
  base_uart_stdout(&ottf_console_uart);

  // Initialize/Configure console flow control (if requested).
  if (kOttfTestConfig.enable_uart_flow_control) {
    ottf_console_flow_control_enable();
  }
}

void ottf_console_configure_spi_device(uintptr_t base_addr) {
  CHECK_DIF_OK(dif_spi_device_init_handle(mmio_region_from_addr(base_addr),
                                          &ottf_console_spi_device));
  CHECK_DIF_OK(dif_spi_device_configure(
      &ottf_console_spi_device,
      (dif_spi_device_config_t){
          .tx_order = kDifSpiDeviceBitOrderMsbToLsb,
          .rx_order = kDifSpiDeviceBitOrderMsbToLsb,
          .device_mode = kDifSpiDeviceModeFlashEmulation,
      }));
  dif_spi_device_flash_command_t read_commands[] = {
      {
          // Slot 0: ReadStatus1
          .opcode = kSpiDeviceFlashOpReadStatus1,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .dummy_cycles = 0,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 1: ReadStatus2
          .opcode = kSpiDeviceFlashOpReadStatus2,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .dummy_cycles = 0,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 2: ReadStatus3
          .opcode = kSpiDeviceFlashOpReadStatus3,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .dummy_cycles = 0,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 3: ReadJedecID
          .opcode = kSpiDeviceFlashOpReadJedec,
          .address_type = kDifSpiDeviceFlashAddrDisabled,
          .dummy_cycles = 0,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 4: ReadSfdp
          .opcode = kSpiDeviceFlashOpReadSfdp,
          .address_type = kDifSpiDeviceFlashAddr3Byte,
          .dummy_cycles = 8,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
      {
          // Slot 5: ReadNormal
          .opcode = kSpiDeviceFlashOpReadNormal,
          .address_type = kDifSpiDeviceFlashAddr3Byte,
          .dummy_cycles = 0,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = true,
      },
  };
  for (size_t i = 0; i < ARRAYSIZE(read_commands); ++i) {
    uint8_t slot = (uint8_t)i + kSpiDeviceReadCommandSlotBase;
    CHECK_DIF_OK(dif_spi_device_set_flash_command_slot(
        &ottf_console_spi_device, slot, kDifToggleEnabled, read_commands[i]));
  }
  dif_spi_device_flash_command_t write_commands[] = {
      {
          // Slot 11: PageProgram
          .opcode = kSpiDeviceFlashOpPageProgram,
          .address_type = kDifSpiDeviceFlashAddrCfg,
          .payload_io_type = kDifSpiDevicePayloadIoSingle,
          .payload_dir_to_host = false,
          .upload = true,
          .set_busy_status = true,
      },
  };
  for (size_t i = 0; i < ARRAYSIZE(write_commands); ++i) {
    uint8_t slot = (uint8_t)i + kSpiDeviceWriteCommandSlotBase;
    CHECK_DIF_OK(dif_spi_device_set_flash_command_slot(
        &ottf_console_spi_device, slot, kDifToggleEnabled, write_commands[i]));
  }
  spi_device_wait_for_sync(&ottf_console_spi_device);
  base_spi_device_stdout(&ottf_console_spi_device);
}

static uint32_t get_flow_control_watermark_plic_id(void) {
  for (size_t i = 0; i < kDtUartCount; i++) {
    if (kOttfTestConfig.console.base_addr == dt_uart_reg_block(&kDtUart[i], kDtUartRegBlockCore)) {
      return dt_uart_irq_to_plic_id(&kDtUart[i], kDtUartIrqRxWatermark);
    }
  }
  return dt_uart_irq_to_plic_id(kUart0Dt, kDtUartIrqRxWatermark);
}

void ottf_console_flow_control_enable(void) {
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kRvPlicDt, &ottf_plic));

  dif_uart_t *uart = (dif_uart_t *)ottf_console_get();
  CHECK_DIF_OK(dif_uart_watermark_rx_set(uart, kFlowControlRxWatermark));
  CHECK_DIF_OK(dif_uart_irq_set_enabled(uart, kDifUartIrqRxWatermark,
                                        kDifToggleEnabled));

  // Set IRQ priorities to MAX
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(
      &ottf_plic, get_flow_control_watermark_plic_id(), kDifRvPlicMaxPriority));
  // Set Ibex IRQ priority threshold level
  CHECK_DIF_OK(dif_rv_plic_target_set_threshold(&ottf_plic, kPlicTarget,
                                                kDifRvPlicMinPriority));
  // Enable IRQs in PLIC
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(&ottf_plic,
                                           get_flow_control_watermark_plic_id(),
                                           kPlicTarget, kDifToggleEnabled));

  flow_control_state = kOttfConsoleFlowControlAuto;
  irq_global_ctrl(true);
  irq_external_ctrl(true);
  // Make sure we're in the Resume state and we emit a Resume to the UART.
  ottf_console_flow_control((dif_uart_t *)ottf_console_get(),
                            kOttfConsoleFlowControlResume);
}

// This version of the function is safe to call from within the ISR.
static status_t manage_flow_control(const dif_uart_t *uart,
                                    ottf_console_flow_control_t ctrl) {
  if (flow_control_state == kOttfConsoleFlowControlNone) {
    return OK_STATUS((int32_t)flow_control_state);
  }
  if (ctrl == kOttfConsoleFlowControlAuto) {
    uint32_t avail;
    TRY(dif_uart_rx_bytes_available(uart, &avail));
    if (avail < kFlowControlLowWatermark &&
        flow_control_state != kOttfConsoleFlowControlResume) {
      // Enable RX watermark interrupt when RX FIFO level is below the
      // watermark.
      CHECK_DIF_OK(dif_uart_irq_set_enabled(uart, kDifUartIrqRxWatermark,
                                            kDifToggleEnabled));
      ctrl = kOttfConsoleFlowControlResume;
    } else if (avail >= kFlowControlHighWatermark &&
               flow_control_state != kOttfConsoleFlowControlPause) {
      ctrl = kOttfConsoleFlowControlPause;
      // RX watermark interrupt is status type, so disable the interrupt whilst
      // RX FIFO is above the watermark to avoid an inifite loop of ISRs.
      CHECK_DIF_OK(dif_uart_irq_set_enabled(uart, kDifUartIrqRxWatermark,
                                            kDifToggleDisabled));
    } else {
      return OK_STATUS((int32_t)flow_control_state);
    }
  }
  uint8_t byte = (uint8_t)ctrl;
  CHECK_DIF_OK(dif_uart_bytes_send(uart, &byte, 1, NULL));
  flow_control_state = ctrl;
  return OK_STATUS((int32_t)flow_control_state);
}

bool ottf_console_flow_control_isr(uint32_t *exc_info) {
  dif_uart_t *uart = (dif_uart_t *)ottf_console_get();
  flow_control_irqs += 1;
  bool rx;
  CHECK_DIF_OK(dif_uart_irq_is_pending(uart, kDifUartIrqRxWatermark, &rx));
  if (rx) {
    manage_flow_control(uart, kOttfConsoleFlowControlAuto);
    CHECK_DIF_OK(dif_uart_irq_acknowledge(uart, kDifUartIrqRxWatermark));
    return true;
  }
  return false;
}

// The public API has to save and restore interrupts to avoid an
// unexpected write to the global `flow_control_state`.
status_t ottf_console_flow_control(const dif_uart_t *uart,
                                   ottf_console_flow_control_t ctrl) {
  dif_uart_irq_enable_snapshot_t snapshot;
  CHECK_DIF_OK(dif_uart_irq_disable_all(uart, &snapshot));
  status_t s = manage_flow_control(uart, ctrl);
  CHECK_DIF_OK(dif_uart_irq_restore_all(uart, &snapshot));
  return s;
}

uint32_t ottf_console_get_flow_control_irqs(void) { return flow_control_irqs; }

static bool spi_tx_last_data_chunk(upload_info_t *info) {
  const static size_t kSpiTxTerminateMagicAddress = 0x100;
  return info->address == kSpiTxTerminateMagicAddress;
}

size_t ottf_console_spi_device_read(size_t buf_size, uint8_t *const buf) {
  size_t received_data_len = 0;
  upload_info_t info;
  memset(&info, 0, sizeof(upload_info_t));
  while (!spi_tx_last_data_chunk(&info)) {
    CHECK_STATUS_OK(
        spi_device_testutils_wait_for_upload(&ottf_console_spi_device, &info));
    if (received_data_len < buf_size) {
      size_t remaining_buf_size = buf_size - received_data_len;
      size_t bytes_to_copy = remaining_buf_size < info.data_len
                                 ? remaining_buf_size
                                 : info.data_len;
      memcpy(buf + received_data_len, info.data, bytes_to_copy);
    }

    received_data_len += info.data_len;
    CHECK_DIF_OK(dif_spi_device_set_flash_status_registers(
        &ottf_console_spi_device, 0x00));
  }

  return received_data_len;
}

status_t ottf_console_putbuf(void *io, const char *buf, size_t len) {
  size_t written_len = sink(io, buf, len);
  if (len != written_len) {
    return DATA_LOSS((int32_t)(len - written_len));
  }
  return OK_STATUS((int32_t)len);
}

status_t ottf_console_getc(void *io) { return getc(io); }
