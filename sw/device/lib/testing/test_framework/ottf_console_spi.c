// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/testing/spi_device_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console.h"

#include "hw/top/spi_device_regs.h"  // Generated.

#define MODULE_ID MAKE_MODULE_ID('o', 'c', 's')

/**
 * SPI console buffer management constants.
 */
enum {
  kSpiDeviceReadBufferSizeBytes =
      SPI_DEVICE_PARAM_SRAM_READ_BUFFER_DEPTH * sizeof(uint32_t),
  kSpiDeviceFrameHeaderSizeBytes = 12,
  kSpiDeviceBufferPreservedSizeBytes = kSpiDeviceFrameHeaderSizeBytes,
  kSpiDeviceMaxFramePayloadSizeBytes = kSpiDeviceReadBufferSizeBytes -
                                       kSpiDeviceFrameHeaderSizeBytes -
                                       kSpiDeviceBufferPreservedSizeBytes - 4,
  kSpiDeviceFrameMagicNumber = 0xa5a5beef,
};

// Staging buffer used by ottf_console.c for the main console when using SPI.
// This buffer MUST NOT be used directly in this file. It is only declared here
// so it's size can use all the SPI device parameters.
static char main_spi_buf[kSpiDeviceMaxFramePayloadSizeBytes];

void *ottf_console_spi_get_main_staging_buffer(size_t *size) {
  *size = sizeof(main_spi_buf);
  return main_spi_buf;
}

// The following variables are only initialized if at least one console
// needs a GPIO.
static dif_gpio_t ottf_console_gpio;
static dif_pinmux_t ottf_console_pinmux;

enum {
  /* Placeholder used to indicate that no TX GPIO indicator is enabled. */
  kOttfSpiNoTxGpio = UINT32_MAX,
};

static status_t spi_device_send_data(dif_spi_device_handle_t *spi_device,
                                     const uint8_t *buf, size_t len,
                                     size_t address) {
  if (len == 0) {
    return OK_STATUS();
  }

  size_t space_to_end_of_buffer = kSpiDeviceReadBufferSizeBytes - address;
  size_t first_part_size =
      space_to_end_of_buffer < len ? space_to_end_of_buffer : len;

  TRY(dif_spi_device_write_flash_buffer(spi_device,
                                        kDifSpiDeviceFlashBufferTypeEFlash,
                                        address, first_part_size, buf));

  // Handle wrap-around.
  if (first_part_size < len) {
    size_t second_part_size = len - first_part_size;
    TRY(dif_spi_device_write_flash_buffer(
        spi_device, kDifSpiDeviceFlashBufferTypeEFlash, 0, second_part_size,
        (uint8_t *)(buf + first_part_size)));
  }

  return OK_STATUS();
}

/**
 * Sends data out of the SPI device.
 *
 * Data is packaged into a frame that is described below.
 * The host side reads the header first, then decides how many words
 * to read from the data section.
 *
 * -----------------------------------------------
 * |      Magic Number     | 4-bytes  |          |
 * -----------------------------------|          |
 * |      Frame Number     | 4-bytes  |  Header  |
 * -----------------------------------|          |
 * |   Data Length (bytes) | 4-bytes  |          |
 * -----------------------------------|----------|
 * |      Data (word aligned)         |          |
 * -----------------------------------|   Data   |
 * |     0xFF Pad Bytes    | <4-bytes |          |
 * -----------------------------------|----------|
 */
static size_t spi_device_send_frame(ottf_console_t *console, const char *buf,
                                    size_t len) {
  dif_spi_device_handle_t *spi_device = &console->data.spi.dif;
  const size_t data_packet_size_bytes = ((len + 3u) & ~3u);
  const size_t frame_size_bytes =
      kSpiDeviceFrameHeaderSizeBytes + data_packet_size_bytes;
  uint8_t frame_header_bytes[kSpiDeviceFrameHeaderSizeBytes];

  static uint32_t next_write_address = 0;

  if (frame_size_bytes >= kSpiDeviceReadBufferSizeBytes) {
    return 0;
  }

  // Add the magic bytes.
  for (size_t i = 0; i < 4; ++i) {
    frame_header_bytes[i] = (kSpiDeviceFrameMagicNumber >> (i * 8)) & 0xff;
  }
  // Add the frame number.
  for (size_t i = 0; i < 4; ++i) {
    frame_header_bytes[i + 4] = (console->data.spi.frame_num >> (i * 8)) & 0xff;
  }
  // Add the data length.
  for (size_t i = 0; i < 4; ++i) {
    frame_header_bytes[i + 8] = (len >> (i * 8)) & 0xff;
  }

  // Wait for enough space to free up in the SPI flash buffer if we are in
  // operating in polling mode.
  if (console->data.spi.tx_ready_gpio == kOttfSpiNoTxGpio) {
    uint32_t available_buffer_size = 0;
    uint32_t last_read_address = 0;
    do {
      if (dif_spi_device_get_last_read_address(spi_device,
                                               &last_read_address) != kDifOk) {
        return 0;
      }

      // If we are not using the GPIO TX-ready indicator pin (which is the
      // default) the host SPI console is constantly polling the spi_device to
      // see if data is available to be read out. In this case, we need to
      // adjust the last read address.
      //
      // Specifically, when the host is continuously reading from the read
      // buffer, it is unaware of whether it is going to find a valid new frame
      // (marked by a magic number in the frame header), an frame header all
      // zeros, or garbage, since it is operating in polling mode. This could
      // result in the reported last_read_address being one header size ahead of
      // the actual address of the last valid frame if all the frames in the
      // read buffer has been consumed by the host. While it's harmless to use
      // the last read address even if the reported value is a frame header
      // ahead, doing so might temporarily underestimate the available buffer
      // size by the size of a frame header (or 12 bytes to be specific).
      //
      // However, if we are using the GPIO TX-ready indicator pin, the host will
      // only ever attempt to read out data if it was signaled to do so by the
      // device. In which case the next write address will always be 0, i.e.,
      // the beginning of the buffer.
      uint32_t adjusted_last_read_address =
          (kSpiDeviceReadBufferSizeBytes + last_read_address -
           kSpiDeviceFrameHeaderSizeBytes) %
          kSpiDeviceReadBufferSizeBytes;

      // Frames are always word aligned, so ensure the last read address is word
      // aligned too.
      uint32_t next_read_address = ((adjusted_last_read_address + 1) & ~3u) %
                                   kSpiDeviceReadBufferSizeBytes;

      // Compute the remaining free space in the SPI flash buffer.
      if (next_read_address > next_write_address) {
        available_buffer_size = next_read_address - next_write_address - 1;
      } else {
        available_buffer_size =
            next_read_address +
            (kSpiDeviceReadBufferSizeBytes - next_write_address) - 1;
      }
    } while ((frame_size_bytes + kSpiDeviceBufferPreservedSizeBytes) >
             available_buffer_size);
  }

  // Send aligned data.
  size_t data_write_address =
      (next_write_address + kSpiDeviceFrameHeaderSizeBytes) %
      kSpiDeviceReadBufferSizeBytes;
  size_t aligned_data_len = len & (~3u);
  if (!status_ok(spi_device_send_data(spi_device, (uint8_t *)buf,
                                      aligned_data_len, data_write_address))) {
    return 0;
  }

  // Send unaligned data.
  if (len != aligned_data_len) {
    uint8_t pad_bytes[4] = {0xff, 0xff, 0xff, 0xff};
    size_t pad_write_address =
        (data_write_address + aligned_data_len) % kSpiDeviceReadBufferSizeBytes;

    for (size_t i = 0; i + aligned_data_len < len; i++) {
      pad_bytes[i] = buf[aligned_data_len + i];
    }
    if (!status_ok(spi_device_send_data(spi_device, pad_bytes, 4,
                                        pad_write_address))) {
      return 0;
    }
  }

  // Send frame header.
  if (!status_ok(spi_device_send_data(spi_device, frame_header_bytes,
                                      kSpiDeviceFrameHeaderSizeBytes,
                                      next_write_address))) {
    return 0;
  }

  // Update the next write address and frame number.
  next_write_address =
      (next_write_address + frame_size_bytes) % kSpiDeviceReadBufferSizeBytes;
  console->data.spi.frame_num++;

  // Block until the host to reads out the frame by toggling the GPIO TX-ready
  // indicator pin to signal to the host to clock out data from the spi_device
  // egress buffer.
  if (console->data.spi.tx_ready_gpio != kOttfSpiNoTxGpio) {
    OT_DISCARD(dif_gpio_write(&ottf_console_gpio,
                              console->data.spi.tx_ready_gpio, true));
    bool cs_state = true;
    bool target_cs_state = false;
    // There will be two bulk transfers that can be synchronized by the
    // chip-select action. First the host will read out the 12-byte frame
    // header, followed by the N-byte payload. Each transfer can be observed by
    // the chip-select toggling low then high. After the first toggle low, when
    // the host begins reading out the frame header, we can deassert the
    // TX-ready pin as the host has already initiated the two SPI transactions.
    for (size_t i = 0; i < 4; ++i) {
      do {
        if (dif_spi_device_get_csb_status(spi_device, &cs_state) != kDifOk) {
          return 0;
        }
      } while (cs_state != target_cs_state);
      if (i == 0) {
        OT_DISCARD(dif_gpio_write(&ottf_console_gpio,
                                  console->data.spi.tx_ready_gpio, false));
      }
      target_cs_state = !target_cs_state;
    }
    next_write_address = 0;
  }

  return len;
}

static void spi_device_write_all_flash_buffers(
    dif_spi_device_handle_t *spi_device, const uint8_t *pattern) {
  for (size_t i = 0; i < SPI_DEVICE_PARAM_SRAM_READ_BUFFER_DEPTH; i++) {
    CHECK_DIF_OK(dif_spi_device_write_flash_buffer(
        spi_device, kDifSpiDeviceFlashBufferTypeEFlash, i * sizeof(uint32_t),
        sizeof(uint32_t), pattern));
  }
}

static void spi_device_clear_flash_buffer(dif_spi_device_handle_t *spi_device) {
  const uint8_t kEmptyPattern[4] = {0};
  spi_device_write_all_flash_buffers(spi_device, kEmptyPattern);
  CHECK_DIF_OK(dif_spi_device_set_flash_status_registers(spi_device, 0x00));
}

static void spi_device_wait_for_sync(dif_spi_device_handle_t *spi_device) {
  // Write the boot synchronization data to the flash buffer.
  const uint8_t kBootMagicPattern[4] = {0x02, 0xb0, 0xfe, 0xca};
  spi_device_write_all_flash_buffers(spi_device, kBootMagicPattern);

  // Wait for host to read out the boot synchronization data.
  upload_info_t info = {0};
  CHECK_STATUS_OK(spi_device_testutils_wait_for_upload(spi_device, &info));

  // Clear the boot magic data in the flash buffer that the host echoed back.
  spi_device_clear_flash_buffer(spi_device);
}

static bool spi_tx_last_data_chunk(upload_info_t *info) {
  const static size_t kSpiTxTerminateMagicAddress = 0x100;
  return info->address == kSpiTxTerminateMagicAddress;
}

size_t ottf_console_spi_device_read(ottf_console_t *console, size_t buf_size,
                                    uint8_t *const buf) {
  CHECK(console->type == kOttfConsoleSpiDevice);

  size_t received_data_len = 0;
  upload_info_t info;
  memset(&info, 0, sizeof(upload_info_t));
  while (!spi_tx_last_data_chunk(&info)) {
    CHECK_STATUS_OK(
        spi_device_testutils_wait_for_upload(&console->data.spi.dif, &info));
    if (received_data_len < buf_size) {
      size_t remaining_buf_size = buf_size - received_data_len;
      size_t bytes_to_copy = remaining_buf_size < info.data_len
                                 ? remaining_buf_size
                                 : info.data_len;
      memcpy(buf + received_data_len, info.data, bytes_to_copy);
    }

    received_data_len += info.data_len;
    CHECK_DIF_OK(dif_spi_device_set_flash_status_registers(
        &console->data.spi.dif, 0x00));
  }

  return received_data_len;
}

static size_t ottf_console_spi_sink(void *io, const char *buf, size_t len) {
  ottf_console_t *console = io;
  size_t write_data_len = 0;

  while (write_data_len < len) {
    size_t payload_len = len - write_data_len;
    if (payload_len > kSpiDeviceMaxFramePayloadSizeBytes) {
      payload_len = kSpiDeviceMaxFramePayloadSizeBytes;
    }
    if (spi_device_send_frame(console, buf + write_data_len, payload_len) ==
        payload_len) {
      write_data_len += payload_len;
    }
  }

  return write_data_len;
}

/*
 * The user of this function needs to be aware of the following:
 * 1. The exact amount of data expected to be sent from the host side must be
 * known in advance.
 * 2. Characters should be retrieved from the console as soon as they become
 * available. Failure to do so may result in an SPI transaction timeout.
 */
static status_t ottf_console_spi_getc(void *io) {
  ottf_console_t *console = io;
  dif_spi_device_handle_t *spi_device = &console->data.spi.dif;
  static size_t index = 0;
  static upload_info_t info = {0};
  if (index == info.data_len) {
    memset(&info, 0, sizeof(upload_info_t));
    CHECK_STATUS_OK(spi_device_testutils_wait_for_upload(spi_device, &info));
    index = 0;
    CHECK_DIF_OK(dif_spi_device_set_flash_status_registers(spi_device, 0x00));
  }

  return OK_STATUS(info.data[index++]);
}

void ottf_console_configure_spi_device(ottf_console_t *console,
                                       uintptr_t base_addr,
                                       bool tx_ready_enable,
                                       uint32_t tx_ready_gpio,
                                       uint32_t tx_ready_mio) {
  console->type = kOttfConsoleSpiDevice;
  dif_spi_device_handle_t *spi_device = &console->data.spi.dif;
  // Configure spi_device SPI flash emulation.
  CHECK_DIF_OK(
      dif_spi_device_init_handle(mmio_region_from_addr(base_addr), spi_device));
  CHECK_DIF_OK(dif_spi_device_configure(
      spi_device, (dif_spi_device_config_t){
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
        spi_device, slot, kDifToggleEnabled, read_commands[i]));
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
        spi_device, slot, kDifToggleEnabled, write_commands[i]));
  }

  console->data.spi.frame_num = 0;

  // Setup TX GPIO if requested.
  if (tx_ready_enable) {
    console->data.spi.tx_ready_gpio = tx_ready_gpio;

    CHECK_DIF_OK(dif_gpio_init_from_dt(kDtGpioFirst, &ottf_console_gpio));
    CHECK_DIF_OK(dif_pinmux_init_from_dt(kDtPinmuxFirst, &ottf_console_pinmux));
    CHECK_DIF_OK(dif_pinmux_mio_select_output(
        &ottf_console_pinmux, tx_ready_mio,
        dt_gpio_periph_io(kDtGpioFirst, kDtGpioPeriphIoGpio0 + tx_ready_gpio)));
    CHECK_DIF_OK(dif_gpio_write(&ottf_console_gpio, tx_ready_gpio, false));
    CHECK_DIF_OK(
        dif_gpio_output_set_enabled(&ottf_console_gpio, tx_ready_gpio, true));
    spi_device_clear_flash_buffer(spi_device);
  } else {
    console->data.spi.tx_ready_gpio = kOttfSpiNoTxGpio;

    spi_device_wait_for_sync(spi_device);
  }

  console->getc = ottf_console_spi_getc;
  console->sink = ottf_console_spi_sink;
}
