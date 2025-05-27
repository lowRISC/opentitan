// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/runtime/ibex.h"
#include "sw/device/lib/testing/spi_device_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_console_internal.h"

#include "spi_device_regs.h"  // Generated.

// The GPIO TX indicator pin that can be used with the SPI console.
static dif_gpio_t *spi_console_gpio = NULL;
static dif_gpio_pin_t spi_console_tx_ready_gpio = UINT32_MAX;

static uint32_t spi_device_frame_num = 0;

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
static size_t spi_device_send_frame(void *data, const char *buf, size_t len) {
  dif_spi_device_handle_t *spi_device = (dif_spi_device_handle_t *)data;
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
    frame_header_bytes[i + 4] = (spi_device_frame_num >> (i * 8)) & 0xff;
  }
  // Add the data length.
  for (size_t i = 0; i < 4; ++i) {
    frame_header_bytes[i + 8] = (len >> (i * 8)) & 0xff;
  }

  // Wait for enough space to free up in the SPI flash buffer if we are in
  // operating in polling mode.
  if (spi_console_gpio == NULL) {
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
  spi_device_frame_num++;

  // Block until the host to reads out the frame by toggling the GPIO TX-ready
  // indicator pin to signal to the host to clock out data from the spi_device
  // egress buffer.
  if (spi_console_gpio != NULL) {
    OT_DISCARD(
        dif_gpio_write(spi_console_gpio, spi_console_tx_ready_gpio, true));
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
        OT_DISCARD(
            dif_gpio_write(spi_console_gpio, spi_console_tx_ready_gpio, false));
      }
      target_cs_state = !target_cs_state;
    }
    next_write_address = 0;
  }

  return len;
}

static size_t base_dev_spi_device(void *data, const char *buf, size_t len) {
  size_t write_data_len = 0;

  while (write_data_len < len) {
    size_t payload_len = len - write_data_len;
    if (payload_len > kSpiDeviceMaxFramePayloadSizeBytes) {
      payload_len = kSpiDeviceMaxFramePayloadSizeBytes;
    }
    if (spi_device_send_frame(data, buf + write_data_len, payload_len) ==
        payload_len) {
      write_data_len += payload_len;
    }
  }

  return write_data_len;
}

sink_func_ptr get_spi_device_sink(void) { return &base_dev_spi_device; }

void base_spi_device_set_gpio_tx_indicator(dif_gpio_t *gpio,
                                           dif_gpio_pin_t tx_indicator_pin) {
  spi_console_gpio = gpio;
  spi_console_tx_ready_gpio = tx_indicator_pin;
}

void base_spi_device_stdout(const dif_spi_device_handle_t *spi_device) {
  // Reset the frame counter.
  spi_device_frame_num = 0;
  base_set_stdout((buffer_sink_t){.data = (void *)spi_device,
                                  .sink = &base_dev_spi_device});
}
