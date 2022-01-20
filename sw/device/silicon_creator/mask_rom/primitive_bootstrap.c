// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/mask_rom/primitive_bootstrap.h"

#include <stddef.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/flash_ctrl.h"
#include "sw/device/lib/testing/test_rom/spiflash_frame.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/log.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define GPIO_BOOTSTRAP_BIT_MASK 0x00020000u

static dif_spi_device_t spi;
static dif_spi_device_config_t spi_config;

static rom_error_t spi_device_init(void) {
  if (dif_spi_device_init(
          mmio_region_from_addr(TOP_EARLGREY_SPI_DEVICE_BASE_ADDR), &spi) !=
      kDifOk) {
    return kErrorBootstrapSpiDevice;
  }

  spi_config.clock_polarity = kDifSpiDeviceEdgePositive;
  spi_config.data_phase = kDifSpiDeviceEdgeNegative;
  spi_config.tx_order = kDifSpiDeviceBitOrderMsbToLsb;
  spi_config.rx_order = kDifSpiDeviceBitOrderMsbToLsb;
  spi_config.rx_fifo_timeout = 63;
  spi_config.rx_fifo_len = kDifSpiDeviceBufferLen / 2;
  spi_config.tx_fifo_len = kDifSpiDeviceBufferLen / 2;

  if (dif_spi_device_configure(&spi, &spi_config) != kDifOk) {
    return kErrorBootstrapSpiDevice;
  }
  return kErrorOk;
}

static rom_error_t spi_device_rx_pending(size_t *bytes_available) {
  if (dif_spi_device_rx_pending(&spi, &spi_config, bytes_available) != kDifOk) {
    return kErrorBootstrapSpiDevice;
  }
  return kErrorOk;
}

static rom_error_t spi_device_recv(void *buf, size_t buf_len) {
  if (dif_spi_device_recv(&spi, &spi_config, buf, buf_len,
                          /*bytes_received=*/NULL) != kDifOk) {
    return kErrorBootstrapSpiDevice;
  }
  return kErrorOk;
}

static rom_error_t spi_device_send(const void *buf, size_t buf_len) {
  if (dif_spi_device_send(&spi, &spi_config, buf, buf_len,
                          /*bytes_received=*/NULL) != kDifOk) {
    return kErrorBootstrapSpiDevice;
  }
  return kErrorOk;
}

/**
 * Check if flash is blank to determine if bootstrap is needed.
 */
static rom_error_t bootstrap_requested(bool *result) {
  // Initialize GPIO device.
  dif_gpio_t gpio;
  if (dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR),
                    &gpio) != kDifOk) {
    return kErrorBootstrapGpio;
  }

  dif_gpio_state_t gpio_in;
  if (dif_gpio_read_all(&gpio, &gpio_in) != kDifOk) {
    return kErrorBootstrapGpio;
  }
  *result = (gpio_in & GPIO_BOOTSTRAP_BIT_MASK) != 0;
  return kErrorOk;
}

/**
 * Erase all flash, and verify blank.
 */
static rom_error_t erase_flash(void) {
  if (flash_bank_erase(FLASH_BANK_0) != 0) {
    return kErrorBootstrapErase;
  }
  if (flash_bank_erase(FLASH_BANK_1) != 0) {
    return kErrorBootstrapErase;
  }
  if (flash_check_empty() == 0) {
    return kErrorBootstrapEraseCheck;
  }
  return kErrorOk;
}

/**
 * Computes the SHA256 of the given data.
 */
static void compute_sha256(const void *data, size_t len,
                           hmac_digest_t *digest) {
  hmac_sha256_init();
  hmac_sha256_update(data, len);
  hmac_sha256_final(digest);
}

/**
 * Compares the SHA256 hash of the received data with the received hash.
 *
 * Returns true if the hashes match.
 */
static bool check_frame_hash(const spiflash_frame_t *frame) {
  hmac_digest_t digest;
  size_t digest_len = sizeof(digest.digest);

  uint8_t *data = ((uint8_t *)frame) + digest_len;

  compute_sha256(data, sizeof(spiflash_frame_t) - digest_len, &digest);
  return memcmp(digest.digest, frame->header.hash.digest, digest_len) == 0;
}

/**
 * Load spiflash frames from the SPI interface.
 *
 * This function checks that the sequence numbers and hashes of the frames are
 * correct before programming them into flash.
 */
static rom_error_t bootstrap_flash(void) {
  hmac_digest_t ack = {0};
  uint32_t expected_frame_num = 0;
  while (true) {
    size_t bytes_available;
    RETURN_IF_ERROR(spi_device_rx_pending(&bytes_available));
    if (bytes_available >= sizeof(spiflash_frame_t)) {
      spiflash_frame_t frame;
      RETURN_IF_ERROR(spi_device_recv(&frame, sizeof(spiflash_frame_t)));
      uint32_t frame_num = SPIFLASH_FRAME_NUM(frame.header.frame_num);

      if (frame_num == expected_frame_num) {
        if (!check_frame_hash(&frame)) {
          log_printf("Detected hash mismatch on frame 0x%x\n\r",
                     (unsigned int)frame_num);
          RETURN_IF_ERROR(
              spi_device_send((uint8_t *)&ack.digest, sizeof(ack.digest)));
          continue;
        }

        compute_sha256(&frame, sizeof(spiflash_frame_t), &ack);
        RETURN_IF_ERROR(
            spi_device_send((uint8_t *)&ack.digest, sizeof(ack.digest)));

        if (expected_frame_num == 0) {
          flash_default_region_access(/*rd_en=*/true, /*prog_en=*/true,
                                      /*erase_en=*/true);
          RETURN_IF_ERROR(erase_flash());
        }

        if (flash_write(frame.header.flash_offset, kDataPartition, frame.data,
                        SPIFLASH_FRAME_DATA_WORDS) != 0) {
          return kErrorBootstrapWrite;
        }

        ++expected_frame_num;
        if (SPIFLASH_FRAME_IS_EOF(frame.header.frame_num)) {
          log_printf("Bootstrap: DONE!\n\r");
          return kErrorOk;
        }
      } else {
        // Send previous ack if unable to verify current frame.
        RETURN_IF_ERROR(
            spi_device_send((uint8_t *)&ack.digest, sizeof(ack.digest)));
      }
    }
  }
  return kErrorBootstrapUnknown;
}

rom_error_t primitive_bootstrap(void) {
  bool bootstrap_request_pending = false;
  RETURN_IF_ERROR(bootstrap_requested(&bootstrap_request_pending));
  if (!bootstrap_request_pending) {
    return kErrorOk;
  }

  log_printf("Bootstrap: BEGIN\n\r");

  flash_init_block();
  RETURN_IF_ERROR(spi_device_init());

  rom_error_t error = bootstrap_flash();
  if (error != kErrorOk) {
    if (erase_flash() != kErrorOk) {
      return kErrorBootstrapEraseExit;
    }
    return error;
  }

  // Always make sure to revert flash_ctrl access to default settings.
  // bootstrap_flash enables access to flash to perform update.
  flash_default_region_access(/*rd_en=*/false, /*prog_en=*/false,
                              /*erase_en=*/false);
  return error;
}
