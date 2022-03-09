// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/mask_rom/primitive_bootstrap.h"

#include <stddef.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/test_rom/spiflash_frame.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/watchdog.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/rom_print.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define GPIO_BOOTSTRAP_BIT_MASK 0x00020000u

static dif_flash_ctrl_state_t flash_ctrl;
static dif_spi_device_handle_t spi;

static rom_error_t spi_device_init(void) {
  if (dif_spi_device_init_handle(
          mmio_region_from_addr(TOP_EARLGREY_SPI_DEVICE_BASE_ADDR), &spi) !=
      kDifOk) {
    return kErrorBootstrapSpiDevice;
  }

  dif_spi_device_config_t spi_config = {
      .clock_polarity = kDifSpiDeviceEdgePositive,
      .data_phase = kDifSpiDeviceEdgeNegative,
      .tx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .rx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .device_mode = kDifSpiDeviceModeGeneric,
      .mode_cfg =
          {
              .generic =
                  {
                      .rx_fifo_commit_wait = 63,
                      .rx_fifo_len = kDifSpiDeviceBufferLen / 2,
                      .tx_fifo_len = kDifSpiDeviceBufferLen / 2,
                  },
          },
  };

  if (dif_spi_device_configure(&spi, spi_config) != kDifOk) {
    return kErrorBootstrapSpiDevice;
  }
  return kErrorOk;
}

static rom_error_t spi_device_rx_pending(size_t *bytes_available) {
  if (dif_spi_device_rx_pending(&spi, bytes_available) != kDifOk) {
    return kErrorBootstrapSpiDevice;
  }
  return kErrorOk;
}

static rom_error_t spi_device_recv(void *buf, size_t buf_len) {
  if (dif_spi_device_recv(&spi, buf, buf_len,
                          /*bytes_received=*/NULL) != kDifOk) {
    return kErrorBootstrapSpiDevice;
  }
  return kErrorOk;
}

static rom_error_t spi_device_send(const void *buf, size_t buf_len) {
  if (dif_spi_device_send(&spi, buf, buf_len,
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
 * Check that flash data partitions are all blank.
 */
static bool flash_is_empty(void) {
  dif_flash_ctrl_device_info_t flash_info = dif_flash_ctrl_get_device_info();
  const uint32_t flash_size_bytes =
      flash_info.num_banks * flash_info.bytes_per_page * flash_info.data_pages;
  uint32_t *const limit =
      (uint32_t *)(TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR + flash_size_bytes);
  uint32_t mask = -1u;
  uint32_t *p = (uint32_t *)TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR;
  for (; p < limit;) {
    mask &= *p++;
    mask &= *p++;
    mask &= *p++;
    mask &= *p++;
    mask &= *p++;
    mask &= *p++;
    mask &= *p++;
    mask &= *p++;
    if (mask != -1u) {
      return false;
    }
  }
  return true;
}

/**
 * Erase all flash, and verify blank.
 */
static int erase_flash(void) {
  if (flash_ctrl_testutils_bank_erase(&flash_ctrl, /*bank=*/0,
                                      /*data_only=*/true)) {
    return kErrorBootstrapErase;
  }
  if (flash_ctrl_testutils_bank_erase(&flash_ctrl, /*bank=*/1,
                                      /*data_only=*/true)) {
    return kErrorBootstrapErase;
  }
  if (!flash_is_empty()) {
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
          rom_printf("Detected hash mismatch on frame 0x%x\n\r",
                     (unsigned int)frame_num);
          RETURN_IF_ERROR(
              spi_device_send((uint8_t *)&ack.digest, sizeof(ack.digest)));
          continue;
        }

        compute_sha256(&frame, sizeof(spiflash_frame_t), &ack);
        RETURN_IF_ERROR(
            spi_device_send((uint8_t *)&ack.digest, sizeof(ack.digest)));

        if (expected_frame_num == 0) {
          flash_ctrl_testutils_default_region_access(
              &flash_ctrl,
              /*rd_en=*/true,
              /*prog_en=*/true,
              /*erase_en=*/true,
              /*scramble_en=*/false,
              /*ecc_en=*/false,
              /*high_endurance_en=*/false);

          RETURN_IF_ERROR(erase_flash());
        }

        if (flash_ctrl_testutils_write(&flash_ctrl, frame.header.flash_offset,
                                       /*partition_id=*/0, frame.data,
                                       kDifFlashCtrlPartitionTypeData,
                                       SPIFLASH_FRAME_DATA_WORDS)) {
          return kErrorBootstrapWrite;
        }

        ++expected_frame_num;
        if (SPIFLASH_FRAME_IS_EOF(frame.header.frame_num)) {
          rom_printf("Bootstrap: DONE!\n\r");
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

static rom_error_t primitive_bootstrap_impl(void) {
  rom_printf("Bootstrap: BEGIN\n\r");

  OT_DISCARD(dif_flash_ctrl_init_state(
      &flash_ctrl,
      mmio_region_from_addr(TOP_EARLGREY_FLASH_CTRL_CORE_BASE_ADDR)));
  flash_ctrl_testutils_wait_for_init(&flash_ctrl);

  RETURN_IF_ERROR(spi_device_init());

  rom_error_t error = bootstrap_flash();
  if (error != kErrorOk) {
    if (erase_flash() != kErrorOk) {
      error = kErrorBootstrapEraseExit;
    }
  }

  return error;
}

rom_error_t primitive_bootstrap(lifecycle_state_t lc_state) {
  bool bootstrap_request_pending = false;
  RETURN_IF_ERROR(bootstrap_requested(&bootstrap_request_pending));
  if (!bootstrap_request_pending) {
    return kErrorOk;
  }

  // Disable the watchdog timer before entering bootstrap.
  // TODO(lowRISC/opentitan#10631): decide on watchdog strategy for bootstrap.
  watchdog_disable();
  SEC_MMIO_WRITE_INCREMENT(kWatchdogSecMmioDisable);

  rom_error_t error = primitive_bootstrap_impl();

  // Re-initialize the watchdog timer once bootstrap is complete.
  watchdog_init(lc_state);
  SEC_MMIO_WRITE_INCREMENT(kWatchdogSecMmioInit);

  // Always make sure to revert flash_ctrl access to default settings.
  // bootstrap_flash enables access to flash to perform update.
  flash_ctrl_testutils_default_region_access(
      &flash_ctrl, /*rd_en=*/false, /*prog_en=*/false, /*erase_en=*/false,
      /*scramble_en=*/false, /*ecc_en=*/false, /*high_endurance_en=*/false);
  return error;
}
