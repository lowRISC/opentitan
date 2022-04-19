// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/test_rom/bootstrap.h"

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_flash_ctrl.h"
#include "sw/device/lib/dif/dif_gpio.h"
#include "sw/device/lib/dif/dif_hmac.h"
#include "sw/device/lib/dif/dif_spi_device.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/flash_ctrl_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_rom/spiflash_frame.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define GPIO_BOOTSTRAP_BIT_MASK 0x00020000u

/**
 * Check if flash is blank to determine if bootstrap is needed.
 */
static bool bootstrap_requested(void) {
  dif_gpio_t gpio;
  CHECK_DIF_OK(
      dif_gpio_init(mmio_region_from_addr(TOP_EARLGREY_GPIO_BASE_ADDR), &gpio));

  dif_gpio_state_t gpio_in;
  CHECK_DIF_OK(dif_gpio_read_all(&gpio, &gpio_in));
  return (gpio_in & GPIO_BOOTSTRAP_BIT_MASK) != 0;
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
  uint32_t mask = UINT32_MAX;
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
static int erase_flash(dif_flash_ctrl_state_t *flash_ctrl) {
  if (flash_ctrl_testutils_bank_erase(flash_ctrl, /*bank=*/0,
                                      /*data_only=*/true)) {
    return E_BS_ERASE;
  }
  if (flash_ctrl_testutils_bank_erase(flash_ctrl, /*bank=*/1,
                                      /*data_only=*/true)) {
    return E_BS_ERASE;
  }
  if (!flash_is_empty()) {
    return E_BS_NOTEMPTY;
  }

  return 0;
}

/**
 * Computes the SHA256 of the given data.
 */
static void compute_sha256(const dif_hmac_t *hmac, const void *data, size_t len,
                           dif_hmac_digest_t *digest) {
  const dif_hmac_transaction_t config = {
      .digest_endianness = kDifHmacEndiannessLittle,
      .message_endianness = kDifHmacEndiannessLittle,
  };
  CHECK_DIF_OK(dif_hmac_mode_sha256_start(hmac, config));
  const char *data8 = (const char *)data;
  size_t data_left = len;
  while (data_left > 0) {
    size_t bytes_sent;
    dif_result_t result =
        dif_hmac_fifo_push(hmac, data8, data_left, &bytes_sent);
    if (result == kDifOk) {
      break;
    }
    CHECK(result == kDifIpFifoFull, "Error while pushing to FIFO.");
    data8 += bytes_sent;
    data_left -= bytes_sent;
  }

  CHECK_DIF_OK(dif_hmac_process(hmac));
  dif_result_t digest_result = kDifUnavailable;
  while (digest_result == kDifUnavailable) {
    digest_result = dif_hmac_finish(hmac, digest);
  }
  CHECK_DIF_OK(digest_result);

  // Swap word order to keep hashes consistent with those generated in the
  // MaskROM (little-endian).
  for (size_t i = 0; i < 4; ++i) {
    uint32_t tmp = digest->digest[i];
    digest->digest[i] = digest->digest[7 - i];
    digest->digest[7 - i] = tmp;
  }
}

/**
 * Compares the SHA256 hash of the recieved data with the recieved hash.
 *
 * Returns true if the hashes match.
 */
static bool check_frame_hash(const dif_hmac_t *hmac,
                             const spiflash_frame_t *frame) {
  dif_hmac_digest_t digest;
  size_t digest_len = sizeof(digest.digest);

  uint8_t *data = ((uint8_t *)frame) + digest_len;
  compute_sha256(hmac, data, sizeof(spiflash_frame_t) - digest_len, &digest);

  return memcmp(digest.digest, frame->header.hash.digest, digest_len) == 0;
}

/**
 * Load spiflash frames from the SPI interface.
 *
 * This function checks that the sequence numbers and hashes of the frames are
 * correct before programming them into flash.
 */
static int bootstrap_flash(const dif_spi_device_t *spi,
                           const dif_spi_device_config_t *spi_config,
                           const dif_hmac_t *hmac,
                           dif_flash_ctrl_state_t *flash_ctrl) {
  dif_hmac_digest_t ack = {0};
  uint32_t expected_frame_num = 0;
  while (true) {
    size_t bytes_available;
    CHECK_DIF_OK(dif_spi_device_rx_pending(spi, spi_config, &bytes_available));
    if (bytes_available >= sizeof(spiflash_frame_t)) {
      spiflash_frame_t frame;
      CHECK_DIF_OK(dif_spi_device_recv(spi, spi_config, &frame,
                                       sizeof(spiflash_frame_t),
                                       /*bytes_received=*/NULL));

      uint32_t frame_num = SPIFLASH_FRAME_NUM(frame.header.frame_num);
      LOG_INFO("Processing frame #%d, expecting #%d", frame_num,
               expected_frame_num);

      if (frame_num == expected_frame_num) {
        if (!check_frame_hash(hmac, &frame)) {
          LOG_ERROR("Detected hash mismatch on frame #%d", frame_num);
          CHECK_DIF_OK(dif_spi_device_send(
              spi, spi_config, (uint8_t *)&ack.digest, sizeof(ack.digest),
              /*bytes_received=*/NULL));
          continue;
        }

        compute_sha256(hmac, &frame, sizeof(spiflash_frame_t), &ack);
        CHECK_DIF_OK(dif_spi_device_send(
            spi, spi_config, (uint8_t *)&ack.digest, sizeof(ack.digest),
            /*bytes_received=*/NULL));

        if (expected_frame_num == 0) {
          // Set up default access for data partition.
          flash_ctrl_testutils_default_region_access(
              flash_ctrl,
              /*rd_en=*/true,
              /*prog_en=*/true,
              /*erase_en=*/true,
              /*scramble_en=*/false,
              /*ecc_en=*/false,
              /*high_endurance_en=*/false);

          int flash_error = erase_flash(flash_ctrl);
          if (flash_error != 0) {
            return flash_error;
          }
          LOG_INFO("Flash erase successful");
        }

        if (flash_ctrl_testutils_write(flash_ctrl, frame.header.flash_offset,
                                       /*partition_id=*/0, frame.data,
                                       kDifFlashCtrlPartitionTypeData,
                                       SPIFLASH_FRAME_DATA_WORDS)) {
          return E_BS_WRITE;
        }

        LOG_INFO("Frame #%d processed done", expected_frame_num);
        ++expected_frame_num;
        if (SPIFLASH_FRAME_IS_EOF(frame.header.frame_num)) {
          LOG_INFO("Bootstrap: DONE!");
          return 0;
        }
      } else {
        // Send previous ack if unable to verify current frame.
        CHECK_DIF_OK(dif_spi_device_send(
            spi, spi_config, (uint8_t *)&ack.digest, sizeof(ack.digest),
            /*bytes_received=*/NULL));
      }
    }
  }
}

int bootstrap(dif_flash_ctrl_state_t *flash_ctrl) {
  if (!bootstrap_requested()) {
    return 0;
  }

  // SPI device is only initialized in bootstrap mode.
  LOG_INFO("Bootstrap requested, initialising HW...");
  flash_ctrl_testutils_wait_for_init(flash_ctrl);

  dif_spi_device_t spi;
  dif_spi_device_config_t spi_config = {
      .clock_polarity = kDifSpiDeviceEdgePositive,
      .data_phase = kDifSpiDeviceEdgeNegative,
      .tx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .rx_order = kDifSpiDeviceBitOrderMsbToLsb,
      .rx_fifo_timeout = 63,
      .rx_fifo_len = kDifSpiDeviceBufferLen / 2,
      .tx_fifo_len = kDifSpiDeviceBufferLen / 2,
  };
  CHECK_DIF_OK(dif_spi_device_init(
      mmio_region_from_addr(TOP_EARLGREY_SPI_DEVICE_BASE_ADDR), &spi));
  CHECK_DIF_OK(dif_spi_device_configure(&spi, &spi_config));

  dif_hmac_t hmac;
  CHECK_DIF_OK(
      dif_hmac_init(mmio_region_from_addr(TOP_EARLGREY_HMAC_BASE_ADDR), &hmac));

  LOG_INFO("HW initialisation completed, waiting for SPI input...");
  int error = bootstrap_flash(&spi, &spi_config, &hmac, flash_ctrl);
  if (error != 0) {
    error |= erase_flash(flash_ctrl);
    LOG_ERROR("Bootstrap error: 0x%x", error);
  }

  // Always make sure to revert flash_ctrl access
  // to default settings. bootstrap_flash enables
  // access to flash to perform update.
  flash_ctrl_testutils_default_region_access(flash_ctrl, /*rd_en=*/false,
                                             /*prog_en=*/false,
                                             /*erase_en=*/false,
                                             /*scramble_en=*/false,
                                             /*ecc_en=*/false,
                                             /*high_endurance_en=*/false);

  return error;
}
