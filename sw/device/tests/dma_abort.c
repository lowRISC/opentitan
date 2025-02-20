// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "dt/dt_dma.h"
#include "dt/dt_pinmux.h"
#include "dt/dt_spi_host.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_dma.h"
#include "sw/device/lib/dif/dif_spi_host.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/dma_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"

// The TX_SIZE must be in sync with the data size in spi_device_dma_seq.sv
// 1 SPI segment can only transfer at maximum 512 bytes
#define TX_SIZE 512
#define CHUNK_SIZE 32 * 4  // Half the SPI host FIFO size

OTTF_DEFINE_TEST_CONFIG();

enum {
  kSoftwareBarrierTimeoutUsec = 500,
};

// This location will be update from SV
static volatile const uint8_t kSoftwareBarrier = 0;

// Expected digest value gets backdoor'ed from the hardware
// Although not used, we need to keep it here as the shared vseq
// wants to write it.
static volatile uint32_t kShaDigestExpData[16];
static volatile uint8_t kShaMode;

uint32_t digest[16];
uint8_t received_data[TX_SIZE] __attribute__((aligned(4)));

static dif_spi_host_t spi_host;
static dif_pinmux_t pinmux;
static dif_dma_t dma;

bool test_main(void) {
  // Initialize the pinmux.
  CHECK_DIF_OK(dif_pinmux_init_from_dt(kDtPinmuxAon, &pinmux));
  pinmux_testutils_init(&pinmux);

  // Initialise DMA.
  CHECK_DIF_OK(dif_dma_init_from_dt(kDtDma, &dma));

  // Setup pinmux if required, enable weak pull-up on relevant pads
  setup_pads_spi_host0(&pinmux);  // direct

  // Setup spi host configuration
  CHECK_DIF_OK(dif_spi_host_init_from_dt((dt_spi_host_t)0, &spi_host));
  init_spi_host(&spi_host, (uint32_t)kClockFreqHiSpeedPeripheralHz,
                CHUNK_SIZE / 4);

  // DV sync message
  LOG_INFO("spi host configuration complete");

  // Dummy assignment to avoid any unused variable warnings
  kShaDigestExpData[0] = 0;

  setup_spi_dma_transaction(&spi_host, &dma, &received_data[0], CHUNK_SIZE,
                            TX_SIZE);

  CHECK_DIF_OK(dif_dma_start(&dma, kShaMode));

  // Wait until the DMA has started to abort the transfer
  IBEX_SPIN_FOR(kSoftwareBarrier == 1, kSoftwareBarrierTimeoutUsec);

  CHECK_DIF_OK(dif_dma_abort(&dma));

  dif_dma_status_t status;
  CHECK_DIF_OK(dif_dma_status_get(&dma, &status));

  CHECK(status & kDifDmaStatusAborted, "Abort bit not set");

  // Reset and re-init the SPI
  init_spi_host(&spi_host, (uint32_t)kClockFreqHiSpeedPeripheralHz,
                CHUNK_SIZE / 4);
  LOG_INFO("spi host re-configuration complete");

  // Do the second transaction
  setup_spi_dma_transaction(&spi_host, &dma, &received_data[0], CHUNK_SIZE,
                            TX_SIZE);
  CHECK_DIF_OK(dif_dma_start(&dma, kShaMode));
  CHECK_DIF_OK(dif_dma_status_poll(&dma, kDifDmaStatusDone));

  CHECK_DIF_OK(dif_dma_sha2_digest_get(&dma, kShaMode, digest));

  uint32_t digest_len;
  CHECK_DIF_OK(dif_dma_get_digest_length(kShaMode, &digest_len));
  CHECK_ARRAYS_EQ((uint8_t *)digest, (uint8_t *)kShaDigestExpData, digest_len);

  return true;
}
