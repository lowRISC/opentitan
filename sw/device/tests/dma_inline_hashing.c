// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "dt/dt_dma.h"
#include "dt/dt_pinmux.h"
#include "dt/dt_rv_core_ibex.h"
#include "dt/dt_rv_plic.h"
#include "dt/dt_spi_host.h"
#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_dma.h"
#include "sw/device/lib/dif/dif_pinmux.h"
#include "sw/device/lib/dif/dif_rv_plic.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/lib/runtime/irq.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/dma_testutils.h"
#include "sw/device/lib/testing/pinmux_testutils.h"
#include "sw/device/lib/testing/rand_testutils.h"
#include "sw/device/lib/testing/rv_core_ibex_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"
#include "sw/device/lib/testing/test_framework/status.h"

// The TX_SIZE must be in sync with the data size in spi_device_dma_seq.sv
// 1 SPI segment can only transfer at maximum 512 bytes
#define TX_SIZE 512
#define CHUNK_SIZE 32 * 4  // Half the SPI host FIFO size

OTTF_DEFINE_TEST_CONFIG();

enum {
  kHart = kTopDarjeelingPlicTargetIbex0,
  kIrqVoid = UINT32_MAX,
};

dif_dma_transaction_width_t dma_transfer_widths[] = {
    kDifDmaTransWidth1Byte, kDifDmaTransWidth2Bytes, kDifDmaTransWidth4Bytes};

// Expected digest value gets backdoor'ed from the hardware
static volatile const uint32_t kShaDigestExpData[16];
static volatile const uint8_t kShaMode;

uint32_t digest[16], digest_2[16];
uint8_t received_data[TX_SIZE] __attribute__((aligned(4)));
uint8_t target_ot_internal_data[TX_SIZE] __attribute__((aligned(4)));
uint8_t target_ctn_data[TX_SIZE] __attribute__((aligned(4)))
__attribute__((section(".ctn_data")));
static volatile bool is_finished;

static dif_spi_host_t spi_host;
static dif_pinmux_t pinmux;
static dif_dma_t dma;
static dif_rv_core_ibex_t rv_core_ibex;
static dif_rv_plic_t rv_plic;

/**
 * Enable the interrupts required by this test.
 */
static void init_interrupts(void) {
  irq_global_ctrl(false);
  irq_external_ctrl(false);

  // Set Ibex IRQ priority threshold level to lowest (0)
  // - All IRQs with prio > 0 will not be masked
  CHECK_DIF_OK(
      dif_rv_plic_target_set_threshold(&rv_plic, kHart, kDifRvPlicMinPriority));

  // Enable IRQs at rv_plic
  // - enable
  // - set prio > 0
  CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(
      &rv_plic, kTopDarjeelingPlicIrqIdDmaDmaDone, kHart, kDifToggleEnabled));
  CHECK_DIF_OK(dif_rv_plic_irq_set_priority(
      &rv_plic, kTopDarjeelingPlicIrqIdDmaDmaDone, kDifRvPlicMaxPriority));
  // Enable IRQs at the peripheral
  CHECK_DIF_OK(
      dif_dma_irq_set_enabled(&dma, kDifDmaIrqDmaDone, kDifToggleEnabled));

  irq_external_ctrl(true);
  irq_global_ctrl(true);
}

/**
 * External ISR handler for this test.
 * (Our overridden ottf_external_isr() calls this function only.)
 *
 * - Claim the interrupt
 * - Check this irq_id is valid for this test
 * continue
 */
static status_t external_isr(void) {
  dif_dma_irq_t dma_irq_id;
  dif_rv_plic_irq_id_t plic_irq_id;
  top_darjeeling_plic_peripheral_t peripheral;

  // (1) First, find which interrupt fired at PLIC by claiming it.
  TRY(dif_rv_plic_irq_claim(&rv_plic, kHart, &plic_irq_id));

  // Check the plic_irq is actually from a DMA peripheral
  // This test currently cannot handle any other interrupts, as the logic/ISRs
  // are not sufficiently robust.
  CHECK(plic_irq_id >= kTopDarjeelingPlicIrqIdDmaDmaDone &&
            plic_irq_id <= kTopDarjeelingPlicIrqIdDmaDmaError,
        "got an irq from a plic_peripheral that is not a DMA!");

  peripheral = (top_darjeeling_plic_peripheral_t)
      top_darjeeling_plic_interrupt_for_peripheral[plic_irq_id];

  dif_rv_plic_irq_id_t plic_periph_base_irq_id =
      kTopDarjeelingPlicIrqIdDmaDmaDone;

  if (peripheral != kTopDarjeelingPlicPeripheralDma) {
    CHECK(false, "Invalid plic_irq_id that from a DMA!");
  }

  dma_irq_id = (dif_dma_irq_t)(plic_irq_id - plic_periph_base_irq_id);

  // (2) Handle the peripheral
  if (dma_irq_id == kDifDmaIrqDmaDone) {
    // Mask the interrupt (also for the next test)
    CHECK_DIF_OK(dif_dma_irq_set_enabled(&dma, dma_irq_id, kDifToggleDisabled));
    CHECK_DIF_OK(dif_rv_plic_irq_set_enabled(&rv_plic, plic_irq_id, kHart,
                                             kDifToggleDisabled));

  } else {
    CHECK(false, "Invalid dma_irq_id: %d", dma_irq_id);
  }

  // (3) Clear the IRQ at the peripheral and at the PLIC.
  // - This section is lifted from the end of the isr_testutils autgenerated
  // handler
  // - Only the plic_irq_complete() routine matters, since we cannot-yet clear
  // the
  //   INTR_STATE reg at the dma as the event input is still asserted.

  // Acknowledge the IRQ at the peripheral if IRQ is of the event type.
  CHECK_DIF_OK(dif_dma_irq_acknowledge(&dma, dma_irq_id));

  // Complete the IRQ at the PLIC.
  CHECK_DIF_OK(dif_rv_plic_irq_complete(&rv_plic, kHart, plic_irq_id));

  // Set the boolean which allows wfi_flag() to return.
  is_finished = true;

  return OK_STATUS();
}

static volatile status_t isr_result;
/* This overrides the weak-symbol for ottf_external_isr() */
void ottf_external_isr(void) {
  status_t tmp = external_isr();
  if (status_ok(isr_result)) {
    isr_result = tmp;
  }
}

bool test_main(void) {
  // Initialize the pinmux.
  CHECK_DIF_OK(dif_pinmux_init_from_dt(kDtPinmuxAon, &pinmux));
  pinmux_testutils_init(&pinmux);

  // Initialise DMA.
  CHECK_DIF_OK(dif_dma_init_from_dt(kDtDma, &dma));

  // Initialize the PLIC
  CHECK_DIF_OK(dif_rv_core_ibex_init_from_dt(kDtRvCoreIbex, &rv_core_ibex));
  CHECK_DIF_OK(dif_rv_plic_init_from_dt(kDtRvPlic, &rv_plic));

  // Setup pinmux if required, enable weak pull-up on relevant pads
  setup_pads_spi_host0(&pinmux);  // direct

  // Setup spi host configuration
  CHECK_DIF_OK(dif_spi_host_init_from_dt((dt_spi_host_t)0, &spi_host));
  init_spi_host(&spi_host, (uint32_t)kClockFreqHiSpeedPeripheralHz,
                CHUNK_SIZE / 4);

  init_interrupts();

  // DV sync message
  LOG_INFO("spi host configuration complete");

  // Based on the SHA mode, determine the digest length
  uint32_t digest_len;
  CHECK_DIF_OK(dif_dma_get_digest_length(kShaMode, &digest_len));

  setup_spi_dma_transaction(&spi_host, &dma, &received_data[0], CHUNK_SIZE,
                            TX_SIZE);

  CHECK_DIF_OK(dif_dma_start(&dma, kShaMode));

  // Loop WFI->ISR->WFI->etc. until 'is_finished' is set true
  // Use this to only advance iff our ISR sets it
  ATOMIC_WAIT_FOR_INTERRUPT(is_finished);

  dif_dma_status_code_t status;
  CHECK_DIF_OK(dif_dma_status_get(&dma, &status));

  CHECK((status & kDifDmaStatusDone) == kDifDmaStatusDone,
        "DMA status done not asserted");
  CHECK((status & kDifDmaStatusSha2DigestValid) == kDifDmaStatusSha2DigestValid,
        "DMA status digest valid not asserted");

  CHECK_DIF_OK(dif_dma_sha2_digest_get(&dma, kShaMode, digest));

  // Randomize the transfer width, which is possible since we are not using the
  // inline hashing mode
  dif_dma_transaction_width_t transfer_width =
      dma_transfer_widths[rand_testutils_gen32_range(
          0, ARRAYSIZE(dma_transfer_widths) - 1)];

  dif_dma_transaction_address_t dest_transaction_address;
  // Decide where to transfer the second transfer the data to
  if (rand_testutils_gen32_range(0, 1) == 0) {
    // OT internal memory
    dest_transaction_address = (dif_dma_transaction_address_t){
        .address = (uint32_t)&target_ot_internal_data[0],
        .asid = kDifDmaOpentitanInternalBus};
  } else {
    // CTN memory
    dest_transaction_address = (dif_dma_transaction_address_t){
        .address = (uint32_t)&target_ctn_data[0],
        .asid = kDifDmaSoCControlRegisterBus};
  }

  // We only check the digest. If thats valid, we assume the correct data to be
  // transferred
  CHECK_ARRAYS_EQ((uint8_t *)digest, (uint8_t *)kShaDigestExpData, digest_len);

  dif_dma_transaction_t transaction = {
      .source = {.address = (uint32_t)&received_data[0],
                 .asid = kDifDmaOpentitanInternalBus},
      .destination = dest_transaction_address,
      .total_size = TX_SIZE,
      .chunk_size = TX_SIZE,
      .width = transfer_width};

  CHECK_DIF_OK(dif_dma_handshake_irq_enable(&dma, 0x0));
  CHECK_DIF_OK(dif_dma_configure(&dma, transaction));
  CHECK_DIF_OK(dif_dma_handshake_disable(&dma));

  CHECK_DIF_OK(dif_dma_start(&dma, kDifDmaCopyOpcode));
  CHECK_DIF_OK(dif_dma_status_poll(&dma, kDifDmaStatusDone));

  CHECK_ARRAYS_EQ((uint8_t *)received_data,
                  (uint8_t *)dest_transaction_address.address, TX_SIZE);

  return true;
}
