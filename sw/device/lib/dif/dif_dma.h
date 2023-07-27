// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_DMA_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_DMA_H_

/**
 * @file
 * @brief <a href="/hw/ip/dma/doc/">DMA Controller</a> Device Interface
 * Functions
 */

#include <stdint.h>

#include "sw/device/lib/dif/autogen/dif_dma_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

// Target Address space that the source address pointer refers to.
typedef enum dif_dma_address_space_id {
  /* OpenTitan 32 bit internal bus. */
  kDifDmaOpentitanInternalBus = 0x07,

  /* SoC control register address bus using 32 bit (or 64 bits if configured by
     an SoC) CTN port .*/
  kDifDmaSoCControlRegisterBus = 0x0a,

  /* SoC system address bus using 64 bit SYS port. */
  kDifDmaSoCSystemBus = 0x09,

  /* OT External Flash address space. */
  kDifDmaOpentitanExternalFlash = 0x0c,
} dif_dma_address_space_id_t;

/* Supported transaction widths by the DMA */
typedef enum dif_dma_transaction_width {
  /* Transfer 1 byte at a time.*/
  kDifDmaTransWidth1Byte = 0x00,
  /* Transfer 2 byte at a time.*/
  kDifDmaTransWidth2Bytes = 0x01,
  /* Transfer 4 byte at a time.*/
  kDifDmaTransWidth4Bytes = 0x03,
} dif_dma_transaction_width_t;

/* Supported Opcodes by the DMA */
typedef enum dif_dma_transaction_opcode {
  /* Simple copy from source to destination.*/
  kDifDmaCopyOpcode = 0x00,
} dif_dma_transaction_opcode_t;

/**
 * Define the transaction address space.
 */
typedef struct dif_dma_transaction_address {
  uint64_t address;
  dif_dma_address_space_id_t asid;
} dif_dma_transaction_address_t;

/**
 * Parameters for a DMA Controller transaction.
 */
typedef struct dif_dma_transaction {
  dif_dma_transaction_address_t source;
  dif_dma_transaction_address_t destination;
  /* Size (in bytes) of the data object to transferred.*/
  size_t size;
  /* Iteration width.*/
  dif_dma_transaction_width_t width;
} dif_dma_transaction_t;

/**
 * Configures DMA Controller for a transaction.
 *
 * This function should be called every time before `dif_dma_start`.
 *
 * @param dma A DMA Controller handle.
 * @param config Transaction configuration parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_configure(const dif_dma_t *dma,
                               dif_dma_transaction_t transaction);

/**
 * Parameters for a handshake mode transaction.
 */
typedef struct dif_dma_handshake {
  /* Auto Increments the memory buffer address register by total data size to
   * point to the next memory buffer address. Generate a warning (assert
   * interrupt) if the auto-incremented address reaches the threshold set in
   * DMAC Memory Buffer Almost Limit Threshold Register to prevent destination
   * buffer overflow. Enables firmware to take appropriate action prior to
   * reaching the limit */
  bool memory_auto_increment;

  /* If `true`, reads/writes from/to incremental addresses for FIFO data
   * register addresses, otherwise uses the same address for subsequent
   * transactions.*/
  bool fifo_auto_increment;

  /* If `true` move data from memory buffer to the LSIO FIFO, otherwise move
   * data from the LSIO FIFO to the memory buffer.*/
  bool direction_from_mem_to_fifo;
} dif_dma_handshake_t;

/**
 * Configures DMA Controller hardware handshake mode.
 *
 * This function should be called before `dif_dma_start`.
 *
 * Hardware handshake mode is used to push / pop FIFOs to / from low speed IO
 * peripherals receiving data e.g. I3C receive buffer.
 *
 * @param dma A DMA Controller handle.
 * @param handshake Hardware handshake configuration parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_handshake_enable(const dif_dma_t *dma,
                                      dif_dma_handshake_t handshake);

/**
 * Disable DMA Controller hardware handshake mode.
 *
 * @param dma A DMA Controller handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_handshake_disable(const dif_dma_t *dma);

/**
 * Begins a DMA Controller transaction.
 *
 * Before this function the DMA transaction shall be configured by calling the
 * function `dif_dma_configure` and optionally `dif_dma_handshake_enable` can be
 * called.
 *
 * @param dma A DMA Controller handle.
 * @param opcode Transaction opcode.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_start(const dif_dma_t *dma,
                           dif_dma_transaction_opcode_t opcode);

/**
 * Abort the DMA Controller transaction in execution.
 *
 * @param dma A DMA Controller handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_abort(const dif_dma_t *dma);

/**
 * Set the DMA enabled memory range within the OT internal memory space.
 *
 * @param dma A DMA Controller handle.
 * @param address Base address.
 * @param size The range size.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_memory_range_set(const dif_dma_t *dma, uint32_t address,
                                      size_t size);

/**
 * Get the DMA enabled memory range within the OT internal memory space.
 *
 * @param dma A DMA Controller handle.
 * @param[out] address Out-param for the base address.
 * @param[out] size Out-param for the range size.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_memory_range_get(const dif_dma_t *dma, uint32_t *address,
                                      size_t *size);
/**
 * Locks out the DMA memory range register.
 *
 * This function is reentrant: calling it while functionality is locked will
 * have no effect and return `kDifOk`.
 *
 * @param dma A DMA Controller handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_memory_range_lock(const dif_dma_t *dma);

/**
 * Checks whether the DMA memory range is locked.
 *
 * @param dma A DMA Controller handle.
 * @param[out] is_locked Out-param for the locked state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_is_memory_range_locked(const dif_dma_t *dma,
                                            bool *is_locked);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_DMA_H_
