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

#include "dma_regs.h"  // Generated.
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
} dif_dma_address_space_id_t;

/* Supported transaction widths by the DMA */
typedef enum dif_dma_transaction_width {
  /* Transfer 1 byte at a time.*/
  kDifDmaTransWidth1Byte = 0x00,
  /* Transfer 2 byte at a time.*/
  kDifDmaTransWidth2Bytes = 0x01,
  /* Transfer 4 byte at a time.*/
  kDifDmaTransWidth4Bytes = 0x02,
} dif_dma_transaction_width_t;

/* Supported Opcodes by the DMA */
typedef enum dif_dma_transaction_opcode {
  /* Simple copy from source to destination.*/
  kDifDmaCopyOpcode = 0x00,
  /* Inline hashing with SHA2-256.*/
  kDifDmaSha256Opcode = 0x01,
  /* Inline hashing with SHA2-384.*/
  kDifDmaSha384Opcode = 0x02,
  /* Inline hashing with SHA2-512.*/
  kDifDmaSha512Opcode = 0x03,
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
  /* Chunk size (in bytes) of the data object to transferred.*/
  size_t chunk_size;
  /* Total size (in bytes) of the data object to transferred.*/
  size_t total_size;
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

/**
 * Checks whether the DMA memory range is valid.
 *
 * @param dma A DMA Controller handle.
 * @param[out] is_valid Out-param for the valid state.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_is_memory_range_valid(const dif_dma_t *dma,
                                           bool *is_valid);

/**
 * Set thresholds for detecting the level of the buffer.Used in conjunction with
 * the address auto-increment mode for hardware handshake operation to generate
 * an interrupt when the buffer address approaches to the buffer address limit.
 *
 * This function is expected to be called when `memory_auto_increment` is
 * enabled via the function `dif_dma_handshake_enable`.
 *
 * @param dma A DMA Controller handle.
 * @param almost_limit Threshold for detecting that the buffer limit is
 * approaching to prevent destination buffer overflow.
 * @param limit Threshold for detecting the buffer limit.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_irq_thresholds_set(const dif_dma_t *dma,
                                        uint64_t almost_limit, uint64_t limit);

/**
 * Set thresholds for detecting the level of the buffer.Used in conjunction with
 * the address auto-increment mode for hardware handshake operation to generate
 * an interrupt when the buffer address approaches to the buffer address limit.
 *
 * This function is expected to be called when `memory_auto_increment` is
 * enabled via the function `dif_dma_handshake_enable`.
 *
 * @param dma A DMA Controller handle.
 * @param[out] almost_limit Out-param for the almost limit address.
 * @param[out] limit Out-param for the limit address.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_irq_thresholds_get(const dif_dma_t *dma,
                                        uint64_t *almost_limit,
                                        uint64_t *limit);

typedef enum dif_dma_status_code {
  // DMA operation is active.
  kDifDmaStatusBusy = 0x01 << DMA_STATUS_BUSY_BIT,
  // Configured DMA operation is complete.
  kDifDmaStatusDone = 0x01 << DMA_STATUS_DONE_BIT,
  // Set once aborted operation drains.
  kDifDmaStatusAborted = 0x01 << DMA_STATUS_ABORTED_BIT,
  // Error occurred during the operation.
  // Check the error_code for information about the source of the error.
  kDifDmaStatusError = 0x01 << DMA_STATUS_ERROR_BIT,
  // Set once the SHA2 digest is valid after finishing a transfer
  kDifDmaStatusSha2DigestValid = 0x01 << DMA_STATUS_SHA2_DIGEST_VALID_BIT,
} dif_dma_status_code_t;

/**
 * Bitmask with the `dif_dma_status_code_t` values.
 */
typedef uint32_t dif_dma_status_t;
/**
 * Reads the DMA status.
 *
 * @param dma A DMA Controller handle.
 * @param[out] status Out-param for the status.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_status_get(const dif_dma_t *dma, dif_dma_status_t *status);

/**
 * Writes the DMA status register and clears the corrsponding status bits.
 *
 * @param dma A DMA Controller handle.
 * @param status Status bits to be cleared.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_status_write(const dif_dma_t *dma,
                                  dif_dma_status_t status);

/**
 * Clear all status bits of the status register.
 *
 * @param dma A DMA Controller handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_status_clear(const dif_dma_t *dma);

/**
 * Poll the DMA status util a given flag in the register is set.
 *
 * @param dma A DMA Controller handle.
 * @param flag The status that needs to bet set.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_status_poll(const dif_dma_t *dma,
                                 dif_dma_status_code_t flag);

typedef enum dif_dma_error_code {
  // Source address error.
  kDifDmaErrorNone = 0x00,
  // Source address error.
  kDifDmaErrorSourceAddress = 0x01 << 0,
  // Destination address error.
  kDifDmaErrorDestinationAddress = 0x01 << 1,
  // Opcode error.
  kDifDmaErrorOpcode = 0x01 << 2,
  // Size error.
  kDifDmaErrorSize = 0x01 << 3,
  // Bus transaction error.
  kDifDmaErrorBus = 0x01 << 4,
  // DMA enable memory config error.
  kDifDmaErrorEnableMemoryConfig = 0x01 << 5,
  // Register range valid error.
  kDifDmaErrorRangeValid = 0x01 << 6,
  // Invalid ASID error.
  kDifDmaErrorInvalidAsid = 0x01 << 7,
} dif_dma_error_code_t;

/**
 * Reads the DMA error code.
 *
 * @param dma A DMA Controller handle.
 * @param[out] error Out-param for the error code.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_error_code_get(const dif_dma_t *dma,
                                    dif_dma_error_code_t *error);
/**
 * Read out the SHA2 digest
 *
 * @param dma A DMA Controller handle.
 * @param opcode The opcode to select the length of the read digest.
 * @param[out] digest Pointer to the digest, to store the read values.
 * @return The result of the operation.
 */
dif_result_t dif_dma_sha2_digest_get(const dif_dma_t *dma,
                                     dif_dma_transaction_opcode_t opcode,
                                     uint32_t digest[]);

/**
 * Enable DMA controller handshake interrupt.
 *
 * @param dma A DMA Controller handle.
 * @param enable_state Enable state. The bit position corresponds to the IRQ
 * index.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_handshake_irq_enable(const dif_dma_t *dma,
                                          uint32_t enable_state);

/**
 * Enable the corresponding DME handshake interrupt clearing mechanism.
 *
 * @param dma A DMA Controller handle.
 * @param clear_state Enable interrupt clearing mechanism. The bit position
 *                    corresponds to the IRQ index.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_handshake_clear_irq(const dif_dma_t *dma,
                                         uint32_t clear_state);

/**
 * Select the bus interface for the interrupt clearing mechanism.
 * 0: CTN/System fabric
 * 1: OT-internal crossbar
 *
 * @param dma A DMA Controller handle.
 * @param clear_irq_bus Bus selection for the clearing mechanism. The bit
 * position corresponds to the IRQ index.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_handshake_clear_irq_bus(const dif_dma_t *dma,
                                             uint32_t clear_irq_bus);

/**
 * Address index for every interrupt. Used to configure the write address and
 * write value for the interrupt clearing mechanism.
 */
typedef enum dif_dma_intr_idx {
  kDifDmaIntrClearIdx0 = 0x0,
  kDifDmaIntrClearIdx1 = 0x4,
  kDifDmaIntrClearIdx2 = 0x8,
  kDifDmaIntrClearIdx3 = 0xC,
  kDifDmaIntrClearIdx4 = 0x10,
  kDifDmaIntrClearIdx5 = 0x14,
  kDifDmaIntrClearIdx6 = 0x18,
  kDifDmaIntrClearIdx7 = 0x1C,
  kDifDmaIntrClearIdx8 = 0x20,
  kDifDmaIntrClearIdx9 = 0x24,
  kDifDmaIntrClearIdx10 = 0x28,
} dif_dma_intr_idx_t;

/**
 * Set the write address for the interrupt clearing mechanism.
 *
 * @param dma A DMA Controller handle.
 * @param idx Index of the selected interrupt.
 * @param intr_src_addr Address to write the interrupt clearing value to.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_intr_src_addr(const dif_dma_t *dma, dif_dma_intr_idx_t idx,
                                   uint32_t intr_src_addr);

/**
 * Set the write value for the interrupt clearing mechanism.
 *
 * @param dma A DMA Controller handle.
 * @param idx Index of the selected interrupt.
 * @param intr_src_value Value to write the interrupt clearing value to.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_dma_intr_write_value(const dif_dma_t *dma,
                                      dif_dma_intr_idx_t idx,
                                      uint32_t intr_src_value);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_DMA_H_
