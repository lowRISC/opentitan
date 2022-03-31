// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SPI_DEVICE_H_
#define OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SPI_DEVICE_H_

/**
 * @file
 * @brief <a href="/hw/ip/spi_device/doc/">SPI Device</a> Device Interface
 * Functions
 */

#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/lib/dif/dif_base.h"

#include "sw/device/lib/dif/autogen/dif_spi_device_autogen.h"

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * The mode that the spi device operates in.
 */
typedef enum dif_spi_device_mode {
  /**
   * In the generic firmware mode, the hardware dumps incoming data to SRAM and
   * outgoing data from the SRAM.
   */
  kDifSpiDeviceModeGeneric = 0,
  /**
   * In flash emulation mode, the hardware behaves like a SPI NOR flash device.
   */
  kDifSpiDeviceModeFlashEmulation = 1,
  /**
   * In pass-through mode, the hardware forwards commands to another SPI flash
   * device, with various tables providing rules for filtering and forwarding.
   * The hardware may be configured to also behave like a SPI NOR flash device,
   * with some commands and/or address regions targeting internal handling,
   * instead of being passed through.
   */
  kDifSpiDeviceModePassthrough = 2,
} dif_spi_device_mode_t;

/**
 * A signal edge type: positive or negative.
 */
typedef enum dif_spi_device_edge {
  /**
   * Represents a positive edge (i.e., from low to high).
   */
  kDifSpiDeviceEdgePositive,
  /**
   * Represents a negative edge (i.e., from high to low).
   */
  kDifSpiDeviceEdgeNegative,
} dif_spi_device_edge_t;

/**
 * A bit ordering within a byte.
 */
typedef enum dif_spi_device_bit_order {
  /**
   * Represents the most-significant-bit to least-significant-bit order.
   */
  kDifSpiDeviceBitOrderMsbToLsb,
  /**
   * Represents the least-significant-bit to most-significant-bit order.
   */
  kDifSpiDeviceBitOrderLsbToMsb,
} dif_spi_device_bit_order_t;

typedef struct dif_spi_device_generic_mode_config {
  /**
   * The length, in bytes, that should be reserved for the RX FIFO.
   *
   * `kDifSpiDeviceBufferLen / 2` is a good default for this value.
   */
  uint16_t rx_fifo_len;
  /**
   * The length, in bytes, that should be reserved for the TX FIFO.
   *
   * `kDifSpiDeviceBufferLen / 2` is a good default for this value.
   */
  uint16_t tx_fifo_len;
  /**
   * The number of bus clock cycles that the RX FIFO waits before committing a
   * sub-word data item to the SRAM. Only used in Generic Mode.
   */
  uint8_t rx_fifo_commit_wait;
} dif_spi_device_generic_mode_config_t;

/**
 * Runtime configuration for SPI.
 *
 * This struct describes runtime information for one-time configuration of the
 * hardware.
 */
typedef struct dif_spi_device_config {
  dif_spi_device_edge_t clock_polarity;
  dif_spi_device_edge_t data_phase;
  dif_spi_device_bit_order_t tx_order;
  dif_spi_device_bit_order_t rx_order;
  dif_spi_device_mode_t device_mode;
  union {
    dif_spi_device_generic_mode_config_t generic;
  } mode_cfg;
} dif_spi_device_config_t;

typedef struct dif_spi_device_tpm_config_t {
  /**
   * Enable the TPM circuit, which has a separate chip-select input but shares
   * the clock and data pins. The TPM can be enabled alongside the other modes.
   */
  bool tpm_enable;
} dif_spi_device_tpm_config_t;

/**
 * Struct containing the relevant run-time information for the DIF.
 */
typedef struct dif_spi_device_handle {
  /**
   * Device information of the hardware.
   */
  dif_spi_device_t dev;
  /**
   * Configuration information of the hardware.
   */
  dif_spi_device_config_t config;
} dif_spi_device_handle_t;

/**
 * The length of the SPI device FIFO buffer, in bytes.
 *
 * Useful for initializing FIFO lengths: for example, for equally-sized FIFOs,
 * `rx_fifo_len` and `tx_fifo_len` would be set to `kDifSpiDeviceBufferLen / 2`.
 */
extern const uint16_t kDifSpiDeviceBufferLen;

/**
 * Initializes a SPI device handle for use.
 *
 * @param base_addr The MMIO base address of the spi_device peripheral.
 * @param[out] Out param for the initialized handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_init_handle(mmio_region_t base_addr,
                                        dif_spi_device_handle_t *spi);

/**
 * Configures SPI with runtime information.
 *
 * This function should need to be called once for the lifetime of `handle`.
 *
 * @param spi A SPI handle.
 * @param config Runtime configuration parameters.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_configure(dif_spi_device_handle_t *spi,
                                      dif_spi_device_config_t config);

/**
 * Issues an "abort" to the given SPI device, causing all in-progress IO to
 * halt.
 *
 * Applies only to generic mode.
 *
 * @param spi A SPI handle.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_abort(dif_spi_device_handle_t *spi);

/**
 * Sets up the "FIFO level" (that is, number of bytes present in a particular
 * FIFO) at which the TxLevel and RxLevel IRQs will fire.
 *
 * For the reciept side, when the FIFO overflows `rx_level` (i.e., goes over
 * the set level), an interrupt is fired. This can be used to detect that more
 * data should be read from the RX FIFO. This is the
 * `Spi Buffer -> Main Memory` case.
 *
 * Conversely, for the transmission side, when the FIFO underflows `tx_level`
 * (i.e., goes below the set level), an interrupt is fired. This can be used
 * to detect that there is free space to write more data to the TX FIFO.
 * This is the `Main Memory -> Spi Buffer` case.
 *
 * Applies only to generic mode.
 *
 * @param spi A SPI handle.
 * @param rx_level The new RX level, as described above.
 * @param tx_level The new TX level, as described above.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_set_irq_levels(dif_spi_device_handle_t *spi,
                                           uint16_t rx_level,
                                           uint16_t tx_level);

/**
 * Returns the number of bytes still pending receipt by software in the RX FIFO.
 *
 * Applies only to generic mode.
 *
 * @param spi A SPI handle.
 * @param[out] bytes_pending The number of bytes pending
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_rx_pending(const dif_spi_device_handle_t *spi,
                                       size_t *bytes_pending);

/**
 * Returns the number of bytes still pending transmission by hardware in the TX
 * FIFO.
 *
 * Applies only to generic mode.
 *
 * @param spi A SPI handle.
 * @param[out] bytes_pending The number of bytes pending
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_tx_pending(const dif_spi_device_handle_t *spi,
                                       size_t *bytes_pending);

/**
 * Reads at most `buf_len` bytes from the RX FIFO; the number of bytes read
 * will be written to `bytes_received`.
 *
 * Applies only to generic mode.
 *
 * @param spi A SPI device.
 * @param[out] buf A pointer to valid memory.
 * @param buf_len The length of the buffer `buf` points to.
 * @param[out] bytes_received The number of bytes successfully read; may be
 * null.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_recv(dif_spi_device_handle_t *spi, void *buf,
                                 size_t buf_len, size_t *bytes_received);

/**
 * Writes at most `buf_len` bytes to the TX FIFO; the number of bytes actually
 * written will be written to `bytes_sent`.
 *
 * Applies only to generic mode.
 *
 * @param spi A SPI device.
 * @param buf A pointer to bytes to be written.
 * @param buf_len The length of the buffer `buf` points to.
 * @param[out] bytes_sent The number of bytes successfully written; may be null.
 * @return The result of the operation.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_send(dif_spi_device_handle_t *spi, const void *buf,
                                 size_t buf_len, size_t *bytes_sent);

typedef struct dif_spi_device_flash_id {
  /** The device ID for the SPI flash. */
  uint16_t device_id;
  /** The JEDEC manufacturer ID. */
  uint8_t manufacturer_id;
  /** The continuation code used before the `manufacturer_id` byte. */
  uint8_t continuation_code;
  /** The number of continuation codes preceding the `manufacturer_id`. */
  uint8_t num_continuation_code;
} dif_spi_device_flash_id_t;

/**
 * Enable the mailbox region for spi_device flash / passthrough modes.
 *
 * Allocate 1 KiB for the mailbox, starting from the provided base `address`.
 *
 * @param spi A SPI device.
 * @param address The base address of the 1 KiB mailbox. The lower 10 bits are
 * ignored.
 * @return kDifBadArg if spi is null, else kDifOk.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_enable_mailbox(dif_spi_device_handle_t *spi,
                                           uint32_t address);

/**
 * Disable the mailbox region for spi_device flash / passthrough modes.
 *
 * @param spi A SPI device.
 * @return kDifBadArg if spi is null, else kDifOk.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_disable_mailbox(dif_spi_device_handle_t *spi);

/**
 * Get the active configuration for the mailbox region.
 *
 * @param spi A SPI device.
 * @param[out] is_enabled Whether the mailbox region is enabled.
 * @param[out] address If the mailbox is enabled, the base address of the
 * mailbox region.
 * @return kDifBadArg if any argument is null, else kDifOk.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_get_mailbox_configuration(
    dif_spi_device_handle_t *spi, dif_toggle_t *is_enabled, uint32_t *address);

/**
 * Set the address mode of the SPI device in flash/passthrough mode.
 *
 * @param spi A SPI device.
 * @param addr_4b If kDifToggleEnabled, set the address mode to 4 Bytes.
 * Otherwise, set the address mode to 3 Bytes.
 * @return kDifBadArg if spi is NULL or addr_4b is not a valid toggle. kDifOk
 * otherwise.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_set_4b_address_mode(dif_spi_device_handle_t *spi,
                                                dif_toggle_t addr_4b);
/**
 * Get the address mode of the SPI device in flash/passthrough mode.
 *
 * @param spi A SPI device.
 * @param[out] addr_4b Points to toggle that will be set to `kDifToggleEnabled`
 * if the device is in 4-byte address mode, else `kDifToggleDisabled`.
 * @return kDifBadArg if spi or addr_4b are NULL. kDifOk otherwise.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_get_4b_address_mode(dif_spi_device_handle_t *spi,
                                                dif_toggle_t *addr_4b);

/**
 * Get the JEDEC ID presented when in flash / passthrough modes.
 *
 * @param spi A SPI device.
 * @param[out] id Points to location that will be set to the current JEDEC ID.
 * @return kDifBadArg if spi or id are NULL. kDifOk otherwise.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_get_flash_id(dif_spi_device_handle_t *spi,
                                         dif_spi_device_flash_id_t *id);
/**
 * Set the JEDEC ID presented when in flash / passthrough modes.
 *
 * @param spi A SPI device.
 * @param id The JEDEC ID to set.
 * @return kDifBadArg if spi is NULL. kDifOk otherwise.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_set_flash_id(dif_spi_device_handle_t *spi,
                                         dif_spi_device_flash_id_t id);

typedef enum dif_spi_device_flash_address_type {
  /** No address for this command */
  kDifSpiDeviceFlashAddrDisabled = 0,
  /** Address size for this command is determined by the current address mode */
  kDifSpiDeviceFlashAddrCfg,
  /** Address size for this command is fixed at 3 bytes */
  kDifSpiDeviceFlashAddr3Byte,
  /** Address size for this command is fixed at 4 bytes */
  kDifSpiDeviceFlashAddr4Byte,
  kDifSpiDeviceFlashAddrCount,
} dif_spi_device_flash_address_type_t;

typedef enum dif_spi_device_payload_io {
  kDifSpiDevicePayloadIoNone = 0x0,
  kDifSpiDevicePayloadIoSingle = 0x1,
  kDifSpiDevicePayloadIoDual = 0x3,
  kDifSpiDevicePayloadIoQuad = 0xf,
  kDifSpiDevicePayloadIoInvalid = 0x10,
} dif_spi_device_payload_io_t;

typedef struct dif_spi_device_flash_command {
  /** The opcode for this command. */
  uint8_t opcode;
  /* The presence and type of the address phase of this command. */
  dif_spi_device_flash_address_type_t address_type;
  /** The number of dummy cycles between the address phase and the payload phase
   * of a command. Note that if `payload_io_width` is
   * `kDifSpiDevicePayloadIoNone`, a nonzero value may cause undefined behavior,
   * possibly including the device assuming dummy cycles are part of this
   * payload-less command.
   */
  uint8_t dummy_cycles;
  /** The I/O width for the payload phase of this command. */
  dif_spi_device_payload_io_t payload_io_type;
  /**
   * Whether to translate the address using the address swap mask and value
   * provided to `dif_spi_device_passthrough_set_swap_address()`. Incompatible
   * with a command with `address_type` that is
   * `kDifSpiDeviceFlashAddrDisabled`.
   */
  bool passthrough_swap_address;
  /** Whether the SPI host is receiving this command's payload phase. */
  bool payload_dir_to_host;
  /** Whether to swap up to the first 32 bits of the payload. */
  bool payload_swap_enable;
  /** Whether to upload the command to the payload FIFO. */
  bool upload;
  /** Whether to set the busy bit in the status register. */
  bool set_busy_status;
} dif_spi_device_flash_command_t;

typedef enum dif_spi_device_flash_buffer_type {
  /** eFlash region */
  kDifSpiDeviceFlashBufferTypeEFlash = 0,
  /** Mailbox region */
  kDifSpiDeviceFlashBufferTypeMailbox,
  /** SFDP region */
  kDifSpiDeviceFlashBufferTypeSfdp,
  /** Payload for uploaded commands */
  kDifSpiDeviceFlashBufferTypePayload,
  /** Count of buffer types */
  kDifSpiDeviceFlashBufferTypes,
} dif_spi_device_flash_buffer_type_t;

/**
 * Set up the indicated command info slot for flash / passthrough modes.
 *
 * @param spi A handle to a spi device.
 * @param slot A command info slot ID.
 * @param enable Whether to enable or disable the command slot.
 * @param command_info If `enable` is set, provides the configuration for the
 *        command.
 * @return `kDifBadArg` if `spi` is NULL or `slot` is larger than the number of
 * command slots. `kDifOk` otherwise.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_set_flash_command_slot(
    dif_spi_device_handle_t *spi, uint8_t slot, dif_toggle_t enable,
    dif_spi_device_flash_command_t command_info);

/**
 * Get the current configuration of the indicated command info slot.
 *
 * @param spi A handle to a spi device.
 * @param slot A command info slot ID.
 * @param[out] enabled A pointer to where the current slot state can be stored.
 * @param[out] command_info If `enabled`, points to where the current command
 * configuration can be stored.
 * @return `kDifBadArg` if any pointers are NULL or `slot` is larger than the
 * number of command slots. `kDifOk` otherwise.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_get_flash_command_slot(
    dif_spi_device_handle_t *spi, uint8_t slot, dif_toggle_t *enabled,
    dif_spi_device_flash_command_t *command_info);

/**
 * Set which address bits are swapped and their values for commands that have
 * the address swap enabled.
 *
 * @param spi A handle to a spi device.
 * @param mask A bitmask indicating which address bits should be replaced.
 * @param replacement The values to swap in for the masked address bits.
 * @return `kDifBadArg` if spi is NULL, else `kDifOk`.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_set_flash_address_swap(dif_spi_device_handle_t *spi,
                                                   uint32_t mask,
                                                   uint32_t replacement);

/**
 * Set which bits are swapped and their values for commands that have
 * the first-word payload swap function enabled.
 *
 * @param spi A handle to a spi device.
 * @param mask A bitmask indicating which bits should be replaced.
 * @param replacement The values to swap in for the masked bits.
 * @return `kDifBadArg` if spi is NULL, else `kDifOk`.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_set_flash_payload_swap(dif_spi_device_handle_t *spi,
                                                   uint32_t mask,
                                                   uint32_t replacement);

/**
 * Pop the first command from the uploaded command FIFO.
 *
 * @param spi A handle to a spi device.
 * @param[out] command A pointer to where the command can be stored.
 * @return `kDifBadArg` if any pointers are NULL. `kDifUnavailable` if the FIFO
 * was empty. `kDifOk` otherwise.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_pop_flash_command_fifo(dif_spi_device_handle_t *spi,
                                                   uint8_t *command);

/**
 * Pop the first address from the uploaded address FIFO.
 *
 * @param spi A handle to a spi device.
 * @param[out] address A pointer to where the address can be stored.
 * @return `kDifBadArg` if any pointers are NULL. `kDifUnavailable` if the FIFO
 * was empty. `kDifOk` otherwise.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_pop_flash_address_fifo(dif_spi_device_handle_t *spi,
                                                   uint32_t *address);

/**
 * Read data from one of the memories associated with flash / passthrough modes.
 *
 * @param spi A handle to a spi device.
 * @param buffer_type An identifier for which memory space to read from.
 * @param offset The starting offset for read data in the memory.
 * @param length The length, in bytes, of the data to be copied.
 * @param[out] buf A pointer to the location where the data should be stored.
 * @return `kDifBadArg` is any pointers are NULL or the `buffer_type` does not
 * exist. `kDifOutOfRange` if the requested `offset` and `length` go beyond the
 * indicated `buffer_type` region. `kDifOk` otherwise.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_read_flash_buffer(
    dif_spi_device_handle_t *spi,
    dif_spi_device_flash_buffer_type_t buffer_type, uint32_t offset,
    size_t length, uint8_t *buf);

/**
 * Write data to one of the memories associated with flash / passthrough modes.
 *
 * @param spi A handle to a spi device.
 * @param buffer_type An identifier for which memory space to write to.
 * @param offset The starting offset for the write location of the data.
 * @param length The length, in bytes, of the data to be copied.
 * @param buf A pointer to the location where the data can be copied from.
 * @return `kDifBadArg` is any pointers are NULL or the `buffer_type` does not
 * exist. `kDifOutOfRange` if the requested `offset` and `length` go beyond the
 * indicated `buffer_type` region. `kDifOk` otherwise.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_write_flash_buffer(
    dif_spi_device_handle_t *spi,
    dif_spi_device_flash_buffer_type_t buffer_type, uint32_t offset,
    size_t length, const uint8_t *buf);

/**
 * Get whether the indicated command is filtered for passthrough.
 *
 * @param spi A handle to a spi device.
 * @param command The command to be queried.
 * @param[out] enabled A pointer to a location where the filter status can be
 * stored. `kDifEnabled` means the command is filtered.
 * @return `kDifBadArg` if any pointers are NULL. `kDifOk` otherwise.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_get_passthrough_command_filter(
    dif_spi_device_handle_t *spi, uint8_t command, dif_toggle_t *enabled);

/**
 * Set whether the indicated command is filtered for passthrough.
 *
 * @param spi A handle to a spi device.
 * @param command The command to have its filter status updated.
 * @param enable Whether to enable the command filter for the `command`.
 * @return `kDifBadArg` if `spi` is NULL or `enable` is invalid. `kDifOk`
 * otherwise.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_set_passthrough_command_filter(
    dif_spi_device_handle_t *spi, uint8_t command, dif_toggle_t enable);

/**
 * Set whether ALL commands are filtered for passthrough.
 *
 * Can be used for a faster initial state before using
 * `dif_spi_device_set_passthrough_command_filter` to set the filter status for
 * individual commands.
 *
 * @param spi A handle to a spi device.
 * @param enable Whether to enable the command filter for all commands.
 * @return `kDifBadArg` if `spi` is NULL or `enable` is invalid. `kDifOk`
 * otherwise.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_set_all_passthrough_command_filters(
    dif_spi_device_handle_t *spi, dif_toggle_t enable);

/**
 * Clear the busy bit for flash / passthrough modes.
 *
 * @param spi A handle to a spi device.
 * @return `kDifBadArg` if `spi` is NULL. `kDifOk` otherwise.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_clear_flash_busy_bit(dif_spi_device_handle_t *spi);

/**
 * Write the status registers for flash / passthrough modes.
 *
 * Note that the three registers are concatenated to make one 24-bit value, with
 * the LSB being the busy bit.
 *
 * @param spi A handle to a spi device.
 * @param value The value to write to the registers.
 * @return `kDifBadArg` if `spi` is NULL. `kDifOk` otherwise.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_set_flash_status_registers(
    dif_spi_device_handle_t *spi, uint32_t value);

/**
 * Get the values of the status registers for flash / passthrough modes.
 *
 * Note that the three registers are concatenated to make one 24-bit value, with
 * the LSB being the busy bit.
 *
 * @param spi A handle to a spi device.
 * @param[out] value A pointer to where to write the values of the registesr.
 * @return `kDifBadArg` if any pointer arguments are NULL. `kDifOk` otherwise.
 */
OT_WARN_UNUSED_RESULT
dif_result_t dif_spi_device_get_flash_status_registers(
    dif_spi_device_handle_t *spi, uint32_t *value);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_LIB_DIF_DIF_SPI_DEVICE_H_
