// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_ROM_EXTS_ROM_EXT_MANIFEST_PARSER_H_
#define OPENTITAN_SW_DEVICE_ROM_EXTS_ROM_EXT_MANIFEST_PARSER_H_

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/mmio.h"
#include "sw/device/rom_exts/manifest.h"

/**
 * @file
 * @brief Parser for the ROM_EXT Image Format
 *
 * This parser is intended to parse in-memory ROM_EXT images, from either Slot A
 * or Slot B. The fields it is parsing are defined in
 * `sw/device/rom_exts/manifest.md` and `sw/device_rom_exts/manifest.hjson`.
 *
 * This parser does minimal validity checking of the returned values, which must
 * always be checked by the caller to ensure do not contain incorrect or
 * insecure values.
 */

#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

/**
 * ROM Extension manifest slot type.
 */
typedef uintptr_t rom_ext_manifest_slot_t;

/**
 * ROM Extension manifest slots base addresses.
 *
 * These are intended to be used as an input parameter to
 * `rom_ext_parameters_get`.
 */
extern const rom_ext_manifest_slot_t kRomExtManifestSlotA;
extern const rom_ext_manifest_slot_t kRomExtManifestSlotB;

/**
 * ROM Extension parameters required for the manifest parsing.
 */
typedef struct rom_ext_manifest {
  /**
   * Base address of the manifest in memory.
   */
  mmio_region_t base_addr;
  rom_ext_manifest_slot_t slot;
} rom_ext_manifest_t;

/**
 * ROM Extension Memory Extents.
 *
 * This information is needed for calculating the signature of the entire
 * ROM_EXT.
 */
typedef struct rom_ext_ranges {
  /**
   * Image Start Address
   */
  uintptr_t image_start;
  /**
   * Signed Area Start Address
   *
   * Not all of a ROM_EXT is signed. This is the address of the first signed
   * byte of the ROM_EXT, in memory.
   */
  uintptr_t signed_area_start;
  /**
   * Image End Address
   *
   * This is also the Signed Area End Address.
   *
   * This is parsed from user-provided data, and must be checked to ensure it
   * the value is within the expected range, and has not overflowed.
   */
  uintptr_t image_end;
} rom_ext_ranges_t;

/**
 * ROM Extension image signature.
 */
typedef struct rom_ext_signature {
  uint32_t data[ROM_EXT_IMAGE_SIGNATURE_SIZE_WORDS];
} rom_ext_signature_t;

/**
 * ROM Extension lockdown information.
 *
 * TODO - probably would eventually become an internal type, and there will
 *        be another public type with more finely parsed information.
 */
typedef struct rom_ext_lockdown_info {
  uint32_t data[ROM_EXT_PERIPHERAL_LOCKDOWN_INFO_SIZE_WORDS];
} rom_ext_lockdown_info_t;

/**
 * ROM Extension Signature Key Modulus.
 */
typedef struct rom_ext_signature_key_modulus {
  uint32_t data[ROM_EXT_SIGNATURE_KEY_MODULUS_SIZE_WORDS];
} rom_ext_signature_key_modulus_t;

/**
 * ROM Extension image extension IDs.
 */
typedef enum rom_ext_extension_id {
  /**
   * Image extension 0.
   */
  kRomExtExtensionId0 = 0,
  /**
   * Image extension 1.
   */
  kRomExtExtensionId1,
  /**
   * Image extension 2.
   */
  kRomExtExtensionId2,
  /**
   * Image extension 3.
   */
  kRomExtExtensionId3,
} rom_ext_extension_id_t;

/**
 * ROM Extension image extension.
 */
typedef struct rom_ext_extension {
  /**
   * Image extension address in memory.
   */
  void *address;
  /**
   * Image extension checksum.
   */
  uint32_t checksum;
} rom_ext_extension_t;

/**
 * Creates the ROM extension manifest parameters.
 *
 * Required for all ROM Extension manifest parser API.
 *
 * @param slot ROM Extension manifest slot base address.
 * @return `rom_ext_manifest_t`.
 */
rom_ext_manifest_t rom_ext_get_parameters(rom_ext_manifest_slot_t slot);

/**
 * Retrieves the ROM_EXT identifier.
 *
 * The memory address where ROM_EXT identifier field resides, is relative.
 *
 * @param params Parameters required for manifest parsing.
 * @return ROM_EXT identifier.
 */
uint32_t rom_ext_get_identifier(rom_ext_manifest_t params);

/**
 * Retrieves the ROM_EXT signature.
 *
 * The memory address where ROM_EXT identifier field resides, is relative.
 *
 * @param params Parameters required for manifest parsing.
 * @param dst The destination address where the signature is copied to.
 * @return `true` on success, `false` on failure.
 */
bool rom_ext_get_signature(rom_ext_manifest_t params, rom_ext_signature_t *dst);

/**
 * Retrieves the ROM_EXT image address ranges.
 *
 * This uses the ROM_EXT image length field, and the offset of the signed area.
 *
 * The results provided are absolute addresses, not relative.
 *
 * This assumes that the slot identified by `params` is a valid ROM_EXT, and
 * does not check the ROM_EXT image identifier.
 *
 * @param params Parameters required to identify the ROM_EXT.
 * @return The address ranges of the specific ROM_EXT.
 */
rom_ext_ranges_t rom_ext_get_ranges(rom_ext_manifest_t params);

/**
 * Retrieves the ROM_EXT image version.
 *
 * The memory address where ROM_EXT image version field resides, is relative.
 *
 * @param params Parameters required for manifest parsing.
 * @return ROM_EXT image version.
 */
uint32_t rom_ext_get_version(rom_ext_manifest_t params);

/**
 * Retrieves the ROM_EXT image timestamp.
 *
 * The memory address where ROM_EXT image timestamp field resides, is relative.
 *
 * @param params Parameters required for manifest parsing.
 * @return ROM_EXT image timestamp.
 */
uint64_t rom_ext_get_timestamp(rom_ext_manifest_t params);

/**
 * Retrieves the ROM_EXT Signature Key Public Exponent.
 *
 * The memory address where ROM_EXT exponent field resides, is relative.
 *
 * @param params Parameters required for manifest parsing.
 * @return ROM_EXT Signature Key Public Exponent.
 */
uint32_t rom_ext_get_signature_key_public_exponent(rom_ext_manifest_t params);

/**
 * Retrieves the ROM_EXT usage constraints.
 *
 * The memory address where ROM_EXT usage constraints field resides, is
 * relative.
 *
 * @param params Parameters required for manifest parsing.
 * @return ROM_EXT usage constraints.
 */
uint32_t rom_ext_get_usage_constraints(rom_ext_manifest_t params);

/**
 * Retrieves the ROM_EXT lockdown info.
 *
 * The memory address where ROM_EXT lockdown info field resides, is relative.
 *
 * @param params Parameters required for manifest parsing.
 * @param dst The destination address where the lockdown info is copied to.
 * @return `true` on success, `false` on failure.
 */
bool rom_ext_get_peripheral_lockdown_info(rom_ext_manifest_t params,
                                          rom_ext_lockdown_info_t *dst);

/**
 * Retrieves the ROM_EXT Signature Key Modulus.
 *
 * The memory address where ROM_EXT key modulus field resides, is relative.
 *
 * @param params Parameters required for manifest parsing.
 * @param dst The destination address where the key modulus is copied to.
 * @return `true` on success, `false` on failure.
 */
bool rom_ext_get_signature_key_modulus(rom_ext_manifest_t params,
                                       rom_ext_signature_key_modulus_t *dst);

/**
 * Retrieves the ROM_EXT image extension specified in `id`.
 *
 * The memory address where ROM_EXT image extension information fields reside,
 * is relative.
 *
 * @param params Parameters required for manifest parsing.
 * @param id Extension identifier.
 * @param extension Parsed `rom_ext_extension_t` output.
 * @return `true` on success, `false` on failure.
 */
bool rom_ext_get_extension(rom_ext_manifest_t params, rom_ext_extension_id_t id,
                           rom_ext_extension_t *extension);

/**
 * Calculates the ROM_EXT interrupt vector value.
 *
 * This value is based upon the absolute address of the ROM_EXT interrupt
 * vector, for this particular ROM_EXT.
 *
 * The value returned does not need extra processing to be used for vectored
 * interrupts in Ibex - the least significant two bits will have the correct
 * value.
 *
 * @param params Parameters required for manifest parsing.
 * @return The value to write to the `mtvec` RISC-V CSR.
 */
uintptr_t rom_ext_get_interrupt_vector(rom_ext_manifest_t params);

/**
 * Calculates the ROM_EXT image code entry point.
 *
 * @param params Parameters required for manifest parsing.
 * @return The absolute address to jump to to begin execution of the ROM_EXT.
 */
uintptr_t rom_ext_get_entry(rom_ext_manifest_t params);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_ROM_EXTS_ROM_EXT_MANIFEST_PARSER_H_
