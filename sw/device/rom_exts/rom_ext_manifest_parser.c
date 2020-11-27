// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/rom_exts/rom_ext_manifest_parser.h"

#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/mmio.h"
#include "sw/device/rom_exts/manifest.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

const rom_ext_manifest_slot_t kRomExtManifestSlotA =
    TOP_EARLGREY_EFLASH_BASE_ADDR;
const rom_ext_manifest_slot_t kRomExtManifestSlotB =
    TOP_EARLGREY_EFLASH_BASE_ADDR + (TOP_EARLGREY_EFLASH_SIZE_BYTES / 2);

_Static_assert((TOP_EARLGREY_EFLASH_SIZE_BYTES % 2) == 0,
               "Flash size is not divisible by 2");

rom_ext_manifest_t rom_ext_get_parameters(rom_ext_manifest_slot_t slot) {
  if (kRomExtManifestSlotA) {
    return (rom_ext_manifest_t){
        .base_addr = mmio_region_from_addr(kRomExtManifestSlotA),
        .slot = kRomExtManifestSlotA,
    };
  } else {
    return (rom_ext_manifest_t){
        .base_addr = mmio_region_from_addr(kRomExtManifestSlotB),
        .slot = kRomExtManifestSlotB,
    };
  }
}

uint32_t rom_ext_get_identifier(rom_ext_manifest_t params) {
  return mmio_region_read32(params.base_addr,
                            ROM_EXT_MANIFEST_IDENTIFIER_OFFSET);
}

bool rom_ext_get_signature(rom_ext_manifest_t params,
                           rom_ext_signature_t *dst) {
  if (dst == NULL) {
    return false;
  }

  mmio_region_memcpy_from_mmio32(params.base_addr,
                                 ROM_EXT_IMAGE_SIGNATURE_OFFSET, &dst->data[0],
                                 ROM_EXT_IMAGE_SIGNATURE_SIZE_BYTES);

  return true;
}

rom_ext_ranges_t rom_ext_get_ranges(rom_ext_manifest_t params) {
  uintptr_t image_length =
      mmio_region_read32(params.base_addr, ROM_EXT_IMAGE_LENGTH_OFFSET);

  rom_ext_ranges_t ranges = {
      .image_start = params.slot,
      .signed_area_start = params.slot + ROM_EXT_SIGNED_AREA_START_OFFSET,
      .image_end = params.slot + image_length,
  };

  return ranges;
}

uint32_t rom_ext_get_version(rom_ext_manifest_t params) {
  return mmio_region_read32(params.base_addr, ROM_EXT_IMAGE_VERSION_OFFSET);
}

uint64_t rom_ext_get_timestamp(rom_ext_manifest_t params) {
  uint32_t timestamp_low =
      mmio_region_read32(params.base_addr, ROM_EXT_IMAGE_TIMESTAMP_OFFSET);

  ptrdiff_t offset_high = ROM_EXT_IMAGE_TIMESTAMP_OFFSET + sizeof(uint32_t);
  uint32_t timestamp_high = mmio_region_read32(params.base_addr, offset_high);

  return ((uint64_t)timestamp_high << 32) | timestamp_low;
}

uint32_t rom_ext_get_signature_key_public_exponent(rom_ext_manifest_t params) {
  return mmio_region_read32(params.base_addr,
                            ROM_EXT_SIGNATURE_KEY_PUBLIC_EXPONENT_OFFSET);
}

uint32_t rom_ext_get_usage_constraints(rom_ext_manifest_t params) {
  return mmio_region_read32(params.base_addr, ROM_EXT_USAGE_CONSTRAINTS_OFFSET);
}

bool rom_ext_get_peripheral_lockdown_info(rom_ext_manifest_t params,
                                          rom_ext_lockdown_info_t *dst) {
  if (dst == NULL) {
    return false;
  }

  mmio_region_memcpy_from_mmio32(
      params.base_addr, ROM_EXT_PERIPHERAL_LOCKDOWN_INFO_OFFSET, &dst->data[0],
      ROM_EXT_PERIPHERAL_LOCKDOWN_INFO_SIZE_BYTES);

  return true;
}

bool rom_ext_get_signature_key_modulus(rom_ext_manifest_t params,
                                       rom_ext_signature_key_modulus_t *dst) {
  if (dst == NULL) {
    return false;
  }

  mmio_region_memcpy_from_mmio32(
      params.base_addr, ROM_EXT_SIGNATURE_KEY_MODULUS_OFFSET, &dst->data[0],
      ROM_EXT_SIGNATURE_KEY_MODULUS_SIZE_BYTES);

  return true;
}

bool rom_ext_get_extension(rom_ext_manifest_t params, rom_ext_extension_id_t id,
                           rom_ext_extension_t *extension) {
  if (extension == NULL) {
    return false;
  }

  uint32_t offset = 0;
  uint32_t checksum = 0;
  switch (id) {
    case kRomExtExtensionId0:
      offset = ROM_EXT_EXTENSION0_OFFSET_OFFSET;
      checksum = ROM_EXT_EXTENSION0_CHECKSUM_OFFSET;
      break;
    case kRomExtExtensionId1:
      offset = ROM_EXT_EXTENSION1_OFFSET_OFFSET;
      checksum = ROM_EXT_EXTENSION1_CHECKSUM_OFFSET;
      break;
    case kRomExtExtensionId2:
      offset = ROM_EXT_EXTENSION2_OFFSET_OFFSET;
      checksum = ROM_EXT_EXTENSION2_CHECKSUM_OFFSET;
      break;
    case kRomExtExtensionId3:
      offset = ROM_EXT_EXTENSION3_OFFSET_OFFSET;
      checksum = ROM_EXT_EXTENSION3_CHECKSUM_OFFSET;
      break;
    default:
      return false;
  }

  uint32_t extension_offset = mmio_region_read32(params.base_addr, offset);

  extension->address = (void *)(extension_offset + params.slot);
  extension->checksum = mmio_region_read32(params.base_addr, checksum);

  return true;
}

uintptr_t rom_ext_get_interrupt_vector(rom_ext_manifest_t params) {
  uintptr_t vector_addr = params.slot + ROM_EXT_INTERRUPT_VECTOR_OFFSET;

  // A valid value for `mtvec` contains:
  //
  // - The most-significant 30 bits of the value are the most-significant 30
  //   bits of the interrupt vector address.
  // - The least-significant 2 bits of the value must be `0b01` to encode
  //   vectored interrupts, which we want.
  //
  // One additional restriction is that Ibex wants the address to be 256-byte
  // aligned. We enforce that in the definition of
  // ROM_EXT_INTERRUPT_VECTOR_OFFSET;

  return (vector_addr & ~0x3) | 0x1;
}

uintptr_t rom_ext_get_entry(rom_ext_manifest_t params) {
  return params.slot + ROM_EXT_ENTRY_POINT_OFFSET;
}
