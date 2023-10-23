// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/lib/sw/device/silicon_creator/rom_patch.h"

#include <stddef.h>
#include <stdint.h>

#include "sw/device/silicon_creator/lib/drivers/ibex.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/lib/sw/device/base/bitfield.h"
#include "sw/lib/sw/device/base/hardened_memory.h"
#include "sw/lib/sw/device/runtime/hart.h"
#include "sw/lib/sw/device/silicon_creator/base/sec_mmio.h"
#include "sw/lib/sw/device/silicon_creator/rom_print.h"
#include "sw/lib/sw/device/silicon_creator/sigverify/sigverify.h"

#include "hw/top_darjeeling/sw/autogen/top_darjeeling.h"
#include "otp_ctrl_regs.h"  // Generated.

#define ROM_PATCH_BITFIELD(m, i) ((bitfield_field32_t){.mask = m, .index = i})
static const bitfield_field32_t kRomPatchLockValid = ROM_PATCH_BITFIELD(0xf, 0);
static const bitfield_field32_t kRomPatchSizeWords =
    ROM_PATCH_BITFIELD(0xffff, 8);
static const bitfield_field32_t kRomPatchRevision =
    ROM_PATCH_BITFIELD(0xff, 24);

static const bitfield_field32_t kRomPatchMatchMBase =
    ROM_PATCH_BITFIELD(0x7ffffff, 0);
static const bitfield_field32_t kRomPatchMatchPSize =
    ROM_PATCH_BITFIELD(0xf, 27);
static const bitfield_field32_t kRomPatchMatchLocked =
    ROM_PATCH_BITFIELD(0x1, 31);

enum {
  kOtpBase = TOP_DARJEELING_OTP_CTRL_CORE_BASE_ADDR,
  kSwConfig = OTP_CTRL_SW_CFG_WINDOW_REG_OFFSET,
};

enum {
  kRomPatchBaseAddr = OTP_CTRL_PARAM_ROM_PATCH_OFFSET,
  kRomPatchMaxAddr = kRomPatchBaseAddr + OTP_CTRL_PARAM_ROM_PATCH_SIZE,
  kRomPatchRegionHeaderSizeBytes = sizeof((struct rom_patch){0}.header),
  kRomPatchRegionMatchTableSizeBytes = sizeof((struct rom_patch){0}.table),
  kRomPatchRegionSignatureSizeBytes = kSigVerifyRsaNumBytes,
  /* Preamble is the patch header and the complete match table. */
  kRomPatchRegionPreambleSizeBytes =
      kRomPatchRegionHeaderSizeBytes + kRomPatchRegionMatchTableSizeBytes,
  /* The patch code envelope is the preamble and the signature. */
  kRomPatchRegionEnvelopeSizeBytes =
      kRomPatchRegionPreambleSizeBytes + kRomPatchRegionSignatureSizeBytes,
};

static inline bool rom_patch_lock_valid(uint32_t patch_header) {
  return bitfield_field32_read(patch_header, kRomPatchLockValid) ==
         kMultiBitBool4True;
}

static inline uint8_t rom_patch_revision(uint32_t patch_header) {
  return (uint8_t)bitfield_field32_read(patch_header, kRomPatchRevision);
}

static inline uint16_t rom_patch_size_words(uint32_t patch_header) {
  return (uint16_t)bitfield_field32_read(patch_header, kRomPatchSizeWords);
}

static inline size_t rom_patch_code_size_words(const rom_patch_t *patch) {
  HARDENED_CHECK_NE(patch, NULL);

  uint32_t patch_size_bytes =
      (uint32_t)(rom_patch_size_words(patch->header) << 2);
  HARDENED_CHECK_GT(patch_size_bytes, kRomPatchRegionEnvelopeSizeBytes);

  return (patch_size_bytes - kRomPatchRegionEnvelopeSizeBytes) >> 2;
}

static inline size_t rom_patch_region_enabled(
    const rom_patch_match_regs_t *match) {
  HARDENED_CHECK_NE(match, NULL);
  return match->m_base != 0 && match->r_base != 0;
}

static inline bool rom_patch_region_locked(
    const rom_patch_match_regs_t *match) {
  HARDENED_CHECK_NE(match, NULL);
  return bitfield_field32_read(match->m_base, kRomPatchMatchLocked) == 1;
}

static inline size_t rom_patch_region_size_bytes(
    const rom_patch_match_regs_t *match) {
  HARDENED_CHECK_NE(match, NULL);
  return bitfield_field32_read(match->m_base, kRomPatchMatchPSize) << 2;
}

static inline uint32_t rom_patch_region_r_base(
    const rom_patch_match_regs_t *match) {
  HARDENED_CHECK_NE(match, NULL);
  return match->r_base;
}

static inline uint32_t rom_patch_region_m_base(
    const rom_patch_match_regs_t *match) {
  HARDENED_CHECK_NE(match, NULL);
  return bitfield_field32_read(match->m_base, kRomPatchMatchMBase);
}

static inline bool rom_patch_addr_valid(const uintptr_t patch_addr) {
  return (patch_addr != kRomPatchInvalidAddr &&
          patch_addr >= kRomPatchBaseAddr && patch_addr < kRomPatchMaxAddr);
}

bool rom_patch_valid(const uintptr_t patch_addr) {
  /*
   * For a patch to be valid:
   * - The patch address must be valid.
   * - The patch size must be strictly larger than the patch envelope, for the
   *   patch code to be at least one word long.
   */
  return (rom_patch_addr_valid(patch_addr) &&
          (rom_patch_size_words(otp_read32(patch_addr)) >
           kRomPatchRegionEnvelopeSizeBytes >> 2));
}

OT_WARN_UNUSED_RESULT uintptr_t rom_patch_latest(uintptr_t before_patch_addr) {
  uintptr_t next_patch_addr = kRomPatchBaseAddr;
  uintptr_t latest_patch_addr = kRomPatchInvalidAddr;
  size_t current_patch_size_words = 0;
  uint8_t current_patch_revision = 0;
  uint8_t latest_patch_revision = 0, max_patch_revision = UINT8_MAX;
  uint32_t patch_header;

  /* If valid, set the max revision to the patch before */
  if (before_patch_addr != kRomPatchInvalidAddr) {
    if (!rom_patch_valid(before_patch_addr)) {
      return kRomPatchInvalidAddr;
    }

    max_patch_revision = rom_patch_revision(before_patch_addr);
  }

  do {
    patch_header = otp_read32(next_patch_addr);
    current_patch_size_words = rom_patch_size_words(patch_header);
    current_patch_revision = rom_patch_revision(patch_header);

    /*
     * Check if the current patch is better than the latest, i.e.:
     * - It is valid, i.e. it's been fully programmed.
     * - It has a strictly higher revision number.
     * - It has a lower or equal revision number than before_patch.
     */
    if (rom_patch_lock_valid(patch_header) &&
        (current_patch_revision > latest_patch_revision) &&
        (current_patch_revision <= max_patch_revision)) {
      // Found a better patch, let's keep it.
      latest_patch_addr = next_patch_addr;
      latest_patch_revision = current_patch_revision;
    }

    next_patch_addr += current_patch_size_words * 4;
  } while (current_patch_size_words > 0 && next_patch_addr < kRomPatchMaxAddr);

  return latest_patch_addr;
}

static OT_WARN_UNUSED_RESULT rom_error_t rom_patch_verify_sig(
    const rom_patch_t *patch, const hmac_digest_t *patch_digest) {
  /*
   * TODO: Verify that the loaded code matches the OTP signature.
   */
  return kErrorOk;
}

static OT_WARN_UNUSED_RESULT rom_error_t
rom_patch_remap(const rom_patch_t *patch) {
  for (uint32_t i = 0; i < RV_CORE_IBEX_PARAM_NUM_REGIONS; i++) {
    const rom_patch_match_regs_t *match = &patch->table[i];
    // If patch is not enabled, skip it.
    if (!rom_patch_region_enabled(match)) {
      continue;
    }

    uint32_t patch_size_bytes = (uint32_t)(rom_patch_region_size_bytes(match));
    uint32_t m_base = rom_patch_region_m_base(match);
    uint32_t r_base = rom_patch_region_r_base(match);

    HARDENED_RETURN_IF_ERROR(
        ibex_addr_remap_set(i, m_base, r_base, patch_size_bytes));
    if (rom_patch_region_locked(match)) {
      HARDENED_RETURN_IF_ERROR(ibex_addr_remap_lock(i));
    }

    OT_DISCARD(rom_printf(
        "Configured Ibex remapping 0x%x->0x%x (0x%x bytes) Locked 0x%x\n",
        m_base, r_base, patch_size_bytes, rom_patch_region_locked(match)));
  }

  return kErrorOk;
}

OT_WARN_UNUSED_RESULT rom_error_t
rom_patch_apply(const uintptr_t patch_addr, hmac_digest_t *const patch_digest) {
  size_t patch_code_offset = kRomPatchRegionPreambleSizeBytes;
  uint32_t patch_preamble_bytes[kRomPatchRegionPreambleSizeBytes >> 2];
  rom_patch_t *patch;

  hmac_sha256_init();

  // Read the patch preamble from OTP.
  otp_read(patch_addr, patch_preamble_bytes,
           kRomPatchRegionPreambleSizeBytes >> 2);
  patch = (rom_patch_t *)(patch_preamble_bytes);

  // The first header byte (LOCK_VALID & PROGRAM_START) is not signed.
  hmac_sha256_update(patch_preamble_bytes + 1,
                     kRomPatchRegionPreambleSizeBytes - 1);

  // The patch code size must not be 0.
  size_t patch_code_size_bytes = rom_patch_code_size_words(patch) << 2;
  HARDENED_CHECK_NE(patch_code_size_bytes, 0);

  // The remapping base address is the first entry in the match table.
  const rom_patch_match_regs_t *match = &patch->table[0];
  uint32_t remap_addr = rom_patch_region_r_base(match);

  /*
   * Read the whole patch section, dword by dword, and copy it to the
   * remapped address.
   */
  for (size_t i = 0; i < patch_code_size_bytes; i += 4) {
    uint32_t insn = otp_read32(patch_addr + patch_code_offset + i);
    hmac_sha256_update(&insn, 4);

    sec_mmio_write32(remap_addr + i, insn);
  }

  hmac_sha256_final(patch_digest);

  // Verify the patch signature
  HARDENED_RETURN_IF_ERROR(rom_patch_verify_sig(patch, patch_digest));

  // Remap and enable each patches
  HARDENED_RETURN_IF_ERROR(rom_patch_remap(patch));

  return kErrorOk;
}
