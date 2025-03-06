// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/rom_ext/rom_ext.h"

#include "sw/device/lib/arch/device.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/stdasm.h"
#include "sw/device/lib/crypto/drivers/entropy.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/base/boot_measurements.h"
#include "sw/device/silicon_creator/lib/base/chip.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/base/util.h"
#include "sw/device/silicon_creator/lib/boot_data.h"
#include "sw/device/silicon_creator/lib/boot_log.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_empty.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_header.h"
#include "sw/device/silicon_creator/lib/boot_svc/boot_svc_msg.h"
#include "sw/device/silicon_creator/lib/cert/cdi_0.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/cdi_1.h"  // Generated.
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/cert/dice.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/ast.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/ibex.h"
#include "sw/device/silicon_creator/lib/drivers/keymgr.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/otp.h"
#include "sw/device/silicon_creator/lib/drivers/pinmux.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rnd.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/silicon_creator/lib/epmp_state.h"
#include "sw/device/silicon_creator/lib/keymgr_binding_value.h"
#include "sw/device/silicon_creator/lib/manifest.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/lib/ownership/ownership.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_activate.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_unlock.h"
#include "sw/device/silicon_creator/lib/shutdown.h"
#include "sw/device/silicon_creator/lib/sigverify/ecdsa_p256_key.h"
#include "sw/device/silicon_creator/lib/sigverify/rsa_verify.h"
#include "sw/device/silicon_creator/lib/sigverify/sigverify.h"
#include "sw/device/silicon_creator/lib/sigverify/sphincsplus/verify.h"
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"
#include "sw/device/silicon_creator/rom_ext/rescue.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_boot_policy_ptrs.h"
#include "sw/device/silicon_creator/rom_ext/rom_ext_epmp.h"
#include "sw/device/silicon_creator/rom_ext/sigverify_keys.h"

#include "flash_ctrl_regs.h"                          // Generated.
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"  // Generated.
#include "sram_ctrl_regs.h"                           // Generated.

static_assert(kCertX509Asn1SerialNumberSizeInBytes <= kHmacDigestNumBytes,
              "The ASN.1 encoded X.509 serial number field should be <= the "
              "size of a SHA256 digest.");

// Useful constants for flash sizes and ROM_EXT locations.
enum {
  kFlashBankSize = FLASH_CTRL_PARAM_REG_PAGES_PER_BANK,
  kFlashPageSize = FLASH_CTRL_PARAM_BYTES_PER_PAGE,
  kFlashTotalSize = 2 * kFlashBankSize,

  kRomExtSizeInPages = CHIP_ROM_EXT_SIZE_MAX / kFlashPageSize,
  kRomExtAStart = 0 / kFlashPageSize,
  kRomExtAEnd = kRomExtAStart + kRomExtSizeInPages,
  kRomExtBStart = kFlashBankSize + kRomExtAStart,
  kRomExtBEnd = kRomExtBStart + kRomExtSizeInPages,
};

// Declaration for the ROM_EXT manifest start address, populated by the linker
extern char _rom_ext_start_address[];
// Declaration for the chip_info structure stored in ROM.
extern const char _chip_info_start[];

// Life cycle state of the chip.
lifecycle_state_t lc_state = kLcStateProd;

// Owner configuration details parsed from the onwer info pages.
owner_config_t owner_config;

// Owner application keys.
owner_application_keyring_t keyring;

// Verifying key index
size_t verify_key;

// ePMP regions for important address spaces.
const epmp_region_t kRamRegion = {
    .start = TOP_EARLGREY_RAM_MAIN_BASE_ADDR,
    .end = TOP_EARLGREY_RAM_MAIN_BASE_ADDR + TOP_EARLGREY_RAM_MAIN_SIZE_BYTES,
};

const epmp_region_t kMmioRegion = {
    .start = TOP_EARLGREY_MMIO_BASE_ADDR,
    .end = TOP_EARLGREY_MMIO_BASE_ADDR + TOP_EARLGREY_MMIO_SIZE_BYTES,
};

const epmp_region_t kRvDmRegion = {
    .start = TOP_EARLGREY_RV_DM_MEM_BASE_ADDR,
    .end = TOP_EARLGREY_RV_DM_MEM_BASE_ADDR + TOP_EARLGREY_RV_DM_MEM_SIZE_BYTES,
};

const epmp_region_t kFlashRegion = {
    .start = TOP_EARLGREY_EFLASH_BASE_ADDR,
    .end = TOP_EARLGREY_EFLASH_BASE_ADDR + TOP_EARLGREY_EFLASH_SIZE_BYTES,
};

// TODO(lowRISC/opentitan:#24368): Move all `dice_chain` prefixed functions to
// dice_chain library.

enum {
  /**
   * The size of the scratch buffer that is large enough for constructing the
   * CDI certs.
   */
  kScratchCertSizeBytes =
      (kCdi0MaxCertSizeBytes > kCdi1MaxCertSizeBytes ? kCdi0MaxCertSizeBytes
                                                     : kCdi1MaxCertSizeBytes),
};

/**
 * Defines a class for parsing and building the DICE cert chain.
 *
 * All of the fields in this struct should be considered private, and users
 * should call the public `dice_chain_*` functions instead.
 */
typedef struct dice_chain {
  /**
   * RAM buffer that mirrors the DICE cert chain in a flash page.
   */
  uint8_t data[kFlashPageSize];

  /**
   * Indicate whether `data` needs to be written back to flash.
   */
  hardened_bool_t data_dirty;

  /**
   * The amount of bytes in `data` that has been processed.
   */
  size_t tail_offset;

  /**
   * Indicate the info page currently buffered in `data`.
   * This is used to skip unnecessary read ops.
   */
  const flash_ctrl_info_page_t *info_page;

  /**
   * Id pair which points to the endorsement and cert ids below.
   */
  cert_key_id_pair_t key_ids;

  /**
   * Public key id for signing endorsement cert.
   */
  hmac_digest_t endorsement_pubkey_id;

  /**
   * Subject public key id of the current cert.
   */
  hmac_digest_t subject_pubkey_id;

  /**
   * Subject public key contents of the current cert.
   */
  ecdsa_p256_public_key_t subject_pubkey;

  /**
   * Scratch buffer for constructing CDI certs.
   */
  uint8_t scratch_cert[kScratchCertSizeBytes];

  /**
   * The current tlv cert the builder is processing.
   */
  perso_tlv_cert_obj_t cert_obj;

  /**
   * Indicate whether the `cert_obj` is valid for the current `subject_pubkey`.
   */
  hardened_bool_t cert_valid;

} dice_chain_t;

static dice_chain_t dice_chain;

/**
 * Initialize the dice chain builder with data from the flash pages.
 *
 * @return errors encountered during the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_chain_init(void);

/**
 * Prepare the UDS key and check the UDS certificate.
 *
 * @return errors encountered during the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_chain_attestation_silicon(void);

/**
 * Check the CDI_0 certificate and regenerate if invalid.
 *
 * @param rom_ext_measurement Pointer to the measurements to attest.
 * @param rom_ext_manifest Pointer to the current rom_ext manifest.
 * @return errors encountered during the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_chain_attestation_creator(
    keymgr_binding_value_t *rom_ext_measurement,
    const manifest_t *rom_ext_manifest);

/**
 * Check the CDI_1 certificate and regenerate if invalid.
 *
 * @param boot_data Pointer to the boot_data struct with ownership info.
 * @param owner_measurement Pointer to the measurements to attest.
 * @param owner_manifest Pointer to the owner SW manifest to be boot.
 * @return errors encountered during the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_chain_attestation_owner(
    const boot_data_t *boot_data, keymgr_binding_value_t *owner_measurement,
    const manifest_t *owner_manifest);

/**
 * Write back the certificate chain to flash if changed.
 *
 * @return errors encountered during the operation.
 */
OT_WARN_UNUSED_RESULT
rom_error_t dice_chain_flush_flash(void);

OT_WARN_UNUSED_RESULT
static rom_error_t rom_ext_irq_error(void) {
  uint32_t mcause;
  CSR_READ(CSR_REG_MCAUSE, &mcause);

  // TODO(opentitan#22947): Remove this debug print prior to a formal release.
  uint32_t mepc, mtval;
  CSR_READ(CSR_REG_MEPC, &mepc);
  CSR_READ(CSR_REG_MTVAL, &mtval);
  dbg_printf("MCAUSE=%x MEPC=%x MTVAL=%x\r\n", mcause, mepc, mtval);

  // Shuffle the mcause bits into the uppermost byte of the word and report
  // the cause as kErrorRomExtInterrupt.
  // Based on the ibex verilog, it appears that the most significant bit
  // indicates whether the cause is an exception (0) or external interrupt (1),
  // and the 5 least significant bits indicate which exception/interrupt.
  //
  // Preserve the MSB and shift the 7 LSBs into the upper byte.
  // (we preserve 7 instead of 5 because the verilog hardcodes the unused bits
  // as zero and those would be the next bits used should the number of
  // interrupt causes increase).
  mcause = (mcause & 0x80000000) | ((mcause & 0x7f) << 24);
  return kErrorRomExtInterrupt + mcause;
}

OT_WARN_UNUSED_RESULT
static uint32_t rom_ext_current_slot(void) {
  uint32_t pc = ibex_addr_remap_get(0);
  if (pc == 0) {
    // If the remap window has address zero, we're running from flash and we can
    // simply read the program counter.
    asm("auipc %[pc], 0;" : [pc] "=r"(pc));
  }

  const uint32_t kFlashSlotA = TOP_EARLGREY_FLASH_CTRL_MEM_BASE_ADDR;
  const uint32_t kFlashSlotB =
      kFlashSlotA + TOP_EARLGREY_FLASH_CTRL_MEM_SIZE_BYTES / 2;
  const uint32_t kFlashSlotEnd =
      kFlashSlotA + TOP_EARLGREY_FLASH_CTRL_MEM_SIZE_BYTES;
  uint32_t side = 0;
  if (pc >= kFlashSlotA && pc < kFlashSlotB) {
    // Running in Slot A.
    side = kBootSlotA;
  } else if (pc >= kFlashSlotB && pc < kFlashSlotEnd) {
    // Running in Slot B.
    side = kBootSlotB;
  } else {
    // Not running in flash: impossible.
    HARDENED_TRAP();
  }
  return side;
}

OT_WARN_UNUSED_RESULT
const manifest_t *rom_ext_manifest(void) {
  uint32_t pc = 0;
  asm("auipc %[pc], 0;" : [pc] "=r"(pc));
  const uint32_t kFlashHalf = TOP_EARLGREY_FLASH_CTRL_MEM_SIZE_BYTES / 2;
  // Align the PC to the current flash side.  The ROM_EXT must be the first
  // entity in each flash side, so this alignment is the manifest address.
  pc &= ~(kFlashHalf - 1);
  return (const manifest_t *)pc;
}

void rom_ext_check_rom_expectations(void) {
  // Check the ePMP state.
  SHUTDOWN_IF_ERROR(epmp_state_check());
  // Check sec_mmio expectations.
  // We don't check the counters since we don't want to tie ROM_EXT to a
  // specific ROM version.
  sec_mmio_check_values(rnd_uint32());
}

OT_WARN_UNUSED_RESULT
static rom_error_t rom_ext_init(boot_data_t *boot_data) {
  sec_mmio_next_stage_init();
  lc_state = lifecycle_state_get();
  pinmux_init();
  // Configure UART0 as stdout.
  uart_init(kUartNCOValue);

  // TODO: Verify ePMP expectations from ROM.

  // Check that the retention RAM is initialized.
  // TODO(lowrisc#22387): Check if return-if-error here is a potential
  // boot-loop.
  HARDENED_RETURN_IF_ERROR(retention_sram_check_version());

  // Get the boot_data record
  HARDENED_RETURN_IF_ERROR(boot_data_read(lc_state, boot_data));

  return kErrorOk;
}

void rom_ext_sram_exec(owner_sram_exec_mode_t mode) {
  switch (mode) {
    case kOwnerSramExecModeEnabled:
      // In enabled mode, we do not lock the register so owner code can disable
      // SRAM exec at some later time.
      HARDENED_CHECK_EQ(mode, kOwnerSramExecModeEnabled);
      sec_mmio_write32(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR +
                           SRAM_CTRL_EXEC_REG_OFFSET,
                       kMultiBitBool4True);
      break;
    case kOwnerSramExecModeDisabled:
      // In disabled mode, we do not lock the register so owner code can enable
      // SRAM exec at some later time.
      HARDENED_CHECK_EQ(mode, kOwnerSramExecModeDisabled);
      sec_mmio_write32(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR +
                           SRAM_CTRL_EXEC_REG_OFFSET,
                       kMultiBitBool4False);
      break;
    case kOwnerSramExecModeDisabledLocked:
    default:
      // In disabled locked mode, we lock the register so the mode cannot be
      // changed.
      sec_mmio_write32(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR +
                           SRAM_CTRL_EXEC_REG_OFFSET,
                       kMultiBitBool4False);
      sec_mmio_write32(TOP_EARLGREY_SRAM_CTRL_MAIN_REGS_BASE_ADDR +
                           SRAM_CTRL_EXEC_REGWEN_REG_OFFSET,
                       0);
      break;
  }
}

// A version of spx_verify that is tailored to the ROM_EXT needs.
// In particular:
//   - We don't care about the OTP setting for SPX+ in the ROM_EXT.
//   - We don't care about flash_exec in the ROM_EXT.
//   - We have a different series of algorithm identifier values to accommodate
//     hybrid signature schemes.
OT_WARN_UNUSED_RESULT
static rom_error_t rom_ext_spx_verify(
    const sigverify_spx_signature_t *signature, const sigverify_spx_key_t *key,
    uint32_t key_alg, const void *msg_prefix_1, size_t msg_prefix_1_len,
    const void *msg_prefix_2, size_t msg_prefix_2_len, const void *msg,
    size_t msg_len, hmac_digest_t digest) {
  /*
   * Shares for producing kErrorOk if SPHINCS+ verification succeeds.  The first
   * three shares are generated using the `sparse-fsm-encode` script while the
   * last share is
   * `kErrorOk ^ shares[0] ^ ... ^ shares[2]`.
   *
   * Encoding generated with:
   * $ ./util/design/sparse-fsm-encode.py -d 5 -m 3 -n 32 \
   *     -s 1069420 --language=c
   *
   * Minimum Hamming distance: 14
   * Maximum Hamming distance: 20
   * Minimum Hamming weight: 14
   * Maximum Hamming weight: 16
   */

  const uint32_t shares[] = {
      0x11deb806,
      0x06457f69,
      0x647f10c4,
      0x73e4d092,
  };

  key_alg &= ~(uint32_t)kOwnershipKeyAlgCategoryMask;
  key_alg |= (uint32_t)kOwnershipKeyAlgCategorySpx;

  sigverify_spx_root_t actual_root;
  sigverify_spx_root_t expected_root;
  spx_public_key_root(key->data, expected_root.data);
  size_t i;
  for (i = 0; launder32(i) < kSigverifySpxRootNumWords; ++i) {
    expected_root.data[i] ^= shares[i];
  }

  switch (key_alg) {
    case kOwnershipKeyAlgSpxPure:
      HARDENED_RETURN_IF_ERROR(spx_verify(
          signature->data, kSpxVerifyPureDomainSep, kSpxVerifyPureDomainSepSize,
          msg_prefix_1, msg_prefix_1_len, msg_prefix_2, msg_prefix_2_len, msg,
          msg_len, key->data, actual_root.data));
      break;

    case kOwnershipKeyAlgSpxPrehash:
      util_reverse_bytes(digest.digest, sizeof(digest.digest));
      HARDENED_RETURN_IF_ERROR(
          spx_verify(signature->data, kSpxVerifyPrehashDomainSep,
                     kSpxVerifyPrehashDomainSepSize,
                     /*msg_prefix_2=*/NULL, /*msg_prefix_2_len=*/0,
                     /*msg_prefix_3=*/NULL, /*msg_prefix_3_len=*/0,
                     (unsigned char *)digest.digest, sizeof(digest.digest),
                     key->data, actual_root.data));
      break;
    default:
      return kErrorSigverifyBadSpxConfig;
  }
  uint32_t result = 0;
  uint32_t diff = 0;
  for (--i; launder32(i) < kSigverifySpxRootNumWords; --i) {
    uint32_t val = expected_root.data[i] ^ actual_root.data[i];
    diff |= val ^ shares[i];
    diff |= ~diff + 1;          // Set upper bits to 1 if not 0, no change o/w.
    diff |= ~(diff >> 31) + 1;  // Set all 1s if MSB is set, no change o/w.
    result ^= val;
    result |= diff;
  }
  HARDENED_CHECK_EQ(i, SIZE_MAX);
  if (result != kErrorOk) {
    return kErrorSigverifyBadSpxSignature;
  }
  return result;
}

OT_WARN_UNUSED_RESULT
static rom_error_t rom_ext_verify(const manifest_t *manifest,
                                  const boot_data_t *boot_data) {
  RETURN_IF_ERROR(rom_ext_boot_policy_manifest_check(manifest, boot_data));

  uint32_t key_id =
      sigverify_ecdsa_p256_key_id_get(&manifest->ecdsa_public_key);
  // Check if there is an SPX+ key.
  const manifest_ext_spx_key_t *ext_spx_key;
  const manifest_ext_spx_signature_t *ext_spx_signature;
  rom_error_t spx_err = manifest_ext_get_spx_key(manifest, &ext_spx_key);
  spx_err += manifest_ext_get_spx_signature(manifest, &ext_spx_signature);
  switch ((uint32_t)spx_err) {
    case kErrorOk * 2:
      // Both extensions present: valid SPX+ signature.
      key_id ^= sigverify_spx_key_id_get(&ext_spx_key->key);
      break;
    case kErrorManifestBadExtension * 2:
      // Both extensions absent: ECDSA only.
      break;
    default:
      // One present, one absent: bad configuration.
      return kErrorManifestBadExtension;
  }

  RETURN_IF_ERROR(owner_keyring_find_key(&keyring, key_id, &verify_key));
  uint32_t key_alg = keyring.key[verify_key]->key_alg;

  dbg_printf("verify: key%u;%C;%C\r\n", verify_key, key_alg,
             keyring.key[verify_key]->key_domain);

  memset(boot_measurements.bl0.data, (int)rnd_uint32(),
         sizeof(boot_measurements.bl0.data));

  hmac_sha256_init();
  // Hash usage constraints.
  manifest_usage_constraints_t usage_constraints_from_hw;
  sigverify_usage_constraints_get(manifest->usage_constraints.selector_bits |
                                      keyring.key[verify_key]->usage_constraint,
                                  &usage_constraints_from_hw);
  hmac_sha256_update(&usage_constraints_from_hw,
                     sizeof(usage_constraints_from_hw));
  // Hash the remaining part of the image.
  manifest_digest_region_t digest_region = manifest_digest_region_get(manifest);
  hmac_sha256_update(digest_region.start, digest_region.length);
  // TODO(#19596): add owner configuration block to measurement.
  // Verify signature
  hmac_sha256_process();
  hmac_digest_t act_digest;
  hmac_sha256_final(&act_digest);

  static_assert(sizeof(boot_measurements.bl0) == sizeof(act_digest),
                "Unexpected BL0 digest size.");
  memcpy(&boot_measurements.bl0, &act_digest, sizeof(boot_measurements.bl0));

  uint32_t flash_exec = 0;
  if (key_alg == kOwnershipKeyAlgEcdsaP256) {
    return sigverify_ecdsa_p256_verify(&manifest->ecdsa_signature,
                                       &keyring.key[verify_key]->data.ecdsa,
                                       &act_digest, &flash_exec);
  } else if ((key_alg & kOwnershipKeyAlgCategoryMask) ==
             kOwnershipKeyAlgCategoryHybrid) {
    // Hybrid signatures check both ECDSA and SPX+ signatures.
    // TODO: as a future optimization, start the ECDSA verify operation on
    // OTBN and compute the SPX+ verify in parallel on Ibex.
    HARDENED_RETURN_IF_ERROR(sigverify_ecdsa_p256_verify(
        &manifest->ecdsa_signature, &keyring.key[verify_key]->data.hybrid.ecdsa,
        &act_digest, &flash_exec));
    return rom_ext_spx_verify(
        &ext_spx_signature->signature,
        &keyring.key[verify_key]->data.hybrid.spx, key_alg,
        &usage_constraints_from_hw, sizeof(usage_constraints_from_hw), NULL, 0,
        digest_region.start, digest_region.length, act_digest);
  } else {
    // TODO: consider whether an SPX+-only verify is sufficent.
    return kErrorOwnershipInvalidAlgorithm;
  }
}

/**
 * These symbols are defined in
 * `opentitan/sw/device/silicon_creator/rom_ext/rom_ext.ld`, and describe the
 * location of the flash header.
 */
extern char _owner_virtual_start_address[];
extern char _owner_virtual_size[];

/**
 * Compute the virtual address corresponding to the physical address `lma_addr`.
 *
 * @param manifest Pointer to the current manifest.
 * @param lma_addr Load address or physical address.
 * @return the computed virtual address.
 */
OT_WARN_UNUSED_RESULT
static uintptr_t owner_vma_get(const manifest_t *manifest, uintptr_t lma_addr) {
  return (lma_addr - (uintptr_t)manifest +
          (uintptr_t)_owner_virtual_start_address + CHIP_ROM_EXT_SIZE_MAX);
}

// Get the size of the remaining tail space that is not processed yet.
OT_WARN_UNUSED_RESULT
static size_t dice_chain_get_tail_size(void) {
  HARDENED_CHECK_GE(sizeof(dice_chain.data), dice_chain.tail_offset);
  return sizeof(dice_chain.data) - dice_chain.tail_offset;
}

// Get the pointer to the remaining tail space that is not processed yet.
OT_WARN_UNUSED_RESULT
static uint8_t *dice_chain_get_tail_buffer(void) {
  return &dice_chain.data[dice_chain.tail_offset];
}

// Cleanup stale `cert_obj` data and mark it as invalid.
static void dice_chain_reset_cert_obj(void) {
  memset(&dice_chain.cert_obj, 0, sizeof(dice_chain.cert_obj));
  dice_chain.cert_valid = kHardenedBoolFalse;
}

/**
 * Increments the DICE cert buffer offset to the next TLV object.
 * (ensuring to round up to the 64-bit flash word offset to prevent potential
 * ECC issues).
 */
static void dice_chain_next_cert_obj(void) {
  // Round up to next flash word for next perso TLV object offset.
  size_t cert_size = dice_chain.cert_obj.obj_size;

  // Pre-check to prevent the alignment op from unsigned overflow.
  HARDENED_CHECK_LE(cert_size, dice_chain_get_tail_size());
  cert_size = util_size_to_words(cert_size) * sizeof(uint32_t);
  cert_size = util_round_up_to(cert_size, 3);
  // Post-check for the buffer boundary.
  HARDENED_CHECK_LE(cert_size, dice_chain_get_tail_size());

  // Jump to the next object.
  dice_chain.tail_offset += cert_size;
  dice_chain_reset_cert_obj();
}

/**
 * Load the tlv cert obj from the tail buffer and check if it's valid.
 *
 * This method will update the `dice_chain` fields of current certificate:
 *   * `cert_obj` will be all zeros if not TLV cert entry is found.
 *   * `cert_valid` will only be set to true if name and pubkey matches.
 *
 * @param name The cert name to match.
 * @param name_size Size in byte of the `name` argument.
 * @return errors encountered during the operation.
 */
OT_WARN_UNUSED_RESULT
static rom_error_t dice_chain_load_cert_obj(const char *name,
                                            size_t name_size) {
  rom_error_t err =
      perso_tlv_get_cert_obj(dice_chain_get_tail_buffer(),
                             dice_chain_get_tail_size(), &dice_chain.cert_obj);

  if (err != kErrorOk) {
    // Cleanup the stale value if error.
    dice_chain_reset_cert_obj();
  }

  if (err == kErrorPersoTlvCertObjNotFound) {
    // If the cert is not found it is because we are running on a sim or FPGA
    // platform, or the device has not yet been provisioned. Continue, and let
    // the ROM_EXT generate an identity certificate for the current DICE stage.
    // The error is not fatal, and the cert obj has been marked as invalid.
    return kErrorOk;
  }

  HARDENED_RETURN_IF_ERROR(err);

  // Check if this cert is what we are looking for. The name and type (X.509 vs
  // CWT) should match.
  HARDENED_CHECK_LE(name_size, sizeof(dice_chain.cert_obj.name));
  const perso_tlv_object_type_t kExpectedCertType =
      kDiceCertFormat == kDiceCertFormatX509TcbInfo ? kPersoObjectTypeX509Cert
                                                    : kPersoObjectTypeCwtCert;
  if (name == NULL || memcmp(dice_chain.cert_obj.name, name, name_size) != 0 ||
      kExpectedCertType != dice_chain.cert_obj.obj_type) {
    // Name unmatched, keep the cert_obj but mark it as invalid.
    dice_chain.cert_valid = kHardenedBoolFalse;
    return kErrorOk;
  }

  // Check if the subject pubkey is matched. `cert_valid` will be set to false
  // if unmatched.
  HARDENED_RETURN_IF_ERROR(dice_cert_check_valid(
      &dice_chain.cert_obj, &dice_chain.subject_pubkey_id,
      &dice_chain.subject_pubkey, &dice_chain.cert_valid));

  return kErrorOk;
}

// Skip the TLV entry if the name matches.
static rom_error_t dice_chain_skip_cert_obj(const char *name,
                                            size_t name_size) {
  HARDENED_RETURN_IF_ERROR(dice_chain_load_cert_obj(NULL, 0));
  if (memcmp(dice_chain.cert_obj.name, name, name_size) == 0) {
    dice_chain_next_cert_obj();
  }
  return kErrorOk;
}

// Load the certificate data from flash to RAM buffer.
OT_WARN_UNUSED_RESULT
static rom_error_t dice_chain_load_flash(
    const flash_ctrl_info_page_t *info_page) {
  // Skip reload if it's already buffered.
  if (dice_chain.info_page == info_page) {
    dice_chain.tail_offset = 0;
    return kErrorOk;
  }

  // We are switching to a different page, flush changes (if dirty) first.
  HARDENED_RETURN_IF_ERROR(dice_chain_flush_flash());

  // Read in a DICE certificate(s) page.
  static_assert(sizeof(dice_chain.data) == kFlashPageSize,
                "Invalid dice_chain buffer size");
  HARDENED_RETURN_IF_ERROR(flash_ctrl_info_read_zeros_on_read_error(
      info_page, /*offset=*/0,
      /*word_count=*/kFlashPageSize / sizeof(uint32_t), dice_chain.data));

  // Resets the flash page status.
  dice_chain.data_dirty = kHardenedBoolFalse;
  dice_chain.tail_offset = 0;
  dice_chain.info_page = info_page;
  dice_chain_reset_cert_obj();

  return kErrorOk;
}

// Push the certificate to the tail with TLV header.
OT_WARN_UNUSED_RESULT
static rom_error_t dice_chain_push_cert(const char *name, const uint8_t *cert,
                                        const size_t cert_size) {
  // The data is going to be updated, mark it as dirty and clear the tail.
  dice_chain.data_dirty = kHardenedBoolTrue;

  // Invalidate all the remaining certificates in the tail buffer.
  memset(dice_chain_get_tail_buffer(), 0, dice_chain_get_tail_size());

  // Encode the certificate to the tail buffer.
  size_t cert_page_left = dice_chain_get_tail_size();
  perso_tlv_object_type_t cert_type =
      kDiceCertFormat == kDiceCertFormatX509TcbInfo ? kPersoObjectTypeX509Cert
                                                    : kPersoObjectTypeCwtCert;
  HARDENED_RETURN_IF_ERROR(
      perso_tlv_cert_obj_build(name, cert_type, cert, cert_size,
                               dice_chain_get_tail_buffer(), &cert_page_left));

  // Move the offset to the new tail.
  HARDENED_RETURN_IF_ERROR(perso_tlv_get_cert_obj(dice_chain_get_tail_buffer(),
                                                  dice_chain_get_tail_size(),
                                                  &dice_chain.cert_obj));
  dice_chain_next_cert_obj();
  return kErrorOk;
}

rom_error_t dice_chain_attestation_silicon(void) {
  // Initialize the entropy complex and KMAC for key manager operations.
  // Note: `OTCRYPTO_OK.value` is equal to `kErrorOk` but we cannot add a static
  // assertion here since its definition is not an integer constant expression.
  HARDENED_RETURN_IF_ERROR((rom_error_t)entropy_complex_init().value);
  HARDENED_RETURN_IF_ERROR(kmac_keymgr_configure());

  // Set keymgr reseed interval. Start with the maximum value to avoid
  // entropy complex contention during the boot process.
  const uint16_t kScKeymgrEntropyReseedInterval = UINT16_MAX;
  sc_keymgr_entropy_reseed_interval_set(kScKeymgrEntropyReseedInterval);
  SEC_MMIO_WRITE_INCREMENT(kScKeymgrSecMmioEntropyReseedIntervalSet);

  // ROM sets the SW binding values for the first key stage (CreatorRootKey) but
  // does not initialize the key manager. Advance key manager state twice to
  // transition to the CreatorRootKey state.
  HARDENED_RETURN_IF_ERROR(sc_keymgr_state_check(kScKeymgrStateReset));
  sc_keymgr_advance_state();
  HARDENED_RETURN_IF_ERROR(sc_keymgr_state_check(kScKeymgrStateInit));

  // Generate UDS keys.
  sc_keymgr_advance_state();
  HARDENED_RETURN_IF_ERROR(otbn_boot_cert_ecc_p256_keygen(
      kDiceKeyUds, &dice_chain.subject_pubkey_id, &dice_chain.subject_pubkey));

  // Switch page for the factory provisioned UDS cert.
  HARDENED_RETURN_IF_ERROR(
      dice_chain_load_flash(&kFlashCtrlInfoPageFactoryCerts));

  // Check if the UDS cert is valid.
  HARDENED_RETURN_IF_ERROR(dice_chain_load_cert_obj("UDS", /*name_size=*/4));
  if (launder32(dice_chain.cert_valid) == kHardenedBoolFalse) {
    // The UDS key ID (and cert itself) should never change unless:
    // 1. there is a hardware issue / the page has been corrupted, or
    // 2. the cert has not yet been provisioned.
    //
    // In both cases, we do nothing, and boot normally, later attestation
    // attempts will fail in a detectable manner.
    HARDENED_CHECK_EQ(dice_chain.cert_valid, kHardenedBoolFalse);
    dbg_printf("error: UDS certificate not valid\r\n");
  } else {
    // Cert is valid, move to the next one.
    HARDENED_CHECK_EQ(dice_chain.cert_valid, kHardenedBoolTrue);
    dice_chain_next_cert_obj();
  }

  // Save UDS key for signing next stage cert.
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      kDiceKeyUds.keygen_seed_idx, kDiceKeyUds.type,
      *kDiceKeyUds.keymgr_diversifier));
  dice_chain.endorsement_pubkey_id = dice_chain.subject_pubkey_id;

  return kErrorOk;
}

rom_error_t dice_chain_attestation_creator(
    keymgr_binding_value_t *rom_ext_measurement,
    const manifest_t *rom_ext_manifest) {
  // Generate CDI_0 attestation keys and (potentially) update certificate.
  keymgr_binding_value_t seal_binding_value = {
      .data = {rom_ext_manifest->identifier, 0}};
  SEC_MMIO_WRITE_INCREMENT(kScKeymgrSecMmioSwBindingSet +
                           kScKeymgrSecMmioOwnerIntMaxVerSet);
  HARDENED_RETURN_IF_ERROR(sc_keymgr_owner_int_advance(
      /*sealing_binding=*/&seal_binding_value,
      /*attest_binding=*/rom_ext_measurement,
      rom_ext_manifest->max_key_version));
  HARDENED_RETURN_IF_ERROR(otbn_boot_cert_ecc_p256_keygen(
      kDiceKeyCdi0, &dice_chain.subject_pubkey_id, &dice_chain.subject_pubkey));

  // Switch page for the device generated CDI_0.
  HARDENED_RETURN_IF_ERROR(dice_chain_load_flash(&kFlashCtrlInfoPageDiceCerts));

  // Seek to skip previous objects.
  HARDENED_RETURN_IF_ERROR(dice_chain_skip_cert_obj("UDS", /*name_size=*/4));

  // Check if the current CDI_0 cert is valid.
  HARDENED_RETURN_IF_ERROR(dice_chain_load_cert_obj("CDI_0", /*name_size=*/6));
  if (launder32(dice_chain.cert_valid) == kHardenedBoolFalse) {
    HARDENED_CHECK_EQ(dice_chain.cert_valid, kHardenedBoolFalse);
    dbg_printf("warning: CDI_0 certificate not valid; updating\r\n");
    // Update the cert page buffer.
    size_t updated_cert_size = kScratchCertSizeBytes;
    HARDENED_RETURN_IF_ERROR(
        dice_cdi_0_cert_build((hmac_digest_t *)rom_ext_measurement->data,
                              rom_ext_manifest->security_version,
                              &dice_chain.key_ids, &dice_chain.subject_pubkey,
                              dice_chain.scratch_cert, &updated_cert_size));
    HARDENED_RETURN_IF_ERROR(dice_chain_push_cert(
        "CDI_0", dice_chain.scratch_cert, updated_cert_size));
  } else {
    // Cert is valid, move to the next one.
    HARDENED_CHECK_EQ(dice_chain.cert_valid, kHardenedBoolTrue);
    dice_chain_next_cert_obj();

    // Replace UDS with CDI_0 key for endorsing next stage cert.
    HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
        kDiceKeyCdi0.keygen_seed_idx, kDiceKeyCdi0.type,
        *kDiceKeyCdi0.keymgr_diversifier));
  }
  dice_chain.endorsement_pubkey_id = dice_chain.subject_pubkey_id;

  return kErrorOk;
}

rom_error_t dice_chain_attestation_owner(
    const boot_data_t *boot_data, keymgr_binding_value_t *owner_measurement,
    const manifest_t *owner_manifest) {
  // Generate CDI_1 attestation keys and (potentially) update certificate.
  SEC_MMIO_WRITE_INCREMENT(kScKeymgrSecMmioSwBindingSet +
                           kScKeymgrSecMmioOwnerIntMaxVerSet);

  static_assert(
      sizeof(hmac_digest_t) == sizeof(keymgr_binding_value_t),
      "Expect the keymgr binding value to be the same size as a sha256 digest");
  // Get the verification key that verified the owner code.
  const owner_application_key_t *key = keyring.key[verify_key];
  hmac_digest_t ownership_block_measurement;
  hmac_digest_t attest_measurement;
  // Determine which owner block the key came from and measure that block.
  // Combine the measurement with the BL0 measurement.
  owner_block_measurement(owner_block_key_page(key),
                          &ownership_block_measurement);
  hmac_sha256_init();
  hmac_sha256_update(owner_measurement, sizeof(keymgr_binding_value_t));
  hmac_sha256_update(&ownership_block_measurement,
                     sizeof(ownership_block_measurement));
  hmac_sha256_process();
  hmac_sha256_final(&attest_measurement);

  // If we're not in LockedOwner state, we don't want to derive any valid
  // sealing keys, so set the binding constant to a nonsense value.
  keymgr_binding_value_t sealing_binding = {
      .data = {0x55555555, 0x55555555, 0x55555555, 0x55555555, 0x55555555,
               0x55555555, 0x55555555, 0x55555555}};

  if (boot_data->ownership_state == kOwnershipStateLockedOwner) {
    HARDENED_CHECK_EQ(boot_data->ownership_state, kOwnershipStateLockedOwner);
    static_assert(
        sizeof(key->raw_diversifier) == sizeof(keymgr_binding_value_t),
        "Expect the keymgr binding value to be the same size as an application "
        "key diversifier");
    memcpy(&sealing_binding, key->raw_diversifier, sizeof(sealing_binding));
  }
  HARDENED_RETURN_IF_ERROR(sc_keymgr_owner_advance(
      /*sealing_binding=*/&sealing_binding,
      /*attest_binding=*/(keymgr_binding_value_t *)&attest_measurement,
      owner_manifest->max_key_version));
  HARDENED_RETURN_IF_ERROR(otbn_boot_cert_ecc_p256_keygen(
      kDiceKeyCdi1, &dice_chain.subject_pubkey_id, &dice_chain.subject_pubkey));

  // Switch page for the device generated CDI_1.
  HARDENED_RETURN_IF_ERROR(dice_chain_load_flash(&kFlashCtrlInfoPageDiceCerts));

  // Seek to skip previous objects.
  HARDENED_RETURN_IF_ERROR(dice_chain_skip_cert_obj("UDS", /*name_size=*/4));
  HARDENED_RETURN_IF_ERROR(dice_chain_skip_cert_obj("CDI_0", /*name_size=*/6));

  // Check if the current CDI_0 cert is valid.
  HARDENED_RETURN_IF_ERROR(dice_chain_load_cert_obj("CDI_1", /*name_size=*/6));
  if (launder32(dice_chain.cert_valid) == kHardenedBoolFalse) {
    HARDENED_CHECK_EQ(dice_chain.cert_valid, kHardenedBoolFalse);
    dbg_printf("warning: CDI_1 certificate not valid; updating\r\n");
    // Update the cert page buffer.
    size_t updated_cert_size = kScratchCertSizeBytes;
    HARDENED_RETURN_IF_ERROR(dice_cdi_1_cert_build(
        (hmac_digest_t *)owner_measurement->data, &ownership_block_measurement,
        owner_manifest->security_version, &dice_chain.key_ids,
        &dice_chain.subject_pubkey, dice_chain.scratch_cert,
        &updated_cert_size));
    HARDENED_RETURN_IF_ERROR(dice_chain_push_cert(
        "CDI_1", dice_chain.scratch_cert, updated_cert_size));
  } else {
    // Cert is valid, move to the next one.
    HARDENED_CHECK_EQ(dice_chain.cert_valid, kHardenedBoolTrue);
    dice_chain_next_cert_obj();

    // Replace CDI_0 with CDI_1 key for endorsing next stage cert.
    HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
        kDiceKeyCdi1.keygen_seed_idx, kDiceKeyCdi1.type,
        *kDiceKeyCdi1.keymgr_diversifier));
  }
  dice_chain.endorsement_pubkey_id = dice_chain.subject_pubkey_id;

  // TODO: elimiate this call when we've fully programmed keymgr and lock it.
  sc_keymgr_sw_binding_unlock_wait();

  return kErrorOk;
}

// Write the DICE certs to flash if they have been updated.
rom_error_t dice_chain_flush_flash(void) {
  if (dice_chain.data_dirty == kHardenedBoolTrue &&
      dice_chain.info_page != NULL) {
    HARDENED_CHECK_EQ(dice_chain.data_dirty, kHardenedBoolTrue);
    HARDENED_RETURN_IF_ERROR(
        flash_ctrl_info_erase(dice_chain.info_page, kFlashCtrlEraseTypePage));
    static_assert(sizeof(dice_chain.data) == kFlashPageSize,
                  "Invalid dice_chain buffer size");
    HARDENED_RETURN_IF_ERROR(flash_ctrl_info_write(
        dice_chain.info_page,
        /*offset=*/0,
        /*word_count=*/kFlashPageSize / sizeof(uint32_t), dice_chain.data));
    dbg_printf("info: flushed dice cert page %d\r\n",
               dice_chain.info_page->base_addr);
    dice_chain.data_dirty = kHardenedBoolFalse;
  }
  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
static rom_error_t rom_ext_boot(boot_data_t *boot_data, boot_log_t *boot_log,
                                const manifest_t *manifest) {
  // Generate CDI_1 attestation keys and certificate.
  HARDENED_RETURN_IF_ERROR(dice_chain_attestation_owner(
      boot_data, &boot_measurements.bl0, manifest));

  // Write the DICE certs to flash if they have been updated.
  HARDENED_RETURN_IF_ERROR(dice_chain_flush_flash());

  // Remove write and erase access to the certificate pages before handing over
  // execution to the owner firmware (owner firmware can still read).
  flash_ctrl_cert_info_page_owner_restrict(
      &kFlashCtrlInfoPageAttestationKeySeeds);
  flash_ctrl_cert_info_page_owner_restrict(&kFlashCtrlInfoPageDiceCerts);

  // Disable access to silicon creator info pages, the OTP creator partition
  // and the OTP direct access interface until the next reset.
  flash_ctrl_creator_info_pages_lockdown();
  otp_creator_sw_cfg_lockdown();
  SEC_MMIO_WRITE_INCREMENT(kFlashCtrlSecMmioCreatorInfoPagesLockdown +
                           kOtpSecMmioCreatorSwCfgLockDown);

  // ePMP region 15 gives read/write access to RAM.
  rom_ext_epmp_set_napot(15, kRamRegion, kEpmpPermReadWrite);

  // Reconfigure the ePMP MMIO region to be NAPOT region 14, thus freeing
  // up an ePMP entry for use elsewhere.
  rom_ext_epmp_set_napot(14, kMmioRegion, kEpmpPermReadWrite);

  // ePMP region 13 allows RvDM access.
  if (lc_state == kLcStateProd || lc_state == kLcStateProdEnd) {
    // No RvDM access in Prod states, so we can clear the entry.
    rom_ext_epmp_clear(13);
  } else {
    rom_ext_epmp_set_napot(13, kRvDmRegion, kEpmpPermReadWriteExecute);
  }

  // ePMP region 12 gives read access to all of flash for both M and U modes.
  // The flash access was in ePMP region 5.  Clear it so it doesn't take
  // priority over 12.
  rom_ext_epmp_set_napot(12, kFlashRegion, kEpmpPermReadOnly);
  rom_ext_epmp_clear(5);

  // Move the ROM_EXT TOR region from entries 3/4/6 to 9/10/11.
  // If the ROM_EXT is located in the virtual window, the ROM will have
  // configured ePMP entry 6 as the read-only region over the entire
  // window.
  //
  // If not using the virtual window, we move the ROM_EXT TOR region to
  // ePMP entries 10/11.
  // If using the virtual window, we move the ROM_EXT read-only region to
  // ePMP entry 11 and move the TOR region to 9/10.
  uint32_t start, end, vwindow;
  CSR_READ(CSR_REG_PMPADDR3, &start);
  CSR_READ(CSR_REG_PMPADDR4, &end);
  CSR_READ(CSR_REG_PMPADDR6, &vwindow);
  uint8_t rxindex = 10;
  if (vwindow) {
    rxindex = 9;
    uint32_t size = 1 << bitfield_count_trailing_zeroes32(~vwindow);
    vwindow = (vwindow & ~(size - 1)) << 2;
    size <<= 3;

    rom_ext_epmp_set_napot(
        11, (epmp_region_t){.start = vwindow, .end = vwindow + size},
        kEpmpPermReadOnly);
  }
  rom_ext_epmp_set_tor(rxindex,
                       (epmp_region_t){.start = start << 2, .end = end << 2},
                       kEpmpPermReadExecute);
  for (int8_t i = (int8_t)rxindex - 1; i >= 0; --i) {
    rom_ext_epmp_clear((uint8_t)i);
  }
  HARDENED_RETURN_IF_ERROR(epmp_state_check());

  // Configure address translation, compute the epmp regions and the entry
  // point for the virtual address in case the address translation is enabled.
  // Otherwise, compute the epmp regions and the entry point for the load
  // address.
  //
  // We'll map the owner code TOR region as ePMP entries 2/3. If using address
  // translation, we'll configure ePMP entry 4 as the read-only region.
  epmp_region_t text_region = manifest_code_region_get(manifest);
  uintptr_t entry_point = manifest_entry_point_get(manifest);
  switch (launder32(manifest->address_translation)) {
    case kHardenedBoolTrue:
      HARDENED_CHECK_EQ(manifest->address_translation, kHardenedBoolTrue);
      ibex_addr_remap_1_set((uintptr_t)_owner_virtual_start_address,
                            (uintptr_t)manifest, (size_t)_owner_virtual_size);
      SEC_MMIO_WRITE_INCREMENT(kAddressTranslationSecMmioConfigure);

      // Unlock read-only for the whole rom_ext virtual memory.
      HARDENED_RETURN_IF_ERROR(epmp_state_check());
      rom_ext_epmp_set_napot(
          4,
          (epmp_region_t){.start = (uintptr_t)_owner_virtual_start_address,
                          .end = (uintptr_t)_owner_virtual_start_address +
                                 (uintptr_t)_owner_virtual_size},
          kEpmpPermReadOnly);
      HARDENED_RETURN_IF_ERROR(epmp_state_check());

      // Move the ROM_EXT execution section from the load address to the virtual
      // address.
      // TODO(#13513): Harden these calculations.
      text_region.start = owner_vma_get(manifest, text_region.start);
      text_region.end = owner_vma_get(manifest, text_region.end);
      entry_point = owner_vma_get(manifest, entry_point);
      break;
    case kHardenedBoolFalse:
      HARDENED_CHECK_EQ(manifest->address_translation, kHardenedBoolFalse);
      // Normally we'd want to clear the ROM region since we aren't using it
      // anymore and since it isn't being used to encode access to the virtual
      // window.  However, for SiVal, we want to keep low entries locked to
      // prevent using low entries to override policy in higher entries.
      // rom_ext_epmp_clear_rom_region();
      break;
    default:
      HARDENED_TRAP();
  }

  // Allow execution of owner stage executable code (text) sections,
  // unlock the ROM_EXT code regions so the next stage can re-use those
  // entries and clear RLB to prevent further changes to locked ePMP regions.
  HARDENED_RETURN_IF_ERROR(epmp_state_check());
  rom_ext_epmp_set_tor(2, text_region, kEpmpPermReadExecute);

  // Now that we're done reconfiguring the ePMP, we'll clear the RLB bit to
  // prevent any modification to locked entries.
  rom_ext_epmp_clear_rlb();
  HARDENED_RETURN_IF_ERROR(epmp_state_check());

  // Lock the address translation windows.
  ibex_addr_remap_lockdown(0);
  ibex_addr_remap_lockdown(1);

  // Lock the flash according to the ownership configuration.
  HARDENED_RETURN_IF_ERROR(
      ownership_flash_lockdown(boot_data, boot_log, &owner_config));

  // Verify expectations before jumping to owner code.
  // TODO: we really want to call rnd_uint32 here to select a random starting
  // location for checking expectations.  However, rnd_uint32 read from OTP
  // to know if it's allowed to used the CSRNG and OTP is locked down.
  sec_mmio_check_values_except_otp(/*rnd_uint32()*/ 0,
                                   TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR);
  // Jump to OWNER entry point.
  dbg_printf("entry: 0x%x\r\n", (unsigned int)entry_point);
  ((owner_stage_entry_point *)entry_point)();

  return kErrorRomExtBootFailed;
}

OT_WARN_UNUSED_RESULT
static rom_error_t boot_svc_next_boot_bl0_slot_handler(
    boot_svc_msg_t *boot_svc_msg, boot_data_t *boot_data,
    boot_log_t *boot_log) {
  uint32_t active_slot = boot_data->primary_bl0_slot;
  uint32_t primary_slot = boot_svc_msg->next_boot_bl0_slot_req.primary_bl0_slot;
  rom_error_t error = kErrorOk;

  // If the requested primary slot is the same as the active slot, this request
  // is a no-op.
  if (active_slot != primary_slot) {
    switch (primary_slot) {
      case kBootSlotA:
      case kBootSlotB:
        boot_data->primary_bl0_slot = primary_slot;
        // Write boot data, updating relevant fields and recomputing the digest.
        HARDENED_RETURN_IF_ERROR(boot_data_write(boot_data));
        // Read the boot data back to ensure the correct slot is booted this
        // time.
        HARDENED_RETURN_IF_ERROR(boot_data_read(lc_state, boot_data));
        // Update the boot log.
        boot_log->primary_bl0_slot = boot_data->primary_bl0_slot;
        break;
      case kBootSlotUnspecified:
        // Do nothing.
        break;
      default:
        error = kErrorBootSvcBadSlot;
    }
  }

  // Record the new primary slot for use in the response message.
  active_slot = boot_data->primary_bl0_slot;

  uint32_t next_slot = boot_svc_msg->next_boot_bl0_slot_req.next_bl0_slot;
  switch (launder32(next_slot)) {
    case kBootSlotA:
    case kBootSlotB:
      // We overwrite the RAM copy of the primary slot to the requested next
      // slot. This will cause a one-time boot of the requested side.
      boot_data->primary_bl0_slot = next_slot;
      break;
    case kBootSlotUnspecified:
      // Do nothing.
      break;
    default:
      error = kErrorBootSvcBadSlot;
  }

  boot_svc_next_boot_bl0_slot_res_init(error, active_slot,
                                       &boot_svc_msg->next_boot_bl0_slot_res);
  // We always return OK here because we've logged any error status in the boot
  // services response message and we want the boot flow to continue.
  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
static rom_error_t boot_svc_min_sec_ver_handler(boot_svc_msg_t *boot_svc_msg,
                                                boot_data_t *boot_data) {
  const uint32_t current_min_sec_ver = boot_data->min_security_version_bl0;
  const uint32_t requested_min_sec_ver =
      boot_svc_msg->next_boot_bl0_slot_req.next_bl0_slot;

  // Ensure the requested minimum security version isn't lower than the current
  // minimum security version.
  if (launder32(requested_min_sec_ver) > current_min_sec_ver) {
    HARDENED_CHECK_GT(requested_min_sec_ver, current_min_sec_ver);
    uint32_t max_sec_ver = current_min_sec_ver;

    // Check the two flash slots for valid manifests and determine the maximum
    // value of the new minimum_security_version.  This prevents a malicious
    // MinBl0SecVer request from making the chip un-bootable.
    const manifest_t *manifest = rom_ext_boot_policy_manifest_a_get();
    rom_error_t error = rom_ext_verify(manifest, boot_data);
    if (error == kErrorOk && manifest->security_version > max_sec_ver) {
      max_sec_ver = manifest->security_version;
    }
    manifest = rom_ext_boot_policy_manifest_b_get();
    error = rom_ext_verify(manifest, boot_data);
    if (error == kErrorOk && manifest->security_version > max_sec_ver) {
      max_sec_ver = manifest->security_version;
    }

    if (requested_min_sec_ver <= max_sec_ver) {
      HARDENED_CHECK_LE(requested_min_sec_ver, max_sec_ver);
      // Update boot data to the requested minimum BL0 security version.
      boot_data->min_security_version_bl0 = requested_min_sec_ver;

      // Write boot data, updating relevant fields and recomputing the digest.
      HARDENED_RETURN_IF_ERROR(boot_data_write(boot_data));
      // Read the boot data back to ensure the correct policy is used this boot.
      HARDENED_RETURN_IF_ERROR(boot_data_read(lc_state, boot_data));

      boot_svc_min_bl0_sec_ver_res_init(boot_data->min_security_version_bl0,
                                        kErrorOk,
                                        &boot_svc_msg->min_bl0_sec_ver_res);

      HARDENED_CHECK_EQ(requested_min_sec_ver,
                        boot_data->min_security_version_bl0);
      return kErrorOk;
    }
  }
  boot_svc_min_bl0_sec_ver_res_init(current_min_sec_ver, kErrorBootSvcBadSecVer,
                                    &boot_svc_msg->min_bl0_sec_ver_res);
  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
static rom_error_t handle_boot_svc(boot_data_t *boot_data,
                                   boot_log_t *boot_log) {
  boot_svc_msg_t *boot_svc_msg = &retention_sram_get()->creator.boot_svc_msg;
  // TODO(lowRISC#22387): Examine the boot_svc code paths for boot loops.
  if (boot_svc_msg->header.identifier == kBootSvcIdentifier) {
    HARDENED_RETURN_IF_ERROR(boot_svc_header_check(&boot_svc_msg->header));
    uint32_t msg_type = boot_svc_msg->header.type;
    switch (launder32(msg_type)) {
      case kBootSvcEmptyReqType:
        HARDENED_CHECK_EQ(msg_type, kBootSvcEmptyReqType);
        boot_svc_empty_res_init(&boot_svc_msg->empty);
        break;
      case kBootSvcNextBl0SlotReqType:
        HARDENED_CHECK_EQ(msg_type, kBootSvcNextBl0SlotReqType);
        return boot_svc_next_boot_bl0_slot_handler(boot_svc_msg, boot_data,
                                                   boot_log);
      case kBootSvcMinBl0SecVerReqType:
        HARDENED_CHECK_EQ(msg_type, kBootSvcMinBl0SecVerReqType);
        return boot_svc_min_sec_ver_handler(boot_svc_msg, boot_data);
      case kBootSvcOwnershipUnlockReqType:
        HARDENED_CHECK_EQ(msg_type, kBootSvcOwnershipUnlockReqType);
        return ownership_unlock_handler(boot_svc_msg, boot_data);
      case kBootSvcOwnershipActivateReqType:
        HARDENED_CHECK_EQ(msg_type, kBootSvcOwnershipActivateReqType);
        return ownership_activate_handler(boot_svc_msg, boot_data);
      case kBootSvcEmptyResType:
      case kBootSvcNextBl0SlotResType:
      case kBootSvcMinBl0SecVerResType:
      case kBootSvcOwnershipUnlockResType:
      case kBootSvcOwnershipActivateResType:
        // For response messages left in ret-ram we do nothing.
        break;
      default:
          // For messages with an unknown msg_type, we do nothing.
          ;
    }
  }
  return kErrorOk;
}

OT_WARN_UNUSED_RESULT
static rom_error_t rom_ext_try_next_stage(boot_data_t *boot_data,
                                          boot_log_t *boot_log) {
  rom_ext_boot_policy_manifests_t manifests =
      rom_ext_boot_policy_manifests_get(boot_data);
  rom_error_t error = kErrorRomExtBootFailed;
  rom_error_t slot[2] = {0, 0};
  for (size_t i = 0; i < ARRAYSIZE(manifests.ordered); ++i) {
    error = rom_ext_verify(manifests.ordered[i], boot_data);
    slot[i] = error;
    if (error != kErrorOk) {
      continue;
    }

    if (manifests.ordered[i] == rom_ext_boot_policy_manifest_a_get()) {
      boot_log->bl0_slot = kBootSlotA;
    } else if (manifests.ordered[i] == rom_ext_boot_policy_manifest_b_get()) {
      boot_log->bl0_slot = kBootSlotB;
    } else {
      return kErrorRomExtBootFailed;
    }
    boot_log_digest_update(boot_log);

    // Boot fails if a verified ROM_EXT cannot be booted.
    RETURN_IF_ERROR(rom_ext_boot(boot_data, boot_log, manifests.ordered[i]));
    // `rom_ext_boot()` should never return `kErrorOk`, but if it does
    // we must shut down the chip instead of trying the next ROM_EXT.
    return kErrorRomExtBootFailed;
  }

  // If we get here, the loop exited after trying both slots.
  // If we see kErrorBootPolicyBadIdentifier as the error, we probably have an
  // empty slot.  In that case, the "bad identifier" error is not helpful, so
  // maybe choose the error from the other slot.
  if (error == kErrorBootPolicyBadIdentifier && error == slot[1]) {
    // If the bad identifier error comes from the non-primary slot, prefer
    // the error from the primary slot.
    error = slot[0];
  }
  return error;
}

rom_error_t dice_chain_init(void) {
  // Variable initialization.
  memset(&dice_chain, 0, sizeof(dice_chain));
  dice_chain.subject_pubkey = (ecdsa_p256_public_key_t){.x = {0}, .y = {0}};
  dice_chain.data_dirty = kHardenedBoolFalse;
  dice_chain.info_page = NULL;
  dice_chain.key_ids = (cert_key_id_pair_t){
      .endorsement = &dice_chain.endorsement_pubkey_id,
      .cert = &dice_chain.subject_pubkey_id,
  };
  dice_chain_reset_cert_obj();

  // Configure DICE certificate flash info page and buffer it into RAM.
  flash_ctrl_cert_info_page_creator_cfg(&kFlashCtrlInfoPageAttestationKeySeeds);
  flash_ctrl_cert_info_page_creator_cfg(&kFlashCtrlInfoPageDiceCerts);
  flash_ctrl_info_cfg_set(&kFlashCtrlInfoPageFactoryCerts,
                          kCertificateInfoPageCfg);
  flash_ctrl_cert_info_page_owner_restrict(&kFlashCtrlInfoPageFactoryCerts);
  return kErrorOk;
}

static void rom_ext_flash_protect_self(uint32_t rom_ext_slot) {
  flash_ctrl_cfg_t cfg = flash_ctrl_data_default_cfg_get();
  flash_ctrl_perms_t read = {
      .read = kMultiBitBool4True,
      .write = kMultiBitBool4False,
      .erase = kMultiBitBool4False,
  };
  flash_ctrl_perms_t write = {
      .read = kMultiBitBool4True,
      .write = kMultiBitBool4True,
      .erase = kMultiBitBool4True,
  };
  flash_ctrl_data_region_protect(0, kRomExtAStart, kRomExtSizeInPages,
                                 rom_ext_slot == kBootSlotA ? read : write, cfg,
                                 kHardenedBoolTrue);
  flash_ctrl_data_region_protect(1, kRomExtBStart, kRomExtSizeInPages,
                                 rom_ext_slot == kBootSlotB ? read : write, cfg,
                                 kHardenedBoolTrue);
}

static rom_error_t rom_ext_start(boot_data_t *boot_data, boot_log_t *boot_log) {
  HARDENED_RETURN_IF_ERROR(rom_ext_init(boot_data));
  const manifest_t *self = rom_ext_manifest();
  dbg_printf("ROM_EXT:%u.%u\r\n", self->version_major, self->version_minor);

  // Establish our identity.
  HARDENED_RETURN_IF_ERROR(dice_chain_init());
  HARDENED_RETURN_IF_ERROR(dice_chain_attestation_silicon());

  // Initialize the boot_log in retention RAM.
  const chip_info_t *rom_chip_info = (const chip_info_t *)_chip_info_start;
  boot_log_check_or_init(boot_log, rom_ext_current_slot(), rom_chip_info);
  boot_log->rom_ext_major = self->version_major;
  boot_log->rom_ext_minor = self->version_minor;
  boot_log->rom_ext_size = CHIP_ROM_EXT_SIZE_MAX;
  // Even though `primary_bl0_slot` can be changed by boot svc, we initialize
  // it here so the "SetNextBl0" can do a one-time override of the RAM copy
  // of `boot_data`.
  boot_log->primary_bl0_slot = boot_data->primary_bl0_slot;

  // Protect the flash pages where the ROM_EXT is located.
  rom_ext_flash_protect_self(boot_log->rom_ext_slot);

  // Initialize the chip ownership state.
  rom_error_t error;
  error = ownership_init(boot_data, &owner_config, &keyring);
  if (error == kErrorWriteBootdataThenReboot) {
    return error;
  }
  // TODO(cfrantz): evaluate permissible ownership init failure conditions
  // and change this to HARDENED_RETURN_IF_ERROR.
  if (error != kErrorOk) {
    dbg_printf("error: ownership_init=%x\r\n", error);
  }

  HARDENED_RETURN_IF_ERROR(
      dice_chain_attestation_creator(&boot_measurements.rom_ext, self));

  // Configure SRAM execution as the owner requested.
  rom_ext_sram_exec(owner_config.sram_exec);

  // Handle any pending boot_svc commands.
  uint32_t reset_reasons = retention_sram_get()->creator.reset_reasons;
  uint32_t skip_boot_svc = reset_reasons & (1 << kRstmgrReasonLowPowerExit);
  if (skip_boot_svc == 0) {
    error = handle_boot_svc(boot_data, boot_log);
    if (error == kErrorWriteBootdataThenReboot) {
      // Boot services reports errors by writing a status code into the reply
      // messages.  Regardless of whether a boot service request produced an
      // error, we want to continue booting unless the error specifically asks
      // for a reboot.
      return error;
    }
  }

  // Synchronize the boot_log entries that could be changed by boot services.
  boot_log->rom_ext_nonce = boot_data->nonce;
  boot_log->ownership_state = boot_data->ownership_state;
  boot_log->ownership_transfers = boot_data->ownership_transfers;
  boot_log->rom_ext_min_sec_ver = boot_data->min_security_version_rom_ext;
  boot_log->bl0_min_sec_ver = boot_data->min_security_version_bl0;
  boot_log_digest_update(boot_log);

  if (uart_break_detect(kRescueDetectTime) == kHardenedBoolTrue) {
    dbg_printf("rescue: remember to clear break\r\n");
    uart_enable_receiver();
    ownership_pages_lockdown(boot_data, /*rescue=*/kHardenedBoolTrue);
    // TODO: update rescue protocol to accept boot data and rescue
    // config from the owner_config.
    error = rescue_protocol(boot_data, owner_config.rescue);
  } else {
    ownership_pages_lockdown(boot_data, /*rescue=*/kHardenedBoolFalse);
    error = rom_ext_try_next_stage(boot_data, boot_log);
  }
  return error;
}

void rom_ext_main(void) {
  rom_ext_check_rom_expectations();
  boot_data_t boot_data;
  boot_log_t *boot_log = &retention_sram_get()->creator.boot_log;

  rom_error_t error = rom_ext_start(&boot_data, boot_log);
  if (error == kErrorWriteBootdataThenReboot) {
    HARDENED_CHECK_EQ(error, kErrorWriteBootdataThenReboot);
    error = boot_data_write(&boot_data);
  }
  shutdown_finalize(error);
}

void rom_ext_interrupt_handler(void) { shutdown_finalize(rom_ext_irq_error()); }

// We only need a single handler for all ROM_EXT interrupts, but we want to
// keep distinct symbols to make writing tests easier.  In the ROM_EXT,
// alias all interrupt handler symbols to the single handler.
OT_ALIAS("rom_ext_interrupt_handler")
void rom_ext_exception_handler(void);

OT_ALIAS("rom_ext_interrupt_handler")
void rom_ext_nmi_handler(void);
