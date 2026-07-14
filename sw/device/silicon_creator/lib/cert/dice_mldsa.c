// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stddef.h>
#include <string.h>

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/hardened_memory.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/base/static_dice_cdi_0.h"
#include "sw/device/silicon_creator/lib/base/static_dice_mldsa_cdi.h"
#include "sw/device/silicon_creator/lib/base/util.h"
#include "sw/device/silicon_creator/lib/cert/cdi_hybrid.h"
#include "sw/device/silicon_creator/lib/cert/dice.h"
#include "sw/device/silicon_creator/lib/cert/dice_chain.h"
#include "sw/device/silicon_creator/lib/cert/dice_keys.h"
#include "sw/device/silicon_creator/lib/cert/dice_storage.h"
#include "sw/device/silicon_creator/lib/cert/seeds.h"
#include "sw/device/silicon_creator/lib/cert/template.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/hmac.h"
#include "sw/device/silicon_creator/lib/drivers/kmac.h"
#include "sw/device/silicon_creator/lib/drivers/lifecycle.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/otbn_boot_services.h"
#include "sw/device/silicon_creator/lib/ownership/ownership_key.h"
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"
#include "sw/device/silicon_creator/manuf/lib/flash_info_fields.h"
#include "third_party/embedpqc/mldsa44_tiny.h"
#include "third_party/embedpqc/ports/mldsa44_tiny_caller.h"

enum {
  kDiceSlotSize = 936,
};

const dice_storage_slot_t kDiceStorageCdi0Ecdsa = DICE_STORAGE_SLOT(
    "CDI_0", &kFlashCtrlInfoPageDiceCerts,
    /*offset_val=*/0,
    /*slot_size_val=*/kDiceSlotSize, kPersoObjectTypeX509Cert);

const dice_storage_slot_t kDiceStorageCdi1Ecdsa = DICE_STORAGE_SLOT(
    "CDI_1", &kFlashCtrlInfoPageDiceCerts,
    /*offset_val=*/kDiceSlotSize,
    /*slot_size_val=*/kDiceSlotSize, kPersoObjectTypeX509Cert);

// Key algorithm variant orders defined in the cdi_hybrid.hjson template.
enum {
  kCdiHybridKeyAlgEcdsa = 0,
  kCdiHybridKeyAlgMldsa44 = 1,
};

// Local dice page buffer.
static dice_storage_page_t dice_page;

// Shared static buffers for `dice_attest_next_cdi` operation.
static uint8_t curr_mldsa_sig[MLDSA44_SIGNATURE_BYTES];
static uint8_t tbs_buffer[kCdiHybridMaxTbsSizeBytes];
static uint8_t pubkey_buffer[kCdiHybridExactPubKeyMldsaSizeBytes];

// Shared scratch buffer for ML-DSA public keys and stack.
static uint8_t mldsa_scratch[32 * 1024] __attribute__((aligned(16)));

// Keymgr configurations for deriving attestation keys.
typedef struct keygen_params {
  const sc_keymgr_ecc_key_t *ecc_cfg;
  const sc_keymgr_ecc_key_t *mldsa_cfg;
} keygen_params_t;

static const keygen_params_t kUdsKeygenParams = {
    .ecc_cfg = &kDiceKeyUds,
    .mldsa_cfg = &kDiceKeyMldsaUds,
};

static const keygen_params_t kCdi0KeygenParams = {
    .ecc_cfg = &kDiceKeyCdi0,
    .mldsa_cfg = &kDiceKeyMldsaCdi0,
};

static const keygen_params_t kCdi1KeygenParams = {
    .ecc_cfg = &kDiceKeyCdi1,
    .mldsa_cfg = &kDiceKeyMldsaCdi1,
};

// Parameters for attesting CDI_0 / CDI_1 certificates.
typedef struct attest_params {
  const keygen_params_t *issuer_params;
  const keygen_params_t *subject_params;

  void *scratch_buf;
  size_t scratch_buf_size;

  uint8_t *ecdsa_cert_out;
  size_t ecdsa_cert_max_size;
  uint32_t *ecdsa_cert_size_out;
  hmac_digest_t *subject_ecdsa_key_id_out;

  uint8_t *mldsa_cert_out;
  size_t mldsa_cert_max_size;
  uint32_t *mldsa_cert_size_out;
  hmac_digest_t *subject_mldsa_key_id_out;
} attest_params_t;

static hmac_digest_t cdi0_mldsa_id;
static hmac_digest_t cdi1_ecdsa_id;
static hmac_digest_t cdi1_mldsa_id;
static uint32_t cdi1_ecdsa_size;
static uint8_t cdi1_ecdsa_cert_buf[kDiceSlotSize];

static const attest_params_t kCdi0AttestParams = {
    .issuer_params = &kUdsKeygenParams,
    .subject_params = &kCdi0KeygenParams,
    .scratch_buf = mldsa_scratch,
    .scratch_buf_size = sizeof(mldsa_scratch),
    .ecdsa_cert_out = static_dice_cdi_0.cert_data,
    .ecdsa_cert_max_size = sizeof(static_dice_cdi_0.cert_data),
    .ecdsa_cert_size_out = &static_dice_cdi_0.cert_size,
    .subject_ecdsa_key_id_out = &static_dice_cdi_0.cdi_0_pubkey_id,
    .mldsa_cert_out = static_dice_mldsa_cdi.cdi_0_cert,
    .mldsa_cert_max_size = sizeof(static_dice_mldsa_cdi.cdi_0_cert),
    .mldsa_cert_size_out = &static_dice_mldsa_cdi.cdi_0_cert_size,
    .subject_mldsa_key_id_out = &cdi0_mldsa_id,
};

static const attest_params_t kCdi1AttestParams = {
    .issuer_params = &kCdi0KeygenParams,
    .subject_params = &kCdi1KeygenParams,
    .scratch_buf = mldsa_scratch,
    .scratch_buf_size = sizeof(mldsa_scratch),
    .ecdsa_cert_out = cdi1_ecdsa_cert_buf,
    .ecdsa_cert_max_size = sizeof(cdi1_ecdsa_cert_buf),
    .ecdsa_cert_size_out = &cdi1_ecdsa_size,
    .subject_ecdsa_key_id_out = &cdi1_ecdsa_id,
    .mldsa_cert_out = static_dice_mldsa_cdi.cdi_1_cert,
    .mldsa_cert_max_size = sizeof(static_dice_mldsa_cdi.cdi_1_cert),
    .mldsa_cert_size_out = &static_dice_mldsa_cdi.cdi_1_cert_size,
    .subject_mldsa_key_id_out = &cdi1_mldsa_id,
};

static const uint8_t kSha256FwIdPrefix[] = {
    /* SEQUENCE with 45 (0x2d) bytes content */
    0x30, 0x2d,
    /* OBJECT IDENTIFIER 2.16.840.1.101.3.4.2.1 (sha-256) */
    0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01,
    /* OCTET STRING 32 (0x20) bytes */
    0x04, 0x20,
    /* 32 bytes to be appended by encode_sha256_fwid here. */
};

enum {
  kSha256FwIdSizeBytes = sizeof(kSha256FwIdPrefix) + sizeof(hmac_digest_t),
};

/**
 * Encodes the SHA-256 firmware ID list in the DICE TCB.
 *
 * @param dest Buffer to copy the encoded firmware ID list to. Must be at least
 * `kSha256FwIdSizeBytes` bytes.
 * @param digest The SHA-256 digest to append.
 */
static void encode_sha256_fwid(uint8_t *dest, const hmac_digest_t *digest) {
  memcpy(dest, kSha256FwIdPrefix, sizeof(kSha256FwIdPrefix));
  memcpy(dest + sizeof(kSha256FwIdPrefix), digest->digest,
         sizeof(hmac_digest_t));
}

/**
 * Returns true if the OwnerSw is booting outside of prod domain.
 */
static bool get_debug_mode_cdi1(owner_app_domain_t key_domain) {
  if (launder32(key_domain) != kOwnerAppDomainProd) {
    return true;
  }
  HARDENED_CHECK_EQ(key_domain, kOwnerAppDomainProd);
  return false;
}

/**
 * Derives a 256-bit ML-DSA certificate ID from a seed.
 *
 * @param seed The ML-DSA key seed.
 * @param[out] id The computed public key ID.
 */
static void get_mldsa_id(const hmac_key_t *seed, hmac_digest_t *id) {
  hmac_hmac_sha256("ID", 2, *seed, /*big_endian_digest=*/true, id);
}

/***
 * Computes attestation binding values from the TCB measurements.
 *
 * @param tbs The TBS variable values.
 * @param[out] output Computed attestation binding values.
 */
static void get_attest_binding(const cdi_hybrid_tbs_values_t *tbs,
                               hmac_digest_t *output) {
  hmac_sha256_configure(false);
  hmac_sha256_start();
  hmac_sha256_update(tbs->tcb_model, tbs->tcb_model_len);
  hmac_sha256_update(tbs->tcb_svn, kCdiHybridExactTcbSvnSizeBytes);
  hmac_sha256_update(&tbs->tcb_layer, sizeof(tbs->tcb_layer));
  hmac_sha256_update(tbs->tcb_fw_ids, tbs->tcb_fw_ids_size);
  hmac_sha256_update(&tbs->debug_flag, sizeof(tbs->debug_flag));
  hmac_sha256_process();
  hmac_sha256_final(output);
}

/**
 * Builds and signs a CDI certificate.
 *
 * @param tbs_values The TBS variable values to build.
 * @param signer_ecdsa_pubkey The signer's ECDSA public key.
 * @param signer_mldsa_seed The signer's ML-DSA private key seed.
 * @param[out] cert The generated certificate.
 * @param[in,out] cert_size The size of the certificate buffer on input, and
 *                          the size of the generated certificate on output.
 * @param stack_top Top of the dedicate stack to use for ML-DSA operations.
 */
static rom_error_t dice_cdi_hybrid_cert_build(
    cdi_hybrid_tbs_values_t *tbs_values,
    const ecdsa_p256_public_key_t *signer_ecdsa_pubkey,
    const uint8_t *signer_mldsa_seed, uint8_t *cert, size_t *cert_size,
    void *stack_top) {
  // Construct X509 TBS payload.
  size_t tbs_size = sizeof(tbs_buffer);
  HARDENED_RETURN_IF_ERROR(
      cdi_hybrid_build_tbs(tbs_values, tbs_buffer, &tbs_size));

  // Sign the TBS.
  cdi_hybrid_sig_values_t sig_params;
  memset(&sig_params, 0, sizeof(sig_params));
  if (tbs_values->key_alg == kCdiHybridKeyAlgMldsa44) {
    uint32_t randomizer[MLDSA44_RANDOMIZER_BYTES / sizeof(uint32_t)];
    HARDENED_CHECK_EQ(
        hardened_memshred(randomizer, ARRAYSIZE(randomizer)).value,
        kHardenedBoolTrue);
    mldsa44_tiny_sign_with_stack(curr_mldsa_sig, signer_mldsa_seed,
                                 (const uint8_t *)randomizer, tbs_buffer,
                                 tbs_size, stack_top);
    HARDENED_CHECK_EQ(
        hardened_memshred(randomizer, ARRAYSIZE(randomizer)).value,
        kHardenedBoolTrue);
    TEMPLATE_SET_TRUNCATED(sig_params, CdiHybrid, CertSignatureMldsa,
                           curr_mldsa_sig,
                           kCdiHybridExactCertSignatureMldsaSizeBytes);
  } else {
    hmac_digest_t tbs_digest;
    hmac_sha256(tbs_buffer, tbs_size, &tbs_digest);

    ecdsa_p256_public_key_t signer_pubkey_le = *signer_ecdsa_pubkey;
    util_reverse_bytes(signer_pubkey_le.x, sizeof(signer_pubkey_le.x));
    util_reverse_bytes(signer_pubkey_le.y, sizeof(signer_pubkey_le.y));

    ecdsa_p256_signature_t ecdsa_tbs_signature;
    HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_endorse(
        &tbs_digest, &ecdsa_tbs_signature, &signer_pubkey_le));

    util_p256_signature_le_to_be_convert(ecdsa_tbs_signature.r,
                                         ecdsa_tbs_signature.s);

    TEMPLATE_SET(sig_params, CdiHybrid, CertSignatureR, ecdsa_tbs_signature.r);
    TEMPLATE_SET(sig_params, CdiHybrid, CertSignatureS, ecdsa_tbs_signature.s);
  }

  // Construct the signed certificate.
  // Note: tbs_size is always less than or equal to sizeof(tbs_buffer), so it
  // is safe to check against sizeof(tbs_buffer) instead of tbs_size.
  TEMPLATE_CHECK_SIZE(CdiHybrid, Tbs, sizeof(tbs_buffer));
  TEMPLATE_SET(sig_params, CdiHybrid, Tbs, tbs_buffer);
  sig_params.tbs_size = tbs_size;
  sig_params.key_alg = tbs_values->key_alg;
  return cdi_hybrid_build_cert(&sig_params, cert, cert_size);
}

/**
 * Derives a 256-bit ML-DSA private key seed using the SP800-133r3 scheme.
 *
 * @param params Key generation parameters.
 * @param[out] seed_output Derived 256-bit ML-DSA key seed.
 */
static rom_error_t dice_mldsa_derive_seed(const keygen_params_t *params,
                                          keymgr_binding_value_t *seed_output) {
  HARDENED_RETURN_IF_ERROR(sc_keymgr_generate_key_sw(
      kScKeymgrKeyTypeAttestation, *params->mldsa_cfg->keymgr_diversifier,
      seed_output));

  uint32_t additional_seed[kAttestationSeedWords];
  HARDENED_RETURN_IF_ERROR(load_attestation_keygen_seed(
      params->mldsa_cfg->keygen_seed_idx, additional_seed));

  for (size_t i = 0; i < sizeof(seed_output->data) / sizeof(uint32_t); ++i) {
    seed_output->data[i] ^= additional_seed[i];
  }

  return kErrorOk;
}

/**
 * Attests the next-stage CDI certificates.
 *
 * @param params Parameters for the attestation.
 * @param sealing_binding Keymgr sealing binding value.
 * @param max_key_version Maximum key version allowed for key derivation.
 * @param tbs_values Pointer to TBS variable values.
 * @param regenerate If true, regenerate the certificate; otherwise, just derive
 * key IDs.
 */
static rom_error_t dice_attest_next_cdi(
    const attest_params_t *params,
    const keymgr_binding_value_t *sealing_binding, uint32_t max_key_version,
    cdi_hybrid_tbs_values_t *tbs_values, bool regenerate) {
  // Derive Issuer Keys & IDs (Before Keymgr Advance)
  ecdsa_p256_public_key_t issuer_ecdsa_pubkey;
  hmac_digest_t issuer_ecdsa_pubkey_id;
  HARDENED_RETURN_IF_ERROR(otbn_boot_cert_ecc_p256_keygen(
      *params->issuer_params->ecc_cfg, &issuer_ecdsa_pubkey_id,
      &issuer_ecdsa_pubkey));

  // Save issuer attestation key for endorsing the next stage
  HARDENED_RETURN_IF_ERROR(otbn_boot_attestation_key_save(
      params->issuer_params->ecc_cfg->keygen_seed_idx,
      params->issuer_params->ecc_cfg->type,
      *params->issuer_params->ecc_cfg->keymgr_diversifier));

  keymgr_binding_value_t issuer_mldsa_seed;
  HARDENED_RETURN_IF_ERROR(
      dice_mldsa_derive_seed(params->issuer_params, &issuer_mldsa_seed));
  hmac_digest_t issuer_mldsa_id;
  get_mldsa_id((const hmac_key_t *)&issuer_mldsa_seed, &issuer_mldsa_id);

  // Keymgr Advancement
  hmac_digest_t attest_measurement;
  get_attest_binding(tbs_values, &attest_measurement);

  if (params->subject_params->ecc_cfg->required_keymgr_state ==
      kScKeymgrStateOwnerKey) {
    SEC_MMIO_WRITE_INCREMENT(kScKeymgrSecMmioSwBindingSet +
                             kScKeymgrSecMmioOwnerMaxVerSet);
    HARDENED_RETURN_IF_ERROR(sc_keymgr_owner_advance(
        (keymgr_binding_value_t *)sealing_binding,
        (keymgr_binding_value_t *)&attest_measurement, max_key_version));
  } else {
    SEC_MMIO_WRITE_INCREMENT(kScKeymgrSecMmioSwBindingSet +
                             kScKeymgrSecMmioOwnerIntMaxVerSet);
    HARDENED_RETURN_IF_ERROR(sc_keymgr_owner_int_advance(
        (keymgr_binding_value_t *)&attest_measurement,
        (keymgr_binding_value_t *)sealing_binding, max_key_version));
  }

  // Derive Subject Key & IDs.
  ecdsa_p256_public_key_t subject_ecdsa_pubkey;
  hmac_digest_t *subject_ecdsa_pubkey_id = params->subject_ecdsa_key_id_out;
  HARDENED_RETURN_IF_ERROR(otbn_boot_cert_ecc_p256_keygen(
      *params->subject_params->ecc_cfg, subject_ecdsa_pubkey_id,
      &subject_ecdsa_pubkey));

  keymgr_binding_value_t subject_mldsa_seed;
  HARDENED_RETURN_IF_ERROR(
      dice_mldsa_derive_seed(params->subject_params, &subject_mldsa_seed));
  hmac_digest_t *subject_mldsa_id = params->subject_mldsa_key_id_out;
  get_mldsa_id((const hmac_key_t *)&subject_mldsa_seed, subject_mldsa_id);

  if (regenerate) {
    uint32_t *stack_top =
        (uint32_t *)((uint8_t *)params->scratch_buf + params->scratch_buf_size);

    // Build ECDSA Cert
    tbs_values->key_alg = kCdiHybridKeyAlgEcdsa;
    TEMPLATE_SET(*tbs_values, CdiHybrid, PubKeyEcX, subject_ecdsa_pubkey.x);
    TEMPLATE_SET(*tbs_values, CdiHybrid, PubKeyEcY, subject_ecdsa_pubkey.y);
    TEMPLATE_SET_TRUNCATED(*tbs_values, CdiHybrid, PubKeyId,
                           subject_ecdsa_pubkey_id->digest,
                           kCertKeyIdSizeInBytes);
    TEMPLATE_SET_TRUNCATED(*tbs_values, CdiHybrid, IssuerPubKeyId,
                           issuer_ecdsa_pubkey_id.digest,
                           kCertKeyIdSizeInBytes);

    // Note: The autogenerated `cdi_hybrid_build_cert` function requires the
    // input buffer size to be at least the maximum size of any hybrid
    // certificate (e.g., when containing an ML-DSA signature). Therefore, we
    // use `mldsa_cert_out` (which has sufficient capacity) as a scratch buffer
    // to build the ECDSA certificate, and then copy the resulting smaller
    // certificate into `ecdsa_cert_out`.
    size_t generated_ecdsa_size = params->mldsa_cert_max_size;
    HARDENED_RETURN_IF_ERROR(dice_cdi_hybrid_cert_build(
        tbs_values, &issuer_ecdsa_pubkey, /*signer_mldsa_seed=*/NULL,
        params->mldsa_cert_out, &generated_ecdsa_size, stack_top));

    if (generated_ecdsa_size > params->ecdsa_cert_max_size) {
      return kErrorCertInvalidSize;
    }
    memcpy(params->ecdsa_cert_out, params->mldsa_cert_out,
           generated_ecdsa_size);
    if (params->ecdsa_cert_size_out) {
      *params->ecdsa_cert_size_out = (uint32_t)generated_ecdsa_size;
    }

    // Build ML-DSA Cert
    mldsa44_tiny_pub_from_seed_with_stack(
        pubkey_buffer, (const uint8_t *)subject_mldsa_seed.data, stack_top);

    tbs_values->key_alg = kCdiHybridKeyAlgMldsa44;
    TEMPLATE_SET(*tbs_values, CdiHybrid, PubKeyMldsa, pubkey_buffer);
    TEMPLATE_SET_TRUNCATED(*tbs_values, CdiHybrid, PubKeyId,
                           subject_mldsa_id->digest, kCertKeyIdSizeInBytes);
    TEMPLATE_SET_TRUNCATED(*tbs_values, CdiHybrid, IssuerPubKeyId,
                           issuer_mldsa_id.digest, kCertKeyIdSizeInBytes);

    size_t generated_mldsa_size = params->mldsa_cert_max_size;
    HARDENED_RETURN_IF_ERROR(dice_cdi_hybrid_cert_build(
        tbs_values, /*signer_ecdsa_pubkey=*/NULL,
        (const uint8_t *)issuer_mldsa_seed.data, params->mldsa_cert_out,
        &generated_mldsa_size, stack_top));

    if (generated_mldsa_size > params->mldsa_cert_max_size) {
      return kErrorCertInvalidSize;
    }
    if (params->mldsa_cert_size_out) {
      *params->mldsa_cert_size_out = (uint32_t)generated_mldsa_size;
    }
  }

  // Cleanup
  HARDENED_CHECK_EQ(
      hardened_memshred((uint32_t *)&issuer_mldsa_seed,
                        sizeof(issuer_mldsa_seed) / sizeof(uint32_t))
          .value,
      kHardenedBoolTrue);
  HARDENED_CHECK_EQ(
      hardened_memshred((uint32_t *)&subject_mldsa_seed,
                        sizeof(subject_mldsa_seed) / sizeof(uint32_t))
          .value,
      kHardenedBoolTrue);
  HARDENED_CHECK_EQ(
      hardened_memshred((uint32_t *)params->scratch_buf,
                        params->scratch_buf_size / sizeof(uint32_t))
          .value,
      kHardenedBoolTrue);

  sc_keymgr_sw_binding_unlock_wait();
  return kErrorOk;
}

/**
 * Populates the UDS ML-DSA public key to static_dice_mldsa_cdi.
 */
static rom_error_t dice_mldsa_uds_pubkey_populate(void) {
  keymgr_binding_value_t uds_mldsa_seed;
  HARDENED_RETURN_IF_ERROR(
      dice_mldsa_derive_seed(&kUdsKeygenParams, &uds_mldsa_seed));
  uint32_t *stack_top = (uint32_t *)(mldsa_scratch + sizeof(mldsa_scratch));
  mldsa44_tiny_pub_from_seed_with_stack(static_dice_mldsa_cdi.uds_pub,
                                        (const uint8_t *)uds_mldsa_seed.data,
                                        stack_top);
  static_dice_mldsa_cdi.uds_pub_size = MLDSA44_PUBLIC_KEY_BYTES;
  HARDENED_CHECK_EQ(hardened_memshred((uint32_t *)&uds_mldsa_seed,
                                      sizeof(uds_mldsa_seed) / sizeof(uint32_t))
                        .value,
                    kHardenedBoolTrue);
  return kErrorOk;
}

/* Public CDI 0 API declared in dice.h */
rom_error_t dice_attest_cdi_0(keymgr_binding_value_t *rom_ext_measurement,
                              const manifest_t *rom_ext_manifest) {
  HARDENED_RETURN_IF_ERROR(dice_chain_init());
  HARDENED_RETURN_IF_ERROR(dice_chain_attestation_silicon());
  HARDENED_RETURN_IF_ERROR(ownership_seal_init());

  cdi_hybrid_tbs_values_t cdi0_tbs_values;
  memset(&cdi0_tbs_values, 0, sizeof(cdi0_tbs_values));

  cdi0_tbs_values.tcb_model = "ROM_EXT";
  cdi0_tbs_values.tcb_model_len = sizeof("ROM_EXT") - 1;
  TEMPLATE_CHECK_SIZE(CdiHybrid, TcbModel, sizeof("ROM_EXT") - 1);
  cdi0_tbs_values.tcb_layer = 1;
  cdi0_tbs_values.debug_flag = false;

  hmac_digest_t rom_ext_hash = *(hmac_digest_t *)rom_ext_measurement->data;
  util_reverse_bytes(&rom_ext_hash, sizeof(rom_ext_hash));
  uint8_t fwid_buf[kSha256FwIdSizeBytes];
  encode_sha256_fwid(&fwid_buf[0 * kSha256FwIdSizeBytes], &rom_ext_hash);
  TEMPLATE_SET(cdi0_tbs_values, CdiHybrid, TcbFwIds, fwid_buf);
  TEMPLATE_CHECK_SIZE(CdiHybrid, TcbFwIds, sizeof(fwid_buf));
  cdi0_tbs_values.tcb_fw_ids_size = sizeof(fwid_buf);

  uint32_t rom_ext_security_version_be =
      bitfield_byteswap32(rom_ext_manifest->security_version);
  TEMPLATE_SET(cdi0_tbs_values, CdiHybrid, TcbSvn,
               &rom_ext_security_version_be);

  keymgr_binding_value_t seal_binding_value = {
      .data = {rom_ext_manifest->identifier, 0}};

  retention_sram_t *retram = retention_sram_get();
  dice_cert_gen_msg_t *msg = &retram->creator.dice_cert_gen;
  bool regenerate = msg->hdr.type == kDiceCertGenRequest;

  if (regenerate) {
    HARDENED_RETURN_IF_ERROR(dice_mldsa_uds_pubkey_populate());
  }

  HARDENED_RETURN_IF_ERROR(dice_attest_next_cdi(
      &kCdi0AttestParams, &seal_binding_value,
      rom_ext_manifest->max_key_version, &cdi0_tbs_values, regenerate));

  write_64(read_64(cdi0_mldsa_id.digest), msg->ids.mldsa_cdi0_id);

  return kErrorOk;
}

/* Public CDI 1 API declared in dice.h */
rom_error_t dice_attest_cdi_1(const manifest_t *owner_manifest,
                              keymgr_binding_value_t *bl0_measurement,
                              hmac_digest_t *owner_measurement,
                              hmac_digest_t *owner_history_hash,
                              keymgr_binding_value_t *sealing_binding,
                              owner_app_domain_t key_domain) {
  HARDENED_RETURN_IF_ERROR(dice_chain_init());

  cdi_hybrid_tbs_values_t cdi1_tbs_values;
  memset(&cdi1_tbs_values, 0, sizeof(cdi1_tbs_values));

  cdi1_tbs_values.tcb_model = "Owner";
  cdi1_tbs_values.tcb_model_len = sizeof("Owner") - 1;
  TEMPLATE_CHECK_SIZE(CdiHybrid, TcbModel, sizeof("Owner") - 1);
  cdi1_tbs_values.tcb_layer = 2;
  cdi1_tbs_values.debug_flag = get_debug_mode_cdi1(key_domain);

  hmac_digest_t bl0_hash = *(hmac_digest_t *)bl0_measurement->data;
  util_reverse_bytes(&bl0_hash, sizeof(bl0_hash));

  hmac_digest_t owner_hash = *owner_measurement;
  util_reverse_bytes(&owner_hash, sizeof(owner_hash));

  uint8_t fwids_buf[kSha256FwIdSizeBytes * 3];
  encode_sha256_fwid(&fwids_buf[0 * kSha256FwIdSizeBytes], &bl0_hash);
  encode_sha256_fwid(&fwids_buf[1 * kSha256FwIdSizeBytes], &owner_hash);
  encode_sha256_fwid(&fwids_buf[2 * kSha256FwIdSizeBytes], owner_history_hash);
  TEMPLATE_SET(cdi1_tbs_values, CdiHybrid, TcbFwIds, fwids_buf);
  TEMPLATE_CHECK_SIZE(CdiHybrid, TcbFwIds, sizeof(fwids_buf));
  cdi1_tbs_values.tcb_fw_ids_size = sizeof(fwids_buf);

  uint32_t owner_security_version_be =
      bitfield_byteswap32(owner_manifest->security_version);
  TEMPLATE_SET(cdi1_tbs_values, CdiHybrid, TcbSvn, &owner_security_version_be);

  retention_sram_t *retram = retention_sram_get();
  dice_cert_gen_msg_t *msg = &retram->creator.dice_cert_gen;
  bool regenerate = msg->hdr.type == kDiceCertGenRequest;

  HARDENED_RETURN_IF_ERROR(dice_attest_next_cdi(
      &kCdi1AttestParams, sealing_binding, owner_manifest->max_key_version,
      &cdi1_tbs_values, regenerate));

  write_64(read_64(cdi1_mldsa_id.digest), msg->ids.mldsa_cdi1_id);

  // Handover results to OwnerSw
  if (regenerate) {
    dbg_puts("info: DICE cert cache miss; updating\r\n");

    // Populating ECDSA certs to flash info page.
    RETURN_IF_ERROR(dice_storage_load_page(&dice_page));

    if (static_dice_cdi_0.cert_size != 0) {
      dice_storage_slot_init(&kDiceStorageCdi0Ecdsa, &dice_page);
      memcpy(dice_storage_slot_data(&kDiceStorageCdi0Ecdsa, &dice_page),
             static_dice_cdi_0.cert_data, static_dice_cdi_0.cert_size);
      dice_storage_set_cert_size(&kDiceStorageCdi0Ecdsa,
                                 static_dice_cdi_0.cert_size, &dice_page);
      dice_page.cdi_key_ids[kDicePageKeyIdxCdi0] =
          read_64(static_dice_cdi_0.cdi_0_pubkey_id.digest);
    }

    dice_storage_slot_init(&kDiceStorageCdi1Ecdsa, &dice_page);
    memcpy(dice_storage_slot_data(&kDiceStorageCdi1Ecdsa, &dice_page),
           cdi1_ecdsa_cert_buf, cdi1_ecdsa_size);
    dice_storage_set_cert_size(&kDiceStorageCdi1Ecdsa, cdi1_ecdsa_size,
                               &dice_page);
    dice_page.cdi_key_ids[kDicePageKeyIdxCdi1] = read_64(cdi1_ecdsa_id.digest);

    dice_storage_digest_page(&dice_page, &dice_page.digest);
    HARDENED_RETURN_IF_ERROR(dice_storage_flush_page(&dice_page));

    // Populating ML-DSA certs handover response
    msg->res.mldsa_uds_pub = (uint32_t)&static_dice_mldsa_cdi.uds_pub;
    msg->res.mldsa_uds_pub_len = static_dice_mldsa_cdi.uds_pub_size;

    msg->res.mldsa_cdi0_cert = (uint32_t)static_dice_mldsa_cdi.cdi_0_cert;
    msg->res.mldsa_cdi0_cert_len = static_dice_mldsa_cdi.cdi_0_cert_size;

    msg->res.mldsa_cdi1_cert = (uint32_t)static_dice_mldsa_cdi.cdi_1_cert;
    msg->res.mldsa_cdi1_cert_len = static_dice_mldsa_cdi.cdi_1_cert_size;

    // Update type to response.
    msg->res.hdr.type = kDiceCertGenResponse;
    msg->res.hdr.version = 0;

    // Calculate CRC32 over the whole response struct (including type, IDs,
    // pointers).
    msg->res.crc32 =
        crc32(&msg->res, sizeof(dice_cert_gen_res_t) - sizeof(uint32_t));
  } else {
    // Populating ML-DSA IDs only handover response

    // Update type to IDs (the values are already populated).
    msg->ids.hdr.type = kDiceCertGenIds;
    msg->ids.hdr.version = 0;
  }

  return kErrorOk;
}
