// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "sw/device/lib/base/crc32.h"
#include "sw/device/lib/base/csr.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/multibits.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/cryptolib_build_info.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/ecc_p256.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/key_transport.h"
#include "sw/device/lib/crypto/include/sha2.h"
#include "sw/device/lib/runtime/hart.h"
#include "sw/device/silicon_creator/lib/attestation.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/base/static_dice_mldsa_cdi.h"
#include "sw/device/silicon_creator/lib/base/util.h"
#include "sw/device/silicon_creator/lib/cert/cert.h"
#include "sw/device/silicon_creator/lib/cert/dice_keys.h"
#include "sw/device/silicon_creator/lib/cert/ram_msg.h"
#include "sw/device/silicon_creator/lib/dbg_print.h"
#include "sw/device/silicon_creator/lib/drivers/flash_ctrl.h"
#include "sw/device/silicon_creator/lib/drivers/retention_sram.h"
#include "sw/device/silicon_creator/lib/drivers/rstmgr.h"
#include "sw/device/silicon_creator/lib/drivers/uart.h"
#include "sw/device/silicon_creator/lib/drivers/watchdog.h"
#include "sw/device/silicon_creator/lib/error.h"
#include "sw/device/silicon_creator/lib/manifest_def.h"
#include "sw/device/silicon_creator/manuf/base/perso_tlv_data.h"
#include "sw/device/silicon_owner/uds_instantiate/uds_mldsa.h"

#include "flash_ctrl_regs.h"
#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

#define MODULE_ID MAKE_MODULE_ID('u', 'd', 'i')

enum {
  kOwnerCertPageCount = 4,
  kOwnerCertStorageBytes =
      kOwnerCertPageCount * FLASH_CTRL_PARAM_BYTES_PER_PAGE,
  kP256CoordBytes = 32,
  kP256PublicKeyBytes = 2 * kP256CoordBytes,
  kP256PublicKeyWords = kP256PublicKeyBytes / sizeof(uint32_t),
  kP256SignatureWords = 64 / sizeof(uint32_t),
  kSha256DigestWords = 32 / sizeof(uint32_t),
  kSleepDurationStepUs = 100 * 1000,
  kSleepStepCount = 100,  // 100 * 100 ms = 10 seconds.
};

static const flash_ctrl_info_page_t
    *const kOwnerReservedCertPages[kOwnerCertPageCount] = {
        &kFlashCtrlInfoPageOwnerReserved0,
        &kFlashCtrlInfoPageOwnerReserved1,
        &kFlashCtrlInfoPageOwnerReserved2,
        &kFlashCtrlInfoPageOwnerReserved3,
};

// ASN.1 DER OID value bytes (without 0x06 tag and length byte).
static const uint8_t kOidSubjectKeyId[] = {0x55, 0x1d, 0x0e};    // 2.5.29.14
static const uint8_t kOidAuthorityKeyId[] = {0x55, 0x1d, 0x23};  // 2.5.29.35
static const uint8_t kOidDiceTcbInfo[] = {
    0x67, 0x81, 0x05, 0x05, 0x04, 0x01,
};  // 2.23.133.5.4.1

// Fixed ASN.1 DER SubjectPublicKeyInfo header for an uncompressed P-256 point.
static const uint8_t kP256SpkiPrefix[] = {
    0x30, 0x59, 0x30, 0x13, 0x06, 0x07, 0x2a, 0x86, 0x48,
    0xce, 0x3d, 0x02, 0x01, 0x06, 0x08, 0x2a, 0x86, 0x48,
    0xce, 0x3d, 0x03, 0x01, 0x07, 0x03, 0x42, 0x00, 0x04,
};

static const char kBase64Table[] =
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

// Static buffers in .bss to keep stack footprint small.
static uint8_t owner_pages_buf[kOwnerCertStorageBytes] OT_WORD_ALIGNED;
static uint8_t verify_pages_buf[kOwnerCertStorageBytes] OT_WORD_ALIGNED;
static uint8_t dice_page_buf[FLASH_CTRL_PARAM_BYTES_PER_PAGE] OT_WORD_ALIGNED;
static uint8_t
    factory_page_buf[FLASH_CTRL_PARAM_BYTES_PER_PAGE] OT_WORD_ALIGNED;
static uint8_t mldsa_uds_pub_buf[kUdsMldsaExactCreatorPubKeyMldsa44SizeBytes];
static uint8_t tcb_ext_buf[kUdsMldsaMaxRawPrivateExtensionsSizeBytes];
static uint8_t tbs_buf[kUdsMldsaMaxTbsSizeBytes];
static uint8_t pq_uds_cert_buf[kUdsMldsaMaxCertSizeBytes];
static char base64_buf[8192];
static otcrypto_state_t crypto_state;

typedef struct asn1_tlv {
  uint8_t tag;
  const uint8_t *tlv_ptr;
  size_t tlv_len;
  const uint8_t *val_ptr;
  size_t val_len;
} asn1_tlv_t;

static bool str_eq(const char *a, const char *b) {
  while (*a != '\0' && *b != '\0') {
    if (*a != *b) {
      return false;
    }
    ++a;
    ++b;
  }
  return *a == *b;
}

static void base64_encode(char *dest, const uint8_t *data, size_t len) {
  for (size_t i = 0; i < len; i += 3) {
    size_t rem = len - i;
    uint32_t val = ((uint32_t)data[i] << 16) |
                   (rem > 1 ? ((uint32_t)data[i + 1] << 8) : 0u) |
                   (rem > 2 ? (uint32_t)data[i + 2] : 0u);
    *dest++ = kBase64Table[(val >> 18) & 0x3fu];
    *dest++ = kBase64Table[(val >> 12) & 0x3fu];
    *dest++ = rem > 1 ? kBase64Table[(val >> 6) & 0x3fu] : '=';
    *dest++ = rem > 2 ? kBase64Table[val & 0x3fu] : '=';
  }
  *dest = '\0';
}

static void print_base64_cert(const char *label, const uint8_t *der,
                              size_t der_len) {
  if ((der_len * 4) / 3 + 5 > sizeof(base64_buf)) {
    dbg_printf("cert too large to print: %s (%u)\r\n", label,
               (unsigned int)der_len);
    return;
  }
  base64_encode(base64_buf, der, der_len);
  dbg_printf("%s: %s\r\n", label, base64_buf);
}

static void sleep_10s_and_reset(void) {
  dbg_puts("Sleeping for 10 seconds before reset...\r\n");
  CSR_CLEAR_BITS(CSR_REG_MCOUNTINHIBIT, 0x1);
  for (size_t i = 0; i < kSleepStepCount; ++i) {
    watchdog_pet();
    busy_spin_micros(kSleepDurationStepUs);
  }
  dbg_puts("Resetting...\r\n");
  while (!uart_tx_idle()) {
  }
  rstmgr_reset();
}

static status_t asn1_next_tlv(const uint8_t **cursor, size_t *rem,
                              asn1_tlv_t *out) {
  if (*rem < 2) {
    return INVALID_ARGUMENT();
  }
  const uint8_t *p = *cursor;
  uint8_t tag = p[0];
  uint8_t len_b0 = p[1];
  size_t hdr_len = 0;
  size_t val_len = 0;
  if ((len_b0 & 0x80u) == 0) {
    hdr_len = 2;
    val_len = len_b0;
  } else {
    size_t num_len_bytes = len_b0 & 0x7fu;
    if (num_len_bytes == 0 || num_len_bytes > 2 || *rem < 2 + num_len_bytes) {
      return INVALID_ARGUMENT();
    }
    hdr_len = 2 + num_len_bytes;
    for (size_t i = 0; i < num_len_bytes; ++i) {
      val_len = (val_len << 8) | p[2 + i];
    }
  }
  if (*rem - hdr_len < val_len) {
    return INVALID_ARGUMENT();
  }
  out->tag = tag;
  out->tlv_ptr = p;
  out->tlv_len = hdr_len + val_len;
  out->val_ptr = p + hdr_len;
  out->val_len = val_len;
  *cursor = p + out->tlv_len;
  *rem -= out->tlv_len;
  return OK_STATUS();
}

static status_t x509_get_tbs(const uint8_t *cert_der, size_t cert_len,
                             asn1_tlv_t *tbs_out) {
  const uint8_t *cur = cert_der;
  size_t rem = cert_len;
  asn1_tlv_t cert_seq;
  TRY(asn1_next_tlv(&cur, &rem, &cert_seq));
  if (cert_seq.tag != 0x30) {
    return INVALID_ARGUMENT();
  }
  const uint8_t *cert_cur = cert_seq.val_ptr;
  size_t cert_rem = cert_seq.val_len;
  TRY(asn1_next_tlv(&cert_cur, &cert_rem, tbs_out));
  if (tbs_out->tag != 0x30) {
    return INVALID_ARGUMENT();
  }
  return OK_STATUS();
}

static status_t x509_find_extension_by_oid(const uint8_t *cert_der,
                                           size_t cert_len,
                                           const uint8_t *oid_val,
                                           size_t oid_val_len,
                                           asn1_tlv_t *ext_seq_out,
                                           asn1_tlv_t *ext_val_octet_out) {
  asn1_tlv_t tbs_seq;
  TRY(x509_get_tbs(cert_der, cert_len, &tbs_seq));

  const uint8_t *tbs_cur = tbs_seq.val_ptr;
  size_t tbs_rem = tbs_seq.val_len;
  while (tbs_rem > 0) {
    asn1_tlv_t field;
    TRY(asn1_next_tlv(&tbs_cur, &tbs_rem, &field));
    if (field.tag != 0xa3) {
      continue;
    }
    const uint8_t *a3_cur = field.val_ptr;
    size_t a3_rem = field.val_len;
    asn1_tlv_t exts_seq;
    TRY(asn1_next_tlv(&a3_cur, &a3_rem, &exts_seq));
    if (exts_seq.tag != 0x30) {
      return INVALID_ARGUMENT();
    }
    const uint8_t *exts_cur = exts_seq.val_ptr;
    size_t exts_rem = exts_seq.val_len;
    while (exts_rem > 0) {
      asn1_tlv_t ext_seq;
      TRY(asn1_next_tlv(&exts_cur, &exts_rem, &ext_seq));
      if (ext_seq.tag != 0x30) {
        return INVALID_ARGUMENT();
      }
      const uint8_t *ext_cur = ext_seq.val_ptr;
      size_t ext_rem = ext_seq.val_len;
      asn1_tlv_t oid_tlv;
      TRY(asn1_next_tlv(&ext_cur, &ext_rem, &oid_tlv));
      if (oid_tlv.tag != 0x06) {
        return INVALID_ARGUMENT();
      }
      asn1_tlv_t next_tlv;
      TRY(asn1_next_tlv(&ext_cur, &ext_rem, &next_tlv));
      if (next_tlv.tag == 0x01) {
        TRY(asn1_next_tlv(&ext_cur, &ext_rem, &next_tlv));
      }
      if (next_tlv.tag != 0x04) {
        return INVALID_ARGUMENT();
      }
      if (oid_tlv.val_len == oid_val_len &&
          memcmp(oid_tlv.val_ptr, oid_val, oid_val_len) == 0) {
        *ext_seq_out = ext_seq;
        *ext_val_octet_out = next_tlv;
        return OK_STATUS();
      }
    }
  }
  return NOT_FOUND();
}

static status_t x509_extract_aki_key_id(
    const uint8_t *cert_der, size_t cert_len,
    uint8_t key_id_out[kCertKeyIdSizeInBytes]) {
  asn1_tlv_t ext_seq;
  asn1_tlv_t ext_val;
  TRY(x509_find_extension_by_oid(cert_der, cert_len, kOidAuthorityKeyId,
                                 sizeof(kOidAuthorityKeyId), &ext_seq,
                                 &ext_val));
  const uint8_t *cur = ext_val.val_ptr;
  size_t rem = ext_val.val_len;
  asn1_tlv_t aki_seq;
  TRY(asn1_next_tlv(&cur, &rem, &aki_seq));
  if (aki_seq.tag != 0x30) {
    return INVALID_ARGUMENT();
  }
  const uint8_t *aki_cur = aki_seq.val_ptr;
  size_t aki_rem = aki_seq.val_len;
  asn1_tlv_t key_id_tlv;
  TRY(asn1_next_tlv(&aki_cur, &aki_rem, &key_id_tlv));
  if (key_id_tlv.tag != 0x80 || key_id_tlv.val_len != kCertKeyIdSizeInBytes) {
    return INVALID_ARGUMENT();
  }
  memcpy(key_id_out, key_id_tlv.val_ptr, kCertKeyIdSizeInBytes);
  return OK_STATUS();
}

static status_t x509_extract_ski_key_id(
    const uint8_t *cert_der, size_t cert_len,
    uint8_t key_id_out[kCertKeyIdSizeInBytes]) {
  asn1_tlv_t ext_seq;
  asn1_tlv_t ext_val;
  TRY(x509_find_extension_by_oid(cert_der, cert_len, kOidSubjectKeyId,
                                 sizeof(kOidSubjectKeyId), &ext_seq, &ext_val));
  const uint8_t *cur = ext_val.val_ptr;
  size_t rem = ext_val.val_len;
  asn1_tlv_t ski_octet;
  TRY(asn1_next_tlv(&cur, &rem, &ski_octet));
  if (ski_octet.tag != 0x04 || ski_octet.val_len != kCertKeyIdSizeInBytes) {
    return INVALID_ARGUMENT();
  }
  memcpy(key_id_out, ski_octet.val_ptr, kCertKeyIdSizeInBytes);
  return OK_STATUS();
}

static status_t x509_extract_p256_pubkey(
    const uint8_t *cert_der, size_t cert_len,
    uint8_t pk_be_out[kP256PublicKeyBytes]) {
  asn1_tlv_t tbs_seq;
  TRY(x509_get_tbs(cert_der, cert_len, &tbs_seq));

  const uint8_t *cur = tbs_seq.val_ptr;
  size_t rem = tbs_seq.val_len;
  asn1_tlv_t field;
  TRY(asn1_next_tlv(&cur, &rem, &field));
  // Skip optional explicit [0] version.
  if (field.tag == 0xa0) {
    TRY(asn1_next_tlv(&cur, &rem, &field));
  }
  // serialNumber (INTEGER), signature (SEQUENCE), issuer (SEQUENCE),
  // validity (SEQUENCE), subject (SEQUENCE), subjectPublicKeyInfo (SEQUENCE).
  if (field.tag != 0x02) {
    return INVALID_ARGUMENT();
  }
  for (size_t i = 0; i < 5; ++i) {
    TRY(asn1_next_tlv(&cur, &rem, &field));
  }
  if (field.tlv_len != sizeof(kP256SpkiPrefix) + kP256PublicKeyBytes ||
      memcmp(field.tlv_ptr, kP256SpkiPrefix, sizeof(kP256SpkiPrefix)) != 0) {
    return INVALID_ARGUMENT();
  }
  memcpy(pk_be_out, field.tlv_ptr + sizeof(kP256SpkiPrefix),
         kP256PublicKeyBytes);
  return OK_STATUS();
}

static void configure_owner_cert_pages(bool writable) {
  const flash_ctrl_cfg_t kCfg = {
      .scrambling = kMultiBitBool4True,
      .ecc = kMultiBitBool4True,
      .he = kMultiBitBool4False,
  };
  const flash_ctrl_perms_t kPerms = {
      .read = kMultiBitBool4True,
      .write = writable ? kMultiBitBool4True : kMultiBitBool4False,
      .erase = writable ? kMultiBitBool4True : kMultiBitBool4False,
  };
  for (size_t i = 0; i < ARRAYSIZE(kOwnerReservedCertPages); ++i) {
    flash_ctrl_info_cfg_set(kOwnerReservedCertPages[i], kCfg);
    flash_ctrl_info_perms_set(kOwnerReservedCertPages[i], kPerms);
  }
}

static status_t read_owner_cert_pages_tolerant(uint8_t *buf) {
  for (size_t i = 0; i < ARRAYSIZE(kOwnerReservedCertPages); ++i) {
    TRY(flash_ctrl_info_read_zeros_on_read_error(
        kOwnerReservedCertPages[i], /*offset=*/0,
        util_size_to_words(FLASH_CTRL_PARAM_BYTES_PER_PAGE),
        buf + i * FLASH_CTRL_PARAM_BYTES_PER_PAGE));
  }
  return OK_STATUS();
}

static status_t find_cert_in_tlv_buf(const uint8_t *buf, size_t buf_size,
                                     const char *cert_name,
                                     perso_tlv_cert_obj_view_t *out_obj) {
  size_t offset = 0;
  while (offset < buf_size) {
    perso_tlv_cert_obj_view_t obj = {0};
    rom_error_t err =
        perso_tlv_get_cert_obj_view(buf + offset, buf_size - offset, &obj);
    if (err != kErrorOk) {
      break;
    }
    if (obj.obj_type == kPersoObjectTypeX509Cert &&
        str_eq(obj.name, cert_name)) {
      *out_obj = obj;
      return OK_STATUS();
    }
    size_t step = util_round_up_to((uint32_t)obj.obj_size, 3);
    if (step == 0 || step > buf_size - offset) {
      break;
    }
    offset += step;
  }
  return NOT_FOUND();
}

static void print_saved_owner_certs(const uint8_t *buf, size_t buf_size) {
  size_t offset = 0;
  while (offset < buf_size) {
    perso_tlv_cert_obj_view_t obj = {0};
    rom_error_t err =
        perso_tlv_get_cert_obj_view(buf + offset, buf_size - offset, &obj);
    if (err != kErrorOk) {
      break;
    }
    if (obj.obj_type == kPersoObjectTypeX509Cert) {
      if (str_eq(obj.name, "PQ_UDS_44")) {
        print_base64_cert("SAVED_PQ_UDS_44", obj.cert_body_p,
                          obj.cert_body_size);
      } else if (str_eq(obj.name, "CDI_1")) {
        print_base64_cert("SAVED_CDI_1", obj.cert_body_p, obj.cert_body_size);
      } else if (str_eq(obj.name, "CDI_0")) {
        print_base64_cert("SAVED_CDI_0", obj.cert_body_p, obj.cert_body_size);
      }
    }
    size_t step = util_round_up_to((uint32_t)obj.obj_size, 3);
    if (step == 0 || step > buf_size - offset) {
      break;
    }
    offset += step;
  }
}

static status_t endorse_tbs_with_cdi1(
    const uint8_t *tbs, size_t tbs_size,
    const uint8_t expected_pk_be[kP256PublicKeyBytes],
    const uint8_t expected_ski[kCertKeyIdSizeInBytes], uint8_t sig_r_be[32],
    uint8_t sig_s_be[32]) {
  watchdog_pet();
  TRY(otcrypto_init(kOtcryptoKeySecurityLevelLow, &crypto_state));

  // Verify that SHA256(cdi1_pk_be)[0..20] matches CDI_1's SKI.
  otcrypto_const_byte_buf_t pk_msg = OTCRYPTO_MAKE_BUF(
      otcrypto_const_byte_buf_t, expected_pk_be, kP256PublicKeyBytes);
  uint32_t pk_digest_words[kSha256DigestWords] = {0};
  otcrypto_hash_digest_t pk_digest = {
      .data = pk_digest_words,
      .len = ARRAYSIZE(pk_digest_words),
  };
  TRY(otcrypto_sha2_256(&pk_msg, &pk_digest));
  if (memcmp(pk_digest_words, expected_ski, kCertKeyIdSizeInBytes) != 0) {
    dbg_puts("error: CDI_1 SKI does not match SHA256(pubkey)\r\n");
    return INTERNAL();
  }

  // Load the CDI_1 attestation seed from bank=0, page=4 (falling back to all
  // zeros if unprovisioned, matching ROM_EXT's load_attestation_keygen_seed).
  uint32_t attestation_seed_words[kAttestationSeedWords] = {0};
  uint32_t seed_offset = kDiceKeyCdi1.keygen_seed_idx * kAttestationSeedBytes;
  TRY(flash_ctrl_info_read_zeros_on_read_error(
      &kFlashCtrlInfoPageAttestationKeySeeds, seed_offset,
      kAttestationSeedWords, attestation_seed_words));
  otcrypto_const_word32_buf_t attestation_seed =
      OTCRYPTO_MAKE_BUF(otcrypto_const_word32_buf_t, attestation_seed_words,
                        ARRAYSIZE(attestation_seed_words));

  // Construct hardware-backed CDI_1 attestation key handle.
  otcrypto_key_config_t key_cfg = {
      .version = otcrypto_lib_version(),
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = kP256CoordBytes,
      .hw_backed = kHardenedBoolTrue,
      .security_level = kOtcryptoKeySecurityLevelLow,
  };
  uint32_t keyblob[9] = {0};
  otcrypto_blinded_key_t cdi1_priv_key = {
      .config = key_cfg,
      .keyblob_length = sizeof(keyblob),
      .keyblob = keyblob,
  };
  TRY(otcrypto_hw_backed_attestation_key(
      kDiceKeyCdi1.keymgr_diversifier->version,
      kDiceKeyCdi1.keymgr_diversifier->salt, &cdi1_priv_key));

  // Derive CDI_1 public key via OTBN and confirm it matches CDI_1 X.509 cert.
  uint32_t derived_pk_words[kP256PublicKeyWords] = {0};
  otcrypto_unblinded_key_t cdi1_pub_key = {
      .key_mode = kOtcryptoKeyModeEcdsaP256,
      .key_length = sizeof(derived_pk_words),
      .key = derived_pk_words,
  };
  watchdog_pet();
  TRY(otcrypto_ecdsa_p256_dice_keygen(&cdi1_priv_key, &cdi1_pub_key,
                                      &attestation_seed));

  uint8_t derived_pk_be[kP256PublicKeyBytes];
  memcpy(derived_pk_be, derived_pk_words, sizeof(derived_pk_be));
  util_reverse_bytes(derived_pk_be, kP256CoordBytes);
  util_reverse_bytes(derived_pk_be + kP256CoordBytes, kP256CoordBytes);
  if (memcmp(derived_pk_be, expected_pk_be, kP256PublicKeyBytes) != 0) {
    dbg_puts("error: derived CDI_1 public key mismatch\r\n");
    return INTERNAL();
  }

  // Hash the PQ_UDS_44 TBS certificate with SHA-256.
  otcrypto_const_byte_buf_t tbs_msg =
      OTCRYPTO_MAKE_BUF(otcrypto_const_byte_buf_t, tbs, tbs_size);
  uint32_t tbs_digest_words[kSha256DigestWords] = {0};
  otcrypto_hash_digest_t tbs_digest = {
      .data = tbs_digest_words,
      .len = ARRAYSIZE(tbs_digest_words),
  };
  TRY(otcrypto_sha2_256(&tbs_msg, &tbs_digest));

  // Sign the TBS digest with the hardware-backed CDI_1 private key.
  uint32_t sig_words[kP256SignatureWords] = {0};
  otcrypto_word32_buf_t sig_buf =
      OTCRYPTO_MAKE_BUF(otcrypto_word32_buf_t, sig_words, ARRAYSIZE(sig_words));
  watchdog_pet();
  TRY(otcrypto_ecdsa_p256_dice_sign_async_start(&cdi1_priv_key, tbs_digest,
                                                &attestation_seed));
  TRY(otcrypto_ecdsa_p256_dice_sign_async_finalize(&sig_buf));

  // Verify the signature on-device before persisting to flash.
  otcrypto_const_word32_buf_t const_sig_buf = OTCRYPTO_MAKE_BUF(
      otcrypto_const_word32_buf_t, sig_words, ARRAYSIZE(sig_words));
  hardened_bool_t verify_ok = kHardenedBoolFalse;
  watchdog_pet();
  TRY(otcrypto_ecdsa_p256_verify(&cdi1_pub_key, tbs_digest, &const_sig_buf,
                                 &verify_ok));
  if (verify_ok != kHardenedBoolTrue) {
    dbg_puts("error: on-device CDI_1 signature verification failed\r\n");
    return INTERNAL();
  }

  // Convert (r, s) from little-endian OTBN word order to big-endian bytes.
  util_p256_signature_le_to_be_convert(&sig_words[0], &sig_words[8]);
  memcpy(sig_r_be, &sig_words[0], 32);
  memcpy(sig_s_be, &sig_words[8], 32);
  return OK_STATUS();
}

static status_t pack_and_store_owner_certs(
    const uint8_t *pq_uds_der, size_t pq_uds_len, const uint8_t *cdi1_der,
    size_t cdi1_len, const uint8_t *cdi0_der, size_t cdi0_len) {
  memset(owner_pages_buf, 0, sizeof(owner_pages_buf));

  struct {
    const char *name;
    const uint8_t *der;
    size_t len;
  } certs[3] = {
      {.name = "PQ_UDS_44", .der = pq_uds_der, .len = pq_uds_len},
      {.name = "CDI_1", .der = cdi1_der, .len = cdi1_len},
      {.name = "CDI_0", .der = cdi0_der, .len = cdi0_len},
  };

  size_t offset = 0;
  for (size_t i = 0; i < ARRAYSIZE(certs); ++i) {
    if (offset >= sizeof(owner_pages_buf)) {
      return INTERNAL();
    }
    size_t obj_size = sizeof(owner_pages_buf) - offset;
    TRY(perso_tlv_cert_obj_build(
        certs[i].name, kPersoObjectTypeX509Cert, certs[i].der, certs[i].len,
        kPersoBlobVersionV1, owner_pages_buf + offset, &obj_size));
    offset = util_round_up_to((uint32_t)(offset + obj_size), 3);
  }
  if (offset > sizeof(owner_pages_buf)) {
    return INTERNAL();
  }

  // Erase, program, and verify bank=0, pages=5-8 (OwnerReserved0..3).
  configure_owner_cert_pages(/*writable=*/true);
  for (size_t i = 0; i < ARRAYSIZE(kOwnerReservedCertPages); ++i) {
    watchdog_pet();
    TRY(flash_ctrl_info_erase(kOwnerReservedCertPages[i],
                              kFlashCtrlEraseTypePage));
    TRY(flash_ctrl_info_write(
        kOwnerReservedCertPages[i], /*offset=*/0,
        util_size_to_words(FLASH_CTRL_PARAM_BYTES_PER_PAGE),
        owner_pages_buf + i * FLASH_CTRL_PARAM_BYTES_PER_PAGE));
  }
  configure_owner_cert_pages(/*writable=*/false);

  memset(verify_pages_buf, 0, sizeof(verify_pages_buf));
  for (size_t i = 0; i < ARRAYSIZE(kOwnerReservedCertPages); ++i) {
    TRY(flash_ctrl_info_read(
        kOwnerReservedCertPages[i], /*offset=*/0,
        util_size_to_words(FLASH_CTRL_PARAM_BYTES_PER_PAGE),
        verify_pages_buf + i * FLASH_CTRL_PARAM_BYTES_PER_PAGE));
  }
  if (memcmp(owner_pages_buf, verify_pages_buf, sizeof(owner_pages_buf)) != 0) {
    dbg_puts("error: flash readback mismatch on OwnerReserved0..3\r\n");
    return INTERNAL();
  }

  for (size_t i = 0; i < ARRAYSIZE(certs); ++i) {
    perso_tlv_cert_obj_view_t view = {0};
    TRY(find_cert_in_tlv_buf(verify_pages_buf, sizeof(verify_pages_buf),
                             certs[i].name, &view));
    if (view.cert_body_size != certs[i].len ||
        memcmp(view.cert_body_p, certs[i].der, certs[i].len) != 0) {
      dbg_printf("error: stored TLV verification failed for %s\r\n",
                 certs[i].name);
      return INTERNAL();
    }
  }
  return OK_STATUS();
}

static status_t uds_instantiate_run(void) {
  sec_mmio_init();
  watchdog_pet();

  retention_sram_t *retram = retention_sram_get();
  dice_cert_gen_msg_t *msg = &retram->creator.dice_cert_gen;

  // Step 1: Idempotency check on bank=0, pages=5-8 (OwnerReserved0..3).
  configure_owner_cert_pages(/*writable=*/false);
  memset(owner_pages_buf, 0, sizeof(owner_pages_buf));
  TRY(read_owner_cert_pages_tolerant(owner_pages_buf));

  perso_tlv_cert_obj_view_t existing_pq_uds = {0};
  rom_error_t tlv_err = perso_tlv_get_cert_obj_view(
      owner_pages_buf, sizeof(owner_pages_buf), &existing_pq_uds);
  if (tlv_err == kErrorOk &&
      existing_pq_uds.obj_type == kPersoObjectTypeX509Cert &&
      str_eq(existing_pq_uds.name, "PQ_UDS_44")) {
    dbg_printf("Found valid existing PQ_UDS_44 (%u bytes); doing nothing.\r\n",
               (unsigned int)existing_pq_uds.cert_body_size);
    msg->hdr.type = 0;
    print_saved_owner_certs(owner_pages_buf, sizeof(owner_pages_buf));
    dbg_puts("UDS_INSTANTIATE: ALREADY_PRESENT\r\n");
    return OK_STATUS();
  }

  // Step 2: Capture MLDSA-44 UDS from RET-RAM + static_dice_mldsa_cdi handoff.
  uint32_t msg_type = msg->hdr.type;
  if (msg_type != kDiceCertGenIds && msg_type != kDiceCertGenResponse) {
    dbg_printf("error: unsupported ROM_EXT handoff type 0x%x\r\n",
               (unsigned int)msg_type);
    return INTERNAL();
  }

  if (msg_type == kDiceCertGenIds || msg->res.mldsa_uds_pub_len == 0) {
    dbg_puts("Requesting ML-DSA UDS pubkey and certs via warm reboot...\r\n");
    msg->hdr.type = kDiceCertGenRequest;
    msg->hdr.version = 0;
    while (!uart_tx_idle()) {
    }
    rstmgr_reset();
    return INTERNAL();
  }

  dice_cert_gen_res_t *res = &msg->res;
  uint32_t expected_crc =
      crc32(res, sizeof(dice_cert_gen_res_t) - sizeof(uint32_t));
  if (expected_crc != res->crc32) {
    dbg_printf("error: RET-RAM handoff CRC mismatch (0x%x vs 0x%x)\r\n",
               (unsigned int)expected_crc, (unsigned int)res->crc32);
    return INTERNAL();
  }
  if (res->mldsa_uds_pub != (uint32_t)static_dice_mldsa_cdi.uds_pub ||
      res->mldsa_uds_pub_len != sizeof(mldsa_uds_pub_buf)) {
    dbg_printf("error: unexpected MLDSA-44 UDS pubkey ptr=0x%x len=%u\r\n",
               (unsigned int)res->mldsa_uds_pub,
               (unsigned int)res->mldsa_uds_pub_len);
    return INTERNAL();
  }
  if (res->mldsa_cdi0_cert == 0 || res->mldsa_cdi0_cert_len == 0 ||
      res->mldsa_cdi1_cert == 0 || res->mldsa_cdi1_cert_len == 0) {
    dbg_puts("error: ML-DSA CDI_0/CDI_1 certificates missing in handoff\r\n");
    return INTERNAL();
  }
  memcpy(mldsa_uds_pub_buf, (const void *)res->mldsa_uds_pub,
         sizeof(mldsa_uds_pub_buf));

  const uint8_t *live_pq_cdi0_der = (const uint8_t *)res->mldsa_cdi0_cert;
  size_t live_pq_cdi0_len = res->mldsa_cdi0_cert_len;
  const uint8_t *live_pq_cdi1_der = (const uint8_t *)res->mldsa_cdi1_cert;
  size_t live_pq_cdi1_len = res->mldsa_cdi1_cert_len;

  // Step 3: Read P-256 CDI_0 and CDI_1 from kFlashCtrlInfoPageDiceCerts, and
  // extract untweaked key IDs + CDI_1 P-256 public key.
  memset(dice_page_buf, 0, sizeof(dice_page_buf));
  TRY(flash_ctrl_info_read(&kFlashCtrlInfoPageDiceCerts, /*offset=*/0,
                           util_size_to_words(sizeof(dice_page_buf)),
                           dice_page_buf));
  perso_tlv_cert_obj_view_t cdi0_obj = {0};
  perso_tlv_cert_obj_view_t cdi1_obj = {0};
  TRY(find_cert_in_tlv_buf(dice_page_buf, sizeof(dice_page_buf), "CDI_0",
                           &cdi0_obj));
  TRY(find_cert_in_tlv_buf(dice_page_buf, sizeof(dice_page_buf), "CDI_1",
                           &cdi1_obj));

  uint8_t creator_pub_key_id[kCertKeyIdSizeInBytes] = {0};
  TRY(x509_extract_aki_key_id(live_pq_cdi0_der, live_pq_cdi0_len,
                              creator_pub_key_id));

  uint8_t auth_key_key_id[kCertKeyIdSizeInBytes] = {0};
  TRY(x509_extract_ski_key_id(cdi1_obj.cert_body_p, cdi1_obj.cert_body_size,
                              auth_key_key_id));

  uint8_t cdi1_pk_be[kP256PublicKeyBytes] = {0};
  TRY(x509_extract_p256_pubkey(cdi1_obj.cert_body_p, cdi1_obj.cert_body_size,
                               cdi1_pk_be));

  // Step 4: Copy dice_tcb_info extension from factory P-256 "UDS" certificate
  // in kFlashCtrlInfoPageFactoryCerts (bank=0, page=9) if present.
  memset(factory_page_buf, 0, sizeof(factory_page_buf));
  memset(tcb_ext_buf, 0, sizeof(tcb_ext_buf));
  size_t tcb_ext_len = 0;
  bool has_factory_uds = false;
  perso_tlv_cert_obj_view_t factory_uds_obj = {0};

  TRY(flash_ctrl_info_read_zeros_on_read_error(
      &kFlashCtrlInfoPageFactoryCerts, /*offset=*/0,
      util_size_to_words(sizeof(factory_page_buf)), factory_page_buf));
  if (status_ok(find_cert_in_tlv_buf(factory_page_buf, sizeof(factory_page_buf),
                                     "UDS", &factory_uds_obj))) {
    has_factory_uds = true;
    asn1_tlv_t tcb_ext_seq = {0};
    asn1_tlv_t tcb_ext_val = {0};
    if (status_ok(x509_find_extension_by_oid(
            factory_uds_obj.cert_body_p, factory_uds_obj.cert_body_size,
            kOidDiceTcbInfo, sizeof(kOidDiceTcbInfo), &tcb_ext_seq,
            &tcb_ext_val))) {
      if (tcb_ext_seq.tlv_len > sizeof(tcb_ext_buf)) {
        dbg_printf("error: factory UDS dice_tcb_info too large (%u)\r\n",
                   (unsigned int)tcb_ext_seq.tlv_len);
        return INTERNAL();
      }
      memcpy(tcb_ext_buf, tcb_ext_seq.tlv_ptr, tcb_ext_seq.tlv_len);
      tcb_ext_len = tcb_ext_seq.tlv_len;
      dbg_printf(
          "Copied dice_tcb_info extension (%u bytes) from factory UDS.\r\n",
          (unsigned int)tcb_ext_len);
    } else {
      dbg_puts("warning: factory UDS has no dice_tcb_info extension.\r\n");
    }
  } else {
    dbg_puts(
        "warning: no factory P-256 UDS cert found; omitting "
        "dice_tcb_info.\r\n");
  }

  // Step 5: Construct PQ_UDS_44 TBS, endorse with hardware-backed P-256 CDI_1,
  // and build final X.509 certificate.
  uds_mldsa_tbs_values_t tbs_values = {
      .creator_pub_key_mldsa_44 = mldsa_uds_pub_buf,
      .creator_pub_key_id = creator_pub_key_id,
      .auth_key_key_id = auth_key_key_id,
      .raw_private_extensions = tcb_ext_buf,
      .raw_private_extensions_size = tcb_ext_len,
  };
  size_t tbs_size = sizeof(tbs_buf);
  TRY(uds_mldsa_build_tbs(&tbs_values, tbs_buf, &tbs_size));

  uint8_t sig_r_be[32] = {0};
  uint8_t sig_s_be[32] = {0};
  TRY(endorse_tbs_with_cdi1(tbs_buf, tbs_size, cdi1_pk_be, auth_key_key_id,
                            sig_r_be, sig_s_be));

  uds_mldsa_cert_values_t cert_values = {
      .cert_signature_r = sig_r_be,
      .cert_signature_s = sig_s_be,
      .tbs = tbs_buf,
      .tbs_size = tbs_size,
  };
  size_t pq_uds_cert_size = sizeof(pq_uds_cert_buf);
  TRY(uds_mldsa_build_cert(&cert_values, pq_uds_cert_buf, &pq_uds_cert_size));
  dbg_printf("Constructed and endorsed PQ_UDS_44 (%u bytes).\r\n",
             (unsigned int)pq_uds_cert_size);

  // Step 6: Store PQ_UDS_44, CDI_1, and CDI_0 into bank=0, pages=5-8 with V1
  // perso_tlv headers.
  TRY(pack_and_store_owner_certs(
      pq_uds_cert_buf, pq_uds_cert_size, cdi1_obj.cert_body_p,
      cdi1_obj.cert_body_size, cdi0_obj.cert_body_p, cdi0_obj.cert_body_size));
  msg->hdr.type = 0;

  // Step 7: Print certificates and status.
  if (has_factory_uds) {
    print_base64_cert("FACTORY_UDS", factory_uds_obj.cert_body_p,
                      factory_uds_obj.cert_body_size);
  }
  print_saved_owner_certs(verify_pages_buf, sizeof(verify_pages_buf));
  print_base64_cert("LIVE_PQ_CDI_0", live_pq_cdi0_der, live_pq_cdi0_len);
  print_base64_cert("LIVE_PQ_CDI_1", live_pq_cdi1_der, live_pq_cdi1_len);
  dbg_puts("UDS_INSTANTIATE: CREATED\r\n");
  return OK_STATUS();
}

void bare_metal_main(void) {
  status_t sts = uds_instantiate_run();
  if (status_err(sts)) {
    dbg_printf("UDS_INSTANTIATE_ERROR: status=0x%x\r\n",
               (unsigned int)sts.value);
  }
  sleep_10s_and_reset();
}

void interrupt_handler(void) {
  dbg_puts("UDS_INSTANTIATE_ERROR: unexpected trap/interrupt\r\n");
  while (!uart_tx_idle()) {
  }
  rstmgr_reset();
}

void exception_handler(void) __attribute__((alias("interrupt_handler")));
void nmi_handler(void) __attribute__((alias("interrupt_handler")));
