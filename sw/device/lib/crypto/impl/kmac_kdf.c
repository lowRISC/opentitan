
otcrypto_status_t otcrypto_kdf_kmac(
    const otcrypto_blinded_key_t key_derivation_key,
    otcrypto_kmac_mode_t kmac_mode, const otcrypto_const_byte_buf_t kdf_label,
    const otcrypto_const_byte_buf_t kdf_context, size_t required_byte_len,
    otcrypto_blinded_key_t *keying_material) {
  // Check NULL pointers.
  if (key_derivation_key.keyblob == NULL || keying_material == NULL ||
      keying_material->keyblob == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check for null label with nonzero length.
  if (kdf_label.data == NULL && kdf_label.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }
  // Because of KMAC HWIPs prefix limitation, `label` should not exceed
  // `kKmacCustStrMaxSize` bytes.
  if (kdf_label.len > kKmacCustStrMaxSize) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check for null context with nonzero length.
  if (kdf_context.data == NULL && kdf_context.len != 0) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check the private key checksum.
  if (integrity_blinded_key_check(&key_derivation_key) != kHardenedBoolTrue) {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check `key_len` is supported by KMAC HWIP.
  // The set of supported key sizes is {128, 192, 256, 384, 512).
  HARDENED_TRY(kmac_key_length_check(key_derivation_key.config.key_length));

  kmac_blinded_key_t kmac_key = {
      .share0 = NULL,
      .share1 = NULL,
      .hw_backed = key_derivation_key.config.hw_backed,
      .len = key_derivation_key.config.key_length,
  };
  // Validate key length of `key_derivation_key`.
  if (key_derivation_key.config.hw_backed == kHardenedBoolTrue) {
    // Check that 1) key size matches sideload port size, 2) keyblob length
    // matches diversification length.
    if (keyblob_share_num_words(key_derivation_key.config) * sizeof(uint32_t) !=
        kKmacSideloadKeyLength / 8) {
      return OTCRYPTO_BAD_ARGS;
    }
    // Configure keymgr with diversification input and then generate the
    // sideload key.
    keymgr_diversification_t diversification;
    // Diversification call also checks that `key_derivation_key.keyblob_length`
    // is 8 words long.
    HARDENED_TRY(keyblob_to_keymgr_diversification(&key_derivation_key,
                                                   &diversification));
    HARDENED_TRY(keymgr_generate_key_kmac(diversification));
  } else if (key_derivation_key.config.hw_backed == kHardenedBoolFalse) {
    if (key_derivation_key.keyblob_length !=
        keyblob_num_words(key_derivation_key.config) * sizeof(uint32_t)) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_TRY(keyblob_to_shares(&key_derivation_key, &kmac_key.share0,
                                   &kmac_key.share1));
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  // Check non-zero length for keying_material.
  if (required_byte_len == 0) {
    return OTCRYPTO_BAD_ARGS;
  }
  // At the moment, `kmac_kmac_128/256` only supports word-sized digest lenghts.
  if (required_byte_len % sizeof(uint32_t) != 0) {
    return OTCRYPTO_NOT_IMPLEMENTED;
  }

  // Check `keying_material` key length.
  if (keying_material->config.hw_backed == kHardenedBoolTrue) {
    // The case where `keying_material` is hw_backed is addressed by
    // `otcrypto_hw_backed_key` function in `key_transport.h`.
    return OTCRYPTO_BAD_ARGS;
  } else if (keying_material->config.hw_backed == kHardenedBoolFalse) {
    if (keying_material->config.key_length != required_byte_len ||
        keying_material->keyblob_length !=
            keyblob_num_words(keying_material->config) * sizeof(uint32_t)) {
      return OTCRYPTO_BAD_ARGS;
    }
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  if (kmac_mode == kOtcryptoKmacModeKmac128) {
    // Check if `key_mode` of the key derivation key matches `kmac_mode`.
    if (key_derivation_key.config.key_mode != kOtcryptoKeyModeKdfKmac128) {
      return OTCRYPTO_BAD_ARGS;
    }
    // No need to further check key size against security level because
    // `kmac_key_length_check` ensures that the key is at least 128-bit.
    HARDENED_TRY(kmac_kmac_128(
        &kmac_key, /*masked_digest=*/kHardenedBoolTrue, kdf_context.data,
        kdf_context.len, kdf_label.data, kdf_label.len,
        keying_material->keyblob, required_byte_len / sizeof(uint32_t)));
  } else if (kmac_mode == kOtcryptoKmacModeKmac256) {
    // Check if `key_mode` of the key derivation key matches `kmac_mode`.
    if (key_derivation_key.config.key_mode != kOtcryptoKeyModeKdfKmac256) {
      return OTCRYPTO_BAD_ARGS;
    }
    // Check that key size matches the security strength. It should be at least
    // 256-bit.
    if (key_derivation_key.config.key_length < 256 / 8) {
      return OTCRYPTO_BAD_ARGS;
    }
    HARDENED_TRY(kmac_kmac_256(
        &kmac_key, /*masked_digest=*/kHardenedBoolTrue, kdf_context.data,
        kdf_context.len, kdf_label.data, kdf_label.len,
        keying_material->keyblob, required_byte_len / sizeof(uint32_t)));
  } else {
    return OTCRYPTO_BAD_ARGS;
  }

  keying_material->checksum = integrity_blinded_checksum(keying_material);

  if (key_derivation_key.config.hw_backed == kHardenedBoolTrue) {
    HARDENED_TRY(keymgr_sideload_clear_kmac());
  } else if (key_derivation_key.config.hw_backed != kHardenedBoolFalse) {
    return OTCRYPTO_BAD_ARGS;
  }

  return OTCRYPTO_OK;
}
