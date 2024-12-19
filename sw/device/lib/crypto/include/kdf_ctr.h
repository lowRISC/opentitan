/**
 * Performs the key derivation function in counter mode wtih HMAC according to
 * NIST SP 800-108r1.
 *
 * The supported PRF engine for the KDF function is HMAC (since KMAC does not
 * use the counter mode).
 *
 * The caller should allocate and partially populate the `keying_material`
 * blinded key struct, including populating the key configuration and
 * allocating space for the keyblob. The caller should indicate the length of
 * the allocated keyblob; this function will return an error if the keyblob
 * length does not match expectations. For hardware-backed keys, the keyblob
 * expectations. If the key is hardware-backed, the caller should pass a fully
 * populated private key handle such as the kind returned by
 * `otcrypto_hw_backed_key`. For non-hardware-backed keys, the keyblob should
 * be twice the length of the key. The value in the `checksum` field of the
 * blinded key struct will be populated by this function.
 *
 * @param key_derivation_key Blinded key derivation key.
 * @param kdf_label Label string according to SP 800-108r1.
 * @param kdf_context Context string according to SP 800-108r1.
 * @param required_byte_len Required length of the derived key in bytes.
 * @param[out] keying_material Pointer to the blinded keying material to be
 * populated by this function.
 * @return Result of the key derivation operation.
 */
otcrypto_status_t otcrypto_kdf_hmac_ctr(
    const otcrypto_blinded_key_t key_derivation_key,
    const otcrypto_const_byte_buf_t kdf_label,
    const otcrypto_const_byte_buf_t kdf_context, size_t required_byte_len,
    otcrypto_blinded_key_t *keying_material);
