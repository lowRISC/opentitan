/**
 * Performs the key derivation function with single KMAC invocation according to
 * NIST SP 800-108r1.
 *
 * This function initially validates the `key_derivation_key` struct, by
 * checking for NULL pointers, checking whether key length and its
 * keyblob_length match each other, verifying its checksum etc. Moreover, its
 * `hw_backed` field is used to determine whether the derivation key comes from
 * Keymgr. In that case, this function requests Keymgr to generate the key
 * according to diversification values passed in keyblob.
 * (see `keyblob_buffer_to_keymgr_diversification` function in `keyblob.h`).
 * For non-hardware-backed keys, the keyblob should be twice the length of the
 * key.
 *
 * `kmac_mode` input argument is used to decide whether KMAC128 or KMAC256 is
 * used and it is also checked against `key_mode` from `key_derivation_key`.
 *
 * The produced key is returned in the `keying_material` blinded key struct.
 * The caller should allocate and partially populate `keying_material`,
 * including populating the key configuration and allocating space for the
 * keyblob. The key length is also checked against `required_byte_len`. The
 * value in the `checksum` field of the blinded key struct will be populated
 * by this function. The use case where `keying_material` needs to be hw-backed
 * is not supported by this function, hence `hw_backed` must be set tofalse.
 * See `otcrypto_hw_backed_key` from `key_transport` for that specific use case.
 *
 * Note that it is the responsibility of the user of `keying_material` to
 * further validate the key configuration. While populating the key, this
 * function ignores `exportable`, `key_mode`, and `security_level` fields
 * therefore the users must validate their `keying_material` config before use.
 *
 * @param key_derivation_key Blinded key derivation key.
 * @param kmac_mode Either KMAC128 or KMAC256 as PRF.
 * @param kdf_label Label string according to SP 800-108r1.
 * @param kdf_context Context string according to SP 800-108r1.
 * @param required_byte_len Required length of the derived key in bytes.
 * @param[out] keying_material Pointer to the blinded keying material to be
 * populated by this function.
 * @return Result of the key derivation operation.
 */
otcrypto_status_t otcrypto_kdf_kmac(
    const otcrypto_blinded_key_t key_derivation_key,
    otcrypto_kmac_mode_t kmac_mode, const otcrypto_const_byte_buf_t kdf_label,
    const otcrypto_const_byte_buf_t kdf_context, size_t required_byte_len,
    otcrypto_blinded_key_t *keying_material);
