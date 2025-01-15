

/**
 * Enum to define KMAC mode.
 *
 * Values are hardened.
 */
typedef enum otcrypto_kmac_mode {
  // KMAC128 mode.
  kOtcryptoKmacModeKmac128 = 0x336,
  // KMAC256 mode.
  kOtcryptoKmacModeKmac256 = 0xec4,
} otcrypto_kmac_mode_t;

/**
 * Performs the KMAC function on the input data.
 *
 * This function computes the KMAC on the `input_message` using the `key` and
 * returns a `tag` of `required_output_len`. The customization string is passed
 * through `customization_string` parameter. If no customization is desired it
 * can be be left empty (by settings its `data` to NULL and `length` to 0).
 *
 * The caller should set the `key_length` field of `key.config` to the number
 * of bytes in the key. Only the following key sizes (in bytes) are supported:
 * [16, 24, 32, 48, 64]. If any other size is given, the function will return
 * an error.
 *
 * The caller should allocate enough space in the `tag` buffer to hold
 * `required_output_len` bytes, rounded up to the nearest word, and then set
 * the `len` field of `tag` to the word length. If the word length is not long
 * enough to hold `required_output_len` bytes, then the function will return an
 * error.
 *
 * @param key Pointer to the blinded key struct with key shares.
 * @param input_message Input message to be hashed.
 * @param mac_mode Required KMAC mode.
 * @param customization_string Customization string.
 * @param required_output_len Required output length, in bytes.
 * @param[out] tag Output authentication tag.
 * @return The result of the KMAC operation.
 */
otcrypto_status_t otcrypto_kmac(const otcrypto_blinded_key_t *key,
                                otcrypto_const_byte_buf_t input_message,
                                otcrypto_kmac_mode_t kmac_mode,
                                otcrypto_const_byte_buf_t customization_string,
                                size_t required_output_len,
                                otcrypto_word32_buf_t tag);

