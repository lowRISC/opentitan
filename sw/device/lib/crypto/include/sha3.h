/**
 * Performs the SHAKE extendable output function (XOF) on input data.
 *
 * The caller should allocate space for the `digest` buffer and set the `mode`
 * and `len` fields.  The `mode` parameter must be
 * `kOtcryptoHashXofModeShake128` or `kOtcryptoHashXofModeShake256`; other
 * values will result in errors.
 *
 * @param input_message Input message for extendable output function.
 * @param[out] digest Output from the extendable output function.
 * @return Result of the xof operation.
 */
otcrypto_status_t otcrypto_xof_shake(otcrypto_const_byte_buf_t input_message,
                                     otcrypto_hash_digest_t digest);

/**
 * Performs the CSHAKE extendable output function (XOF) on input data.
 *
 * The `function_name_string` is used by NIST to define functions based on
 * cSHAKE. When no function other than cSHAKE is desired; it can be empty. The
 * `customization_string` is used to define a variant of the cSHAKE function.
 * If no customization is desired it can be empty.
 *
 * The caller should allocate space for the `digest` buffer and set the `mode`
 * and `len` fields. The `mode` parameter must be
 * `kOtcryptoHashXofModeCshake128` or `kOtcryptoHashXofModeCshake256`; other
 * values will result in errors.
 *
 * @param input_message Input message for extendable output function.
 * @param function_name_string NIST Function name string.
 * @param customization_string Customization string for cSHAKE.
 * @param[out] digest Output from the extendable output function.
 * @return Result of the xof operation.
 */
otcrypto_status_t otcrypto_xof_cshake(
    otcrypto_const_byte_buf_t input_message,
    otcrypto_const_byte_buf_t function_name_string,
    otcrypto_const_byte_buf_t customization_string,
    otcrypto_hash_digest_t digest);
