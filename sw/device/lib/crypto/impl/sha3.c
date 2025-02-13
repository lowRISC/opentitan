otcrypto_status_t otcrypto_xof_shake(otcrypto_const_byte_buf_t input_message,
                                     otcrypto_hash_digest_t digest) {
  switch (digest.mode) {
    case kOtcryptoHashXofModeShake128:
      return kmac_shake_128(input_message.data, input_message.len, digest.data,
                            digest.len);
    case kOtcryptoHashXofModeShake256:
      return kmac_shake_256(input_message.data, input_message.len, digest.data,
                            digest.len);
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}

otcrypto_status_t otcrypto_xof_cshake(
    otcrypto_const_byte_buf_t input_message,
    otcrypto_const_byte_buf_t function_name_string,
    otcrypto_const_byte_buf_t customization_string,
    otcrypto_hash_digest_t digest) {
  // According to NIST SP 800-185 Section 3.2, cSHAKE call should use SHAKE, if
  // both `customization_string` and `function_name_string` are empty string
  if (customization_string.len == 0 && function_name_string.len == 0) {
    switch (digest.mode) {
      case kOtcryptoHashXofModeCshake128:
        return kmac_shake_128(input_message.data, input_message.len,
                              digest.data, digest.len);
      case kOtcryptoHashXofModeCshake256:
        return kmac_shake_256(input_message.data, input_message.len,
                              digest.data, digest.len);
      default:
        return OTCRYPTO_BAD_ARGS;
    }
  }

  switch (digest.mode) {
    case kOtcryptoHashXofModeCshake128:
      return kmac_cshake_128(
          input_message.data, input_message.len, function_name_string.data,
          function_name_string.len, customization_string.data,
          customization_string.len, digest.data, digest.len);
      break;
    case kOtcryptoHashXofModeCshake256:
      return kmac_cshake_256(
          input_message.data, input_message.len, function_name_string.data,
          function_name_string.len, customization_string.data,
          customization_string.len, digest.data, digest.len);
    default:
      return OTCRYPTO_BAD_ARGS;
  }

  // Should be unreachable.
  HARDENED_TRAP();
  return OTCRYPTO_FATAL_ERR;
}
