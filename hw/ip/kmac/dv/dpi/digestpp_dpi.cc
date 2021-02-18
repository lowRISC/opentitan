// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <list>

#include "svdpi.h"
#include "vendor/kerukuro_digestpp/algorithm/kmac.hpp"
#include "vendor/kerukuro_digestpp/algorithm/sha3.hpp"
#include "vendor/kerukuro_digestpp/algorithm/shake.hpp"

extern "C" {

// TODO(udi) might need to implement endian conversion

//////////////////////
// HELPER FUNCTIONS //
//////////////////////

/**
 * Generic function to load an unsized array from SV memory into C memory.
 */
static void load_arr_from_simulator(const svOpenArrayHandle arr,
                                    uint8_t *array_out, uint64_t array_len) {
  svBitVecVal val;

  if (array_len == 0) {
    return;
  }

  uint8_t *arr_ptr = (uint8_t *)svGetArrayPtr(arr);
  for (int i = 0; i < array_len; i++) {
    svGetBitArrElem1VecVal(&val, arr, i);
    array_out[i] = (uint8_t)val;
  }
}

/**
 * Generic function to write an unsized array from C memory into SV memory.
 */
static void write_array_to_simulator(const svOpenArrayHandle arr,
                                     uint8_t *data) {
  uint64_t arr_len = svSize(arr, 1);

  for (uint64_t i = 0; i < arr_len; ++i) {
    svBitVecVal data_val = (svBitVecVal)data[i];
    svPutBitArrElem1VecVal(arr, &data_val, i);
  }
}

/**
 * Helper function to calculate generic length SHA3 algorithm.
 *
 * Note that `sha_len` can only be in {224, 256, 384, 512} for KMAC HWIP, these
 * lengths are explicitly passsed in from SV code, so no need to use an
 * assertion here.
 */
static void get_sha3_digest(uint64_t sha_len, const svOpenArrayHandle msg,
                            uint64_t msg_len, svOpenArrayHandle digest) {
  // Number of bytes in result digest
  uint64_t digest_len = sha_len / 8;

  uint8_t digest_arr[digest_len];

  // Load message from SV memory
  uint8_t *msg_arr = (uint8_t *)malloc(msg_len * sizeof(uint8_t));
  load_arr_from_simulator(msg, msg_arr, msg_len);

  // Compute the digest
  digestpp::sha3 sha3(sha_len);
  sha3.absorb(msg_arr, msg_len);
  sha3.digest(digest_arr, sizeof(digest_arr));

  if (msg_arr != nullptr) {
    free(msg_arr);
  }

  // Return the digest array so that SV can access it
  write_array_to_simulator(digest, digest_arr);
}

//////////////
// SHA3-224 //
//////////////
extern void c_dpi_sha3_224(const svOpenArrayHandle msg, uint64_t msg_len,
                           svOpenArrayHandle digest) {
  get_sha3_digest(224, msg, msg_len, digest);
}

//////////////
// SHA3-256 //
//////////////
extern void c_dpi_sha3_256(const svOpenArrayHandle msg, uint64_t msg_len,
                           svOpenArrayHandle digest) {
  get_sha3_digest(256, msg, msg_len, digest);
}

//////////////
// SHA3-384 //
//////////////
extern void c_dpi_sha3_384(const svOpenArrayHandle msg, uint64_t msg_len,
                           svOpenArrayHandle digest) {
  get_sha3_digest(384, msg, msg_len, digest);
}

//////////////
// SHA3-512 //
//////////////
extern void c_dpi_sha3_512(const svOpenArrayHandle msg, uint64_t msg_len,
                           svOpenArrayHandle digest) {
  get_sha3_digest(512, msg, msg_len, digest);
}

//////////////
// SHAKE128 //
//////////////
extern void c_dpi_shake128(const svOpenArrayHandle msg, uint64_t msg_len,
                           uint64_t output_len, svOpenArrayHandle digest) {
  // Load message from SV memory
  uint8_t *msg_arr = (uint8_t *)malloc(msg_len * sizeof(uint8_t));
  load_arr_from_simulator(msg, msg_arr, msg_len);

  uint8_t digest_arr[output_len];

  // Compute the digest
  digestpp::shake128 shake;
  shake.absorb(msg_arr, msg_len);
  shake.squeeze(digest_arr, output_len);

  if (msg_arr != nullptr) {
    free(msg_arr);
  }

  // Return the digest array to SV code
  write_array_to_simulator(digest, digest_arr);
}

//////////////
// SHAKE256 //
//////////////
extern void c_dpi_shake256(const svOpenArrayHandle msg, uint64_t msg_len,
                           uint64_t output_len, svOpenArrayHandle digest) {
  // Load message from SV memory
  uint8_t *msg_arr = (uint8_t *)malloc(msg_len * sizeof(uint8_t));
  load_arr_from_simulator(msg, msg_arr, msg_len);

  uint8_t digest_arr[output_len];

  // Compute the digest
  digestpp::shake256 shake;
  shake.absorb(msg_arr, msg_len);
  shake.squeeze(digest_arr, output_len);

  if (msg_arr != nullptr) {
    free(msg_arr);
  }

  // Return the digest array to SV code
  write_array_to_simulator(digest, digest_arr);
}

///////////////
// CSHAKE128 //
///////////////
extern void c_dpi_cshake128(const svOpenArrayHandle msg,
                            const char *function_name,
                            const char *customization_str, uint64_t msg_len,
                            uint64_t output_len, svOpenArrayHandle digest) {
  // Load message from SV memory
  uint8_t *msg_arr = (uint8_t *)malloc(msg_len * sizeof(uint8_t));
  load_arr_from_simulator(msg, msg_arr, msg_len);

  uint8_t digest_arr[output_len];

  // Compute the digest
  digestpp::cshake128 shake;
  shake.set_function_name(function_name, strlen(function_name));
  shake.set_customization(customization_str, strlen(customization_str));
  shake.absorb(msg_arr, msg_len);
  shake.squeeze(digest_arr, output_len);

  if (msg_arr != nullptr) {
    free(msg_arr);
  }

  // Return the digest array to SV code
  write_array_to_simulator(digest, digest_arr);
}

///////////////
// CSHAKE256 //
///////////////
extern void c_dpi_cshake256(const svOpenArrayHandle msg,
                            const char *function_name,
                            const char *customization_str, uint64_t msg_len,
                            uint64_t output_len, svOpenArrayHandle digest) {
  // Load message from SV memory
  uint8_t *msg_arr = (uint8_t *)malloc(msg_len * sizeof(uint8_t));
  load_arr_from_simulator(msg, msg_arr, msg_len);

  uint8_t digest_arr[output_len];

  // Compute the digest
  digestpp::cshake256 shake;
  shake.set_function_name(function_name, strlen(function_name));
  shake.set_customization(customization_str, strlen(customization_str));
  shake.absorb(msg_arr, msg_len);
  shake.squeeze(digest_arr, output_len);

  if (msg_arr != nullptr) {
    free(msg_arr);
  }

  // Return the digest array to SV code
  write_array_to_simulator(digest, digest_arr);
}

/////////////
// KMAC128 //
/////////////
extern void c_dpi_kmac128(const svOpenArrayHandle msg, uint64_t msg_len,
                          const svOpenArrayHandle key, uint64_t key_len,
                          const char *customization_str, uint64_t output_len,
                          svBitVecVal *digest) {
  uint64_t output_len_bits = output_len * 8;

  // Load message from SV memory
  uint8_t *msg_arr = (uint8_t *)malloc(msg_len * sizeof(uint8_t));
  load_arr_from_simulator(msg, msg_arr, msg_len);

  // Load key from SV memory
  uint8_t *key_arr = (uint8_t *)malloc(key_len * sizeof(uint8_t));
  load_arr_from_simulator(key, key_arr, key_len);

  uint8_t digest_arr[output_len];

  // Compute the digest
  digestpp::kmac128 kmac(output_len_bits);
  kmac.set_customization(customization_str, strlen(customization_str));
  kmac.set_key(key_arr, key_len);
  kmac.absorb(msg_arr, msg_len);
  kmac.digest(digest_arr, sizeof(digest_arr));

  if (msg_arr != nullptr) {
    free(msg_arr);
  }

  if (key_arr != nullptr) {
    free(key_arr);
  }

  // Return the digest array to SV code
  write_array_to_simulator(digest, digest_arr);
}

/////////////////
// KMAC128-XOF //
/////////////////
extern void c_dpi_kmac128_xof(const svOpenArrayHandle msg, uint64_t msg_len,
                              const svOpenArrayHandle key, uint64_t key_len,
                              const char *customization_str,
                              uint64_t output_len, svBitVecVal *digest) {
  // Load message from SV memory
  uint8_t *msg_arr = (uint8_t *)malloc(msg_len * sizeof(uint8_t));
  load_arr_from_simulator(msg, msg_arr, msg_len);

  // Load key from SV memory
  uint8_t *key_arr = (uint8_t *)malloc(key_len * sizeof(uint8_t));
  load_arr_from_simulator(key, key_arr, key_len);

  uint8_t digest_arr[output_len];

  // Compute the digest
  digestpp::kmac128_xof kmac;
  kmac.set_customization(customization_str, strlen(customization_str));
  kmac.set_key(key_arr, key_len);
  kmac.absorb(msg_arr, msg_len);
  kmac.squeeze(digest_arr, sizeof(digest_arr));

  if (msg_arr != nullptr) {
    free(msg_arr);
  }

  if (key_arr != nullptr) {
    free(key_arr);
  }

  // Return the digest array to SV code
  write_array_to_simulator(digest, digest_arr);
}

/////////////
// KMAC256 //
/////////////
extern void c_dpi_kmac256(const svOpenArrayHandle msg, uint64_t msg_len,
                          const svOpenArrayHandle key, uint64_t key_len,
                          const char *customization_str, uint64_t output_len,
                          svBitVecVal *digest) {
  uint64_t output_len_bits = output_len * 8;

  // Load message from SV memory
  uint8_t *msg_arr = (uint8_t *)malloc(msg_len * sizeof(uint8_t));
  load_arr_from_simulator(msg, msg_arr, msg_len);

  // Load key from SV memory
  uint8_t *key_arr = (uint8_t *)malloc(key_len * sizeof(uint8_t));
  load_arr_from_simulator(key, key_arr, key_len);

  uint8_t digest_arr[output_len];

  // Compute the digest
  digestpp::kmac256 kmac(output_len_bits);
  kmac.set_customization(customization_str, strlen(customization_str));
  kmac.set_key(key_arr, key_len);
  kmac.absorb(msg_arr, msg_len);
  kmac.digest(digest_arr, sizeof(digest_arr));

  if (msg_arr != nullptr) {
    free(msg_arr);
  }

  if (key_arr != nullptr) {
    free(key_arr);
  }

  // Return the digest array to SV code
  write_array_to_simulator(digest, digest_arr);
}

/////////////////
// KMAC256-XOF //
/////////////////
extern void c_dpi_kmac256_xof(const svOpenArrayHandle msg, uint64_t msg_len,
                              const svOpenArrayHandle key, uint64_t key_len,
                              const char *customization_str,
                              uint64_t output_len, svBitVecVal *digest) {
  // Load message from SV memory
  uint8_t *msg_arr = (uint8_t *)malloc(msg_len * sizeof(uint8_t));
  load_arr_from_simulator(msg, msg_arr, msg_len);

  // Load key from SV memory
  uint8_t *key_arr = (uint8_t *)malloc(key_len * sizeof(uint8_t));
  load_arr_from_simulator(key, key_arr, key_len);

  uint8_t digest_arr[output_len];

  // Compute the digest
  digestpp::kmac256_xof kmac;
  kmac.set_customization(customization_str, strlen(customization_str));
  kmac.set_key(key_arr, key_len);
  kmac.absorb(msg_arr, msg_len);
  kmac.squeeze(digest_arr, sizeof(digest_arr));

  if (msg_arr != nullptr) {
    free(msg_arr);
  }

  if (key_arr != nullptr) {
    free(key_arr);
  }

  // Return the digest array to SV code
  write_array_to_simulator(digest, digest_arr);
}
}
