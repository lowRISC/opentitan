// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

#include "hmac.h"
#include "hmac_wrap.h"
#include "sha.h"
#include "sha256.h"
#include "sha384.h"
#include "sha512.h"

// SystemVerilog DPI definitions
#include "svdpi.h"

// Gather the elements of the open array to form a C-style array of contiguous
// bytes
static uint8_t *collect_bytes(const svOpenArrayHandle arg, uint64_t len) {
  // Note: alas when passed an open array that is empty we are unable even to
  //       query svSize() of the single dimension without inducing a E,MEMALC
  //       error from xcelium, so we must pass supplied with the length.
  assert(len > 0u);

  assert(1 == svDimensions(arg));
  assert(len <= svSize(arg, 1));

  uint8_t *arr = (uint8_t *)malloc(len);
  if (arr) {
    const svBitVecVal *ptr = (svBitVecVal *)svGetArrayPtr(arg);
    if (ptr) {
      // C-style layout
      for (uint64_t idx = 0u; idx < len; ++idx) {
        arr[idx] = (uint8_t)ptr[idx];
      }
    } else {
      // The implementation-independent way to access open arrays is to use the
      // SystemVerilog array bounds/indexes.
      const int high = svHigh(arg, 1);
      const int low = svLow(arg, 1);

      printf("bounds [%d:%d]\n", high, low);

      for (int idx = low; idx <= high; ++idx) {
        uint8_t *ptr = (uint8_t *)svGetArrElemPtr1(arg, idx);
        assert(ptr);
        arr[idx] = (uint8_t)*ptr;
      }
    }
  }

  return arr;
}

extern void c_dpi_SHA_hash(const svOpenArrayHandle msg, uint64_t len,
                           uint32_t hash[8]) {
  if (len > 0u) {
    uint8_t *arr = collect_bytes(msg, len);
    assert(arr);

    // compute SHA hash
    SHA_hash(arr, len, (uint8_t *)hash);

    free(arr);
  }
}

extern void c_dpi_SHA256_hash(const svOpenArrayHandle msg, uint64_t len,
                              uint32_t hash[8]) {
  if (len > 0u) {
    uint8_t *arr = collect_bytes(msg, len);
    assert(arr);

    // compute SHA256 hash
    SHA256_hash(arr, len, (uint8_t *)hash);

    free(arr);
  } else {
    // compute SHA256 hash when msg is empty
    SHA256_hash(NULL, 0u, (uint8_t *)hash);
  }
}

extern void c_dpi_SHA384_hash(const svOpenArrayHandle msg, uint64_t len,
                              uint32_t hash[12]) {
  if (len > 0u) {
    uint8_t *arr = collect_bytes(msg, len);
    assert(arr);

    // compute SHA384 hash
    SHA384_hash(arr, len, (uint8_t *)hash);

    free(arr);
  } else {
    // compute SHA384 hash when msg is empty
    SHA384_hash(NULL, 0u, (uint8_t *)hash);
  }
}

extern void c_dpi_SHA512_hash(const svOpenArrayHandle msg, uint64_t len,
                              uint32_t hash[16]) {
  if (len > 0u) {
    uint8_t *arr = collect_bytes(msg, len);
    assert(arr);

    // compute SHA512 hash
    SHA512_hash(arr, len, (uint8_t *)hash);

    free(arr);
  } else {
    // compute SHA512 hash when msg is empty
    SHA512_hash(NULL, 0u, (uint8_t *)hash);
  }
}

extern void c_dpi_HMAC_SHA(const svOpenArrayHandle key, uint64_t key_len,
                           const svOpenArrayHandle msg, uint64_t msg_len,
                           uint32_t hmac[8]) {
  if (msg_len > 0u) {
    uint8_t *msg_arr = collect_bytes(msg, msg_len);
    assert(msg_arr);

    uint8_t *key_arr = collect_bytes(key, key_len);
    assert(key_arr);

    // compute SHA hash
    HMAC_SHA(key_arr, key_len, msg_arr, msg_len, (uint8_t *)hmac);

    free(msg_arr);
    free(key_arr);
  }
}

extern void c_dpi_HMAC_SHA256(const svOpenArrayHandle key, uint64_t key_len,
                              const svOpenArrayHandle msg, uint64_t msg_len,
                              uint32_t hmac[8]) {
  uint8_t *key_arr = collect_bytes(key, key_len);
  assert(key_arr);

  if (msg_len > 0u) {
    uint8_t *msg_arr = collect_bytes(msg, msg_len);
    assert(msg_arr);

    // compute SHA256 hash
    HMAC_SHA256(key_arr, key_len, msg_arr, msg_len, (uint8_t *)hmac);

    free(msg_arr);
  } else {
    // compute SHA256 hash when msg is empty
    HMAC_SHA256(key_arr, key_len, NULL, 0u, (uint8_t *)hmac);
  }

  free(key_arr);
}
extern void c_dpi_HMAC_SHA384(const svOpenArrayHandle key, uint64_t key_len,
                              const svOpenArrayHandle msg, uint64_t msg_len,
                              uint32_t hmac[12]) {
  uint8_t *key_arr = collect_bytes(key, key_len);
  assert(key_arr);

  if (msg_len > 0u) {
    uint8_t *msg_arr = collect_bytes(msg, msg_len);
    assert(msg_arr);

    // compute SHA384 hash
    HMAC_SHA384(key_arr, key_len, msg_arr, msg_len, (uint8_t *)hmac);

    free(msg_arr);
  } else {
    // compute SHA384 hash when msg is empty
    HMAC_SHA384(key_arr, key_len, NULL, 0u, (uint8_t *)hmac);
  }

  free(key_arr);
}

extern void c_dpi_HMAC_SHA512(const svOpenArrayHandle key, uint64_t key_len,
                              const svOpenArrayHandle msg, uint64_t msg_len,
                              uint32_t hmac[16]) {
  uint8_t *key_arr = collect_bytes(key, key_len);
  assert(key_arr);

  if (msg_len > 0u) {
    uint8_t *msg_arr = collect_bytes(msg, msg_len);
    assert(msg_arr);

    // compute SHA512 hash
    HMAC_SHA512(key_arr, key_len, msg_arr, msg_len, (uint8_t *)hmac);

    free(msg_arr);
  } else {
    // compute SHA512 hash when msg is empty
    HMAC_SHA512(key_arr, key_len, NULL, 0u, (uint8_t *)hmac);
  }

  free(key_arr);
}
