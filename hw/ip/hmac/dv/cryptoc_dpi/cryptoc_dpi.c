// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include <stdio.h>
#include <stdlib.h>

#include "hmac.h"
#include "hmac_wrap.h"
#include "sha.h"
#include "sha256.h"
#include "svdpi.h"

typedef unsigned long long ull_t;

extern void c_dpi_SHA_hash(const svOpenArrayHandle msg, ull_t len,
                           uint8_t hash[8]) {
  unsigned char *arr;
  unsigned int *arr_ptr;
  ull_t i;

  arr = (unsigned char *)malloc(len * sizeof(unsigned char));
  arr_ptr = (unsigned int *)svGetArrayPtr(msg);

  for (i = 0; i < len; i++) {
    arr[i] = arr_ptr[i];
  }

  // compute SHA hash
  SHA_hash(arr, len, hash);

  free(arr);
}

extern void c_dpi_SHA256_hash(const svOpenArrayHandle msg, ull_t len,
                              uint8_t hash[8]) {
  unsigned char *arr;
  unsigned int *arr_ptr;
  ull_t i;

  if (len > 0) {
    arr = (unsigned char *)malloc(len * sizeof(unsigned char));
    arr_ptr = (unsigned int *)svGetArrayPtr(msg);

    for (i = 0; i < len; i++) {
      arr[i] = arr_ptr[i];
    }

    // compute SHA256 hash
    SHA256_hash(arr, len, hash);

    free(arr);
  } else {
    // compute SHA256 hash when msg is empty
    SHA256_hash(NULL, len, hash);
  }
}

extern void c_dpi_HMAC_SHA(const svOpenArrayHandle key, ull_t key_len,
                           const svOpenArrayHandle msg, ull_t msg_len,
                           uint8_t hmac[8]) {
  unsigned char *msg_arr;
  unsigned int *msg_arr_ptr;
  unsigned char *key_arr;
  unsigned int *key_arr_ptr;
  ull_t i;

  msg_arr = (unsigned char *)malloc(msg_len * sizeof(unsigned char));
  msg_arr_ptr = (unsigned int *)svGetArrayPtr(msg);

  key_arr = (unsigned char *)malloc(key_len * sizeof(unsigned char));
  key_arr_ptr = (unsigned int *)svGetArrayPtr(key);

  for (i = 0; i < msg_len; i++) {
    msg_arr[i] = msg_arr_ptr[i];
  }

  for (i = 0; i < key_len; i++) {
    key_arr[i] = key_arr_ptr[i];
  }

  // compute SHA hash
  HMAC_SHA(key_arr, key_len, msg_arr, msg_len, hmac);

  free(msg_arr);
  free(key_arr);
}

extern void c_dpi_HMAC_SHA256(const svOpenArrayHandle key, ull_t key_len,
                              const svOpenArrayHandle msg, ull_t msg_len,
                              uint8_t hmac[8]) {
  unsigned char *msg_arr;
  unsigned int *msg_arr_ptr;
  unsigned char *key_arr;
  unsigned int *key_arr_ptr;
  ull_t i;

  if (msg_len > 0) {
    msg_arr = (unsigned char *)malloc(msg_len * sizeof(unsigned char));
    msg_arr_ptr = (unsigned int *)svGetArrayPtr(msg);

    for (i = 0; i < msg_len; i++) {
      msg_arr[i] = msg_arr_ptr[i];
    }
  }

  key_arr = (unsigned char *)malloc(key_len * sizeof(unsigned char));
  key_arr_ptr = (unsigned int *)svGetArrayPtr(key);

  for (i = 0; i < key_len; i++) {
    key_arr[i] = key_arr_ptr[i];
  }

  if (msg_len > 0) {
    // compute SHA256 hash
    HMAC_SHA256(key_arr, key_len, msg_arr, msg_len, hmac);

    free(msg_arr);
  } else {
    // compute SHA256 hash when msg is empty
    HMAC_SHA256(key_arr, key_len, NULL, msg_len, hmac);
  }

  free(key_arr);
}
