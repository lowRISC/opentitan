// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_CBOR_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_CBOR_H_

#include "sw/device/silicon_creator/lib/error.h"

struct cbor_out {
  uint8_t *start;
  size_t offset;
};

typedef struct cbor_out cbor_out_t;

/**
 * Initialize the cbor_out_t.
 *
 * @param[in,out] p cbor_out structure
 * @param buf buffer to be written
 */
static inline void cbor_out_init(cbor_out_t *p, void *buf) {
  p->start = buf;
  p->offset = 0;
}

/**
 * Return the current written size in the cbor_out_t.
 *
 * @param[in] p cbor_out structure
 * @return current written size
 */
static inline size_t cbor_out_size(cbor_out_t *p) { return p->offset; }

/**
 * Calculate the required size of "CBOR argument".
 *
 * @param value unsigned argument
 * @return required size
 */
size_t cbor_calc_arg_size(uint64_t value);

/**
 * Calculate the required size to encode the signed integer as "CBOR argument".
 *
 * @param value signed integer
 * @return required size
 */
size_t cbor_calc_int_size(int64_t value);

/**
 * Write the raw bytes if cbor_out is not NULL.
 *
 * @param[in,out] p cbor_out structure
 * @param raw pointer to raw bytes
 * @param raw_size the size of raw bytes
 * @return size to be written
 */
size_t cbor_write_raw_bytes(cbor_out_t *p, const uint8_t *raw, size_t raw_size);

/**
 * Write the integer if cbor_out is not NULL.
 *
 * @param[in,out] p cbor_out structure
 * @param value signed integer
 * @return size to be written
 */
size_t cbor_write_int(cbor_out_t *p, int64_t value);

/**
 * Write the byte string header if cbor_out is not NULL.
 *
 * @param[in,out] p cbor_out structure
 * @param bstr_size size of the bstr
 * @return size to be written
 */
size_t cbor_write_bstr_header(cbor_out_t *p, size_t bstr_size);

/**
 * A helper function to write the byte string if cbor_out is not NULL.
 *
 * @param[in,out] p cbor_out structure
 * @param bstr pointer to the bstr
 * @param bstr_size size of the bstr
 * @return size to be written
 */
static inline size_t cbor_write_bstr(cbor_out_t *p, const uint8_t *bstr,
                                     size_t bstr_size) {
  size_t sz = 0;
  sz += cbor_write_bstr_header(p, bstr_size);
  sz += cbor_write_raw_bytes(p, bstr, bstr_size);
  return sz;
}

/**
 * Write the text string header if cbor_out is not NULL.
 *
 * @param[in,out] p cbor_out structure
 * @param bstr_size size of the tstr
 * @return size to be written
 */
size_t cbor_write_tstr_header(cbor_out_t *p, size_t tstr_size);

/**
 * A helper function to write the text string if cbor_out is not NULL.
 *
 * @param[in,out] p cbor_out structure
 * @param tstr pointer to the tstr
 * @param bstr_size size of the tstr
 * @return size to be written
 */
static inline size_t cbor_write_tstr(cbor_out_t *p, const uint8_t *tstr,
                                     size_t tstr_size) {
  size_t sz = 0;
  sz += cbor_write_tstr_header(p, tstr_size);
  sz += cbor_write_raw_bytes(p, tstr, tstr_size);
  return sz;
}

/**
 * Write the array header if cbor_out is not NULL.
 *
 * @param[in,out] p cbor_out structure
 * @param num_elements the number of elements in the array
 * @return size to be written
 */
size_t cbor_write_array_header(cbor_out_t *p, size_t num_elements);

/**
 * Write the map header if cbor_out is not NULL.
 *
 * @param[in,out] p cbor_out structure
 * @param num_pairs the number of pairs in the map
 * @return size to be written
 */
size_t cbor_write_map_header(cbor_out_t *p, size_t num_pairs);

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_CBOR_H_
