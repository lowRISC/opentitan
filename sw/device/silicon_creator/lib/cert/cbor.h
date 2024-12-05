// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_CBOR_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_CBOR_H_

#include "include/dice/cbor_writer.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/silicon_creator/lib/error.h"

#define CBOR_RETURN_IF_OVERFLOWED(p)    \
  do {                                  \
    if (CborOutOverflowed(p)) {         \
      LOG_ERROR("CborOutOverflowed!!"); \
      return kErrorCertInvalidSize;     \
    }                                   \
  } while (0)

#define CBOR_CHECK_OVERFLOWED_AND_RETURN(p) \
  do {                                      \
    CBOR_RETURN_IF_OVERFLOWED(p);           \
    return kErrorOk;                        \
  } while (0)

/**
 * Initialize a CborOut structure.
 *
 * @param[in,out] p The pointer to a CborOut structure
 * @param buf The buffer that can be used for CBOR encoding
 * @param buf_size The buffer size
 * @return kErrorOk, or kErrorCertInvalidSize if the buf_size exceeds the
 *         buffer size that is recorded in p.
 */
OT_WARN_UNUSED_RESULT static inline rom_error_t cbor_write_out_init(
    struct CborOut *p, void *buf, const size_t buf_size) {
  CborOutInit(buf, buf_size, p);
  CBOR_CHECK_OVERFLOWED_AND_RETURN(p);
}
/**
 * Add a "map" header along with the elements count to a CborOut structure.
 *
 * @param[in,out] p The pointer to a CborOut structure
 * @param num_pairs The elements count in the map
 * @return kErrorOk, or kErrorCertInvalidSize if the updated CborOut is
 *         overflowed
 */
OT_WARN_UNUSED_RESULT static inline rom_error_t cbor_map_init(
    struct CborOut *p, const size_t num_pairs) {
  CborWriteMap(num_pairs, p);
  CBOR_CHECK_OVERFLOWED_AND_RETURN(p);
}
/**
 * Add a "array" header along with the elements count to a CborOut structure.
 *
 * @param[in,out] p The pointer to a CborOut structure
 * @param num_elements The elements count in the map
 * @return kErrorOk, or kErrorCertInvalidSize if the updated CborOut is
 *         overflowed
 */
OT_WARN_UNUSED_RESULT static inline rom_error_t cbor_array_init(
    struct CborOut *p, const size_t num_elements) {
  CborWriteArray(num_elements, p);
  CBOR_CHECK_OVERFLOWED_AND_RETURN(p);
}
/**
 * Add a "tstr" to a CborOut structure
 *
 * @param[in,out] p The pointer to a CborOut structure
 * @param str The string pointer
 * @return kErrorOk, or kErrorCertInvalidSize if the updated CborOut is
 *         overflowed
 */
OT_WARN_UNUSED_RESULT static inline rom_error_t cbor_write_string(
    struct CborOut *p, const char *str) {
  CborWriteTstr(str, p);
  CBOR_CHECK_OVERFLOWED_AND_RETURN(p);
}
/**
 * Add a "bstr" to a CborOut structure
 *
 * @param[in,out] p The pointer to a CborOut structure
 * @param data The pointer to the data that needs to be packed
 * @packed data_size Size of the data
 * @return kErrorOk, or kErrorCertInvalidSize if the updated CborOut is
 *         overflowed
 */
OT_WARN_UNUSED_RESULT static inline rom_error_t cbor_write_bytes(
    struct CborOut *p, const uint8_t *data, const size_t data_size) {
  CborWriteBstr(data_size, data, p);
  CBOR_CHECK_OVERFLOWED_AND_RETURN(p);
}

/***********************************************
 * Wrappers to encode a pair of data for cbor-map
 ***********************************************/
/**
 * Add 2 elements, "uint" and "uint", to a CborOut structure
 *
 * @param[in,out] p The pointer to a CborOut structure
 * @param key The first "uint" element
 * @param value The second "uint" element
 * @return kErrorOk, or kErrorCertInvalidSize if the updated CborOut is
 *         overflowed
 */
OT_WARN_UNUSED_RESULT static inline rom_error_t cbor_write_pair_uint_uint(
    struct CborOut *p, uint64_t key, uint64_t value) {
  CborWriteUint(key, p);
  CborWriteUint(value, p);
  CBOR_CHECK_OVERFLOWED_AND_RETURN(p);
}
/**
 * Add 2 elements, "int" and "uint", to a CborOut structure
 *
 * @param[in,out] p The pointer to a CborOut structure
 * @param key The first "int" element
 * @param value The second "uint" element
 * @return kErrorOk, or kErrorCertInvalidSize if the updated CborOut is
 *         overflowed
 */
OT_WARN_UNUSED_RESULT static inline rom_error_t cbor_write_pair_int_uint(
    struct CborOut *p, int64_t key, uint64_t value) {
  CborWriteInt(key, p);
  CborWriteUint(value, p);
  CBOR_CHECK_OVERFLOWED_AND_RETURN(p);
}
/**
 * Add 2 elements, "uint" and "int", to a CborOut structure
 *
 * @param[in,out] p The pointer to a CborOut structure
 * @param key The first "uint" element
 * @param value The second "int" element
 * @return kErrorOk, or kErrorCertInvalidSize if the updated CborOut is
 *         overflowed
 */
OT_WARN_UNUSED_RESULT static inline rom_error_t cbor_write_pair_uint_int(
    struct CborOut *p, uint64_t key, int64_t value) {
  CborWriteUint(key, p);
  CborWriteInt(value, p);
  CBOR_CHECK_OVERFLOWED_AND_RETURN(p);
}
/**
 * Add 2 elements, "int" and "bstr", to a CborOut structure
 *
 * @param[in,out] p The pointer to a CborOut structure
 * @param key The first "int" element
 * @param value The pointer of the second "bstr" element
 * @param value_size Size of the value
 * @return kErrorOk, or kErrorCertInvalidSize if the updated CborOut is
 *         overflowed
 */
OT_WARN_UNUSED_RESULT static inline rom_error_t cbor_write_pair_int_bytes(
    struct CborOut *p, int64_t key, const uint8_t *value,
    const size_t value_size) {
  CborWriteInt(key, p);
  CborWriteBstr(value_size, value, p);
  CBOR_CHECK_OVERFLOWED_AND_RETURN(p);
}
/**
 * Add 2 elements, "uint" and "tstr", to a CborOut structure
 *
 * @param[in,out] p The pointer to a CborOut structure
 * @param key The first "uint" element
 * @param value The pointer of the second "tstr" element
 * @return kErrorOk, or kErrorCertInvalidSize if the updated CborOut is
 *         overflowed
 */
OT_WARN_UNUSED_RESULT static inline rom_error_t cbor_write_pair_uint_tstr(
    struct CborOut *p, uint64_t key, const char *value) {
  CborWriteUint(key, p);
  CborWriteTstr(value, p);
  CBOR_CHECK_OVERFLOWED_AND_RETURN(p);
}
/**
 * Add 2 elements, "int" and "tstr", to a CborOut structure
 *
 * @param[in,out] p The pointer to a CborOut structure
 * @param key The first "int" element
 * @param value The pointer of the second "tstr" element
 * @return kErrorOk, or kErrorCertInvalidSize if the updated CborOut is
 *         overflowed
 */
OT_WARN_UNUSED_RESULT static inline rom_error_t cbor_write_pair_int_tstr(
    struct CborOut *p, int64_t key, const char *value) {
  CborWriteInt(key, p);
  CborWriteTstr(value, p);
  CBOR_CHECK_OVERFLOWED_AND_RETURN(p);
}

/***********************************************
 * Helpers for the auto-gen template
 ***********************************************/
/**
 * Calculate how much space is needed in the header for an "unsigned interger"
 * type of CBOR argument.
 *
 * @param value An unsigned integer argument.
 * @return Size required in the header
 */
static inline size_t cbor_calc_arg_size(uint64_t value) {
  if (value <= 23) {
    return 0;
  } else if (value <= 0xff) {
    return 1;
  } else if (value <= 0xffff) {
    return 2;
  } else if (value <= 0xffffffff) {
    return 4;
  } else {
    return 8;
  };
}
/**
 * Calculate how much space is needed in the header for a "signed interger" type
 * of CBOR argument.
 *
 * @param value An signed integer argument.
 * @return Size required in the header
 */
static inline size_t cbor_calc_int_size(int64_t value) {
  if (value < 0)
    return cbor_calc_arg_size((uint64_t)(-(value + 1)));

  return cbor_calc_arg_size((uint64_t)value);
}

// Add a bstr/tstr header with size, and rewind the cursor
/**
 * Add a "bstr" header along with the payload size, and rewind the cursor of
 * CborOut structure.
 *
 * @param[in,out] p The pointer to a CborOut structure
 * @param bstr_size The size of the payload
 * @return kErrorOk, or kErrorCertInvalidSize if the bstr_size exceeds the
 *         buffer size that is recorded in p.
 */
OT_WARN_UNUSED_RESULT static inline rom_error_t cbor_write_bstr_header(
    struct CborOut *p, const size_t bstr_size) {
  if (NULL == CborAllocBstr(bstr_size, p))
    return kErrorCertInvalidSize;
  p->cursor -= bstr_size;
  CBOR_CHECK_OVERFLOWED_AND_RETURN(p);
}
/**
 * Add a "tstr" header along with the payload size, and rewind the cursor of
 * CborOut structure.
 *
 * @param[in,out] p The pointer to a CborOut structure
 * @param tstr_size The size of the payload
 * @return kErrorOk, or kErrorCertInvalidSize if the tstr_size exceeds the
 *         buffer size that is recorded in p.
 */
OT_WARN_UNUSED_RESULT static inline rom_error_t cbor_write_tstr_header(
    struct CborOut *p, const size_t tstr_size) {
  if (NULL == CborAllocTstr(tstr_size, p))
    return kErrorCertInvalidSize;
  p->cursor -= tstr_size;
  CBOR_CHECK_OVERFLOWED_AND_RETURN(p);
}

/**
 * Fill in raw data to a given CborOut structure.
 *
 * @param[in,out] p The pointer to a CborOut structure
 * @param raw The pointer to the raw bytes
 * @param raw_size The size of the raw byptes
 * @return kErrorOk, or kErrorCertInvalidSize if the raw_size exceeds the
 *         buffer size that is recorded in p.
 */
OT_WARN_UNUSED_RESULT static inline rom_error_t cbor_write_raw_bytes(
    struct CborOut *p, const uint8_t *raw, const size_t raw_size) {
  if (p->cursor + raw_size > p->buffer_size)
    return kErrorCertInvalidSize;
  memcpy(&p->buffer[p->cursor], raw, raw_size);
  p->cursor += raw_size;
  CBOR_CHECK_OVERFLOWED_AND_RETURN(p);
}
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_CBOR_H_
