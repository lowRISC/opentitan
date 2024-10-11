// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_CBOR_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_CBOR_H_

#include "include/dice/cbor_writer.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/silicon_creator/lib/error.h"

#define CBOR_CHECK_OVERFLOWED_AND_RETURN(p) \
  do {                                      \
    if (CborOutOverflowed(p)) {             \
      LOG_ERROR("CborOutOverflowed!!");     \
      return kErrorCertInvalidSize;         \
    }                                       \
    return kErrorOk;                        \
  } while (0)

// Wrappers for each CBOR type and CBOR handle initialization
static inline rom_error_t cbor_write_out_init(struct CborOut *p, void *buf,
                                              const size_t buf_size) {
  CborOutInit(buf, buf_size, p);
  CBOR_CHECK_OVERFLOWED_AND_RETURN(p);
}

static inline rom_error_t cbor_map_init(struct CborOut *p,
                                        const size_t num_pairs) {
  CborWriteMap(num_pairs, p);
  CBOR_CHECK_OVERFLOWED_AND_RETURN(p);
}

// Wrappers to encode a pair of data for cbor-map
static inline rom_error_t cbor_write_pair_uint_uint(struct CborOut *p,
                                                    uint64_t key,
                                                    uint64_t value) {
  CborWriteUint(key, p);
  CborWriteUint(value, p);
  CBOR_CHECK_OVERFLOWED_AND_RETURN(p);
}

static inline rom_error_t cbor_write_pair_int_uint(struct CborOut *p,
                                                   int64_t key,
                                                   uint64_t value) {
  CborWriteInt(key, p);
  CborWriteUint(value, p);
  CBOR_CHECK_OVERFLOWED_AND_RETURN(p);
}

static inline rom_error_t cbor_write_pair_uint_int(struct CborOut *p,
                                                   uint64_t key,
                                                   int64_t value) {
  CborWriteUint(key, p);
  CborWriteInt(value, p);
  CBOR_CHECK_OVERFLOWED_AND_RETURN(p);
}

static inline rom_error_t cbor_write_pair_int_bytes(struct CborOut *p,
                                                    int64_t key, uint8_t *value,
                                                    size_t value_size) {
  CborWriteInt(key, p);
  CborWriteBstr(value_size, value, p);
  CBOR_CHECK_OVERFLOWED_AND_RETURN(p);
}

#undef CBOR_CHECK_OVERFLOWED_AND_RETURN

#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_CERT_CBOR_H_
