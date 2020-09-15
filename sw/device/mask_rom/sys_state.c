// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/mask_rom/sys_state.h"

#include <stddef.h>

#include "sw/device/lib/base/memory.h"

enum { kUninitBits = 0xaaaaaaaa };

// Open Q: I think we want this to *not* be static, so that tests can reach
// into this symbol and emulate glitching.
//
// For now, I'm giving it a trailing underscore and a "uniqueish" name, to match
// how we might write a private member of a class in C++, since that's kind of
// what this is.
static rom_ext_manifest_tag_t sys_state_rom_ext_desc_;
// Open Q: It feels like the easiest way to safely track is_initialized is to
// fill it with some weird bit pattern and zero it once it's been initialized.
// The "is initialized" state is then "is this in any value but the weird
// bit-pattern one"?
//
// That way, an attacker can easily glitch into the "is initialized" state, but
// that's fine, because that triggers a check against freshly-read data, and
// they shouldn't be able to mess with that.
static uint32_t sys_state_rom_ext_desc_is_init_ = kUninitBits;

sys_state_result_t sys_state_rom_ext_security_descriptor(
    const rom_ext_manifest_tag_t **ptr) {
  rom_ext_manifest_tag_t measure;
  // TODO: Fill `measure` with data.

  rom_ext_manifest_tag_t *storage = &sys_state_rom_ext_desc_;
  if (sys_state_rom_ext_desc_is_init_ == kUninitBits) {
    memcpy(storage, &measure, sizeof(measure));
    sys_state_rom_ext_desc_is_init_ = 0;
  } else if (memcmp(storage, &measure, sizeof(measure)) != 0) {
    return kSysStateCorrupt;
  }

  if (ptr != NULL) {
    *ptr = storage;
  }

  return kSysStateOk;
}

static sys_state_device_id_t sys_state_device_id_;
static uint32_t sys_state_device_id_is_init_ = kUninitBits;

sys_state_result_t sys_state_device_id(const sys_state_device_id_t **ptr) {
  sys_state_device_id_t measure;
  // TODO: Fill `measure` with data.

  sys_state_device_id_t *storage = &sys_state_device_id_;
  if (sys_state_device_id_is_init_ == kUninitBits) {
    memcpy(storage, &measure, sizeof(measure));
    sys_state_device_id_is_init_ = 0;
  } else if (memcmp(storage, &measure, sizeof(measure)) != 0) {
    return kSysStateCorrupt;
  }

  if (ptr != NULL) {
    *ptr = storage;
  }

  return kSysStateOk;
}

static dif_lifecycle_state_t sys_state_lc_state_;
static uint32_t sys_state_lc_state_is_init_ = kUninitBits;

sys_state_result_t sys_state_lifecycle_state(
    const dif_lifecycle_state_t **ptr) {
  dif_lifecycle_state_t measure;
  // TODO: Fill `measure` with data.

  dif_lifecycle_state_t *storage = &sys_state_lc_state_;
  if (sys_state_lc_state_is_init_ == kUninitBits) {
    memcpy(storage, &measure, sizeof(measure));
    sys_state_lc_state_is_init_ = 0;
  } else if (memcmp(storage, &measure, sizeof(measure)) != 0) {
    return kSysStateCorrupt;
  }

  if (ptr != NULL) {
    *ptr = storage;
  }

  return kSysStateOk;
}

static dif_lifecycle_debug_state_t sys_state_debug_state_;
static uint32_t sys_state_debug_state_is_init_ = kUninitBits;

sys_state_result_t sys_state_debug_state(
    const dif_lifecycle_debug_state_t **ptr) {
  dif_lifecycle_debug_state_t measure;
  // TODO: Fill `measure` with data.

  dif_lifecycle_debug_state_t *storage = &sys_state_debug_state_;
  if (sys_state_debug_state_is_init_ == kUninitBits) {
    memcpy(storage, &measure, sizeof(measure));
    sys_state_debug_state_is_init_ = 0;
  } else if (memcmp(storage, &measure, sizeof(measure)) != 0) {
    return kSysStateCorrupt;
  }

  if (ptr != NULL) {
    *ptr = storage;
  }

  return kSysStateOk;
}

// Open Q: How are we getting this value here? Should it be passed in as an
// argument? Should the module just create it? It's a bit problematic, since
// other modules might want to use HMAC, and having multiple handles lying
// around seems problematic.
extern dif_hmac_t hmac;

static sys_state_result_t write_to_hmac(const void *data, size_t len) {
  const char *data8 = (const char *)data;
  size_t data_left = len;
  while (data_left > 0) {
    size_t bytes_sent;
    switch (dif_hmac_fifo_push(&hmac, data8, data_left, &bytes_sent)) {
      case kDifHmacFifoOk:
        return kSysStateOk;
      case kDifHmacFifoFull:
        data8 += bytes_sent;
        data_left -= bytes_sent;
        continue;
      default:
        return kSysStateExternError;
    }
  }
  return kSysStateOk;
}

static dif_hmac_digest_t sys_state_health_state_;
static uint32_t sys_state_health_state_is_init_ = kUninitBits;

/**
 * Takes a measurement of the health state, by hashing the lc state and the
 * debug state together.
 */
static sys_state_result_t compute_health_state(dif_hmac_digest_t *measure) {
  sys_state_result_t err;

  const dif_lifecycle_state_t *lc;
  err = sys_state_lifecycle_state(&lc);
  if (err != kSysStateOk) {
    return err;
  }

  const dif_lifecycle_debug_state_t *debug;
  err = sys_state_debug_state(&debug);
  if (err != kSysStateOk) {
    return err;
  }

  if (dif_hmac_mode_sha256_start(&hmac) != kDifHmacOk) {
    return kSysStateExternError;
  }

  err = write_to_hmac(lc, sizeof(*lc));
  if (err != kSysStateOk) {
    return err;
  }
  err = write_to_hmac(debug, sizeof(*debug));
  if (err != kSysStateOk) {
    return err;
  }

  if (dif_hmac_process(&hmac) != kDifHmacOk) {
    return kSysStateExternError;
  }

  dif_hmac_digest_result_t digest_result = kDifHmacDigestProcessing;
  while (digest_result == kDifHmacDigestProcessing) {
    digest_result = dif_hmac_digest_read(&hmac, measure);
  }
  if (digest_result != kDifHmacDigestOk) {
    return kSysStateExternError;
  }

  return kSysStateOk;
}

sys_state_result_t sys_state_health_state(const dif_hmac_digest_t **ptr) {
  dif_hmac_digest_t measure;
  sys_state_result_t err = compute_health_state(&measure);
  if (err != kSysStateOk) {
    return err;
  }

  dif_hmac_digest_t *storage = &sys_state_health_state_;
  if (sys_state_health_state_is_init_ == kUninitBits) {
    memcpy(storage, &measure, sizeof(measure));
    sys_state_health_state_is_init_ = 0;
  } else if (memcmp(storage, &measure, sizeof(measure)) != 0) {
    return kSysStateCorrupt;
  }

  if (ptr != NULL) {
    *ptr = storage;
  }

  return kSysStateOk;
}
