// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/include/cryptolib_build_info.h"

#include "hw/top/dt/rom_ctrl.h"
#include "sw/device/lib/base/abs_mmio.h"
#include "sw/device/lib/base/hardened.h"
#include "sw/device/lib/base/macros.h"
#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/crypto/drivers/cryptolib_build_info.h"
#include "sw/device/lib/crypto/impl/status.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"

#include "hw/top/rom_ctrl_regs.h"  // Generated.

// Module ID for status codes.
#define MODULE_ID MAKE_MODULE_ID('c', 'b', 'i')

static const dt_rom_ctrl_t kRomCtrlDt = kDtRomCtrlFirst;

static inline uint32_t rom_ctrl_base(void) {
  return dt_rom_ctrl_primary_reg_block(kRomCtrlDt);
}

// Module name of the cryptolib.
static const char kCryptoLibModuleName[] = "otcrypto_earlgrey_cryptolib";
static_assert(
    sizeof(kCryptoLibModuleName) - 1 == kOtcryptoModuleNameBytes,
    "kCryptoLibModuleName length must match kOtcryptoModuleNameBytes");

otcrypto_status_t otcrypto_module_name(otcrypto_byte_buf_t *name) {
#ifndef OTCRYPTO_DISABLE_NULL_CHECKS
  if (name == NULL || name->data == NULL) {
    return OTCRYPTO_BAD_ARGS;
  }
#endif
  if (launder32(name->len) != kOtcryptoModuleNameBytes) {
    return OTCRYPTO_BAD_ARGS;
  }

  if (launder32(OTCRYPTO_CHECK_BUF(name)) != kHardenedBoolTrue) {
    return OTCRYPTO_FATAL_ERR;
  }

  memcpy(name->data, kCryptoLibModuleName, kOtcryptoModuleNameBytes);

  return LAUNDERED_OTCRYPTO_OK;
}

otcrypto_status_t otcrypto_build_info(uint32_t *version, bool *released,
                                      uint32_t *build_hash_low,
                                      uint32_t *build_hash_high) {
  *version = kCryptoLibBuildInfo.version;
  *released = kCryptoLibBuildInfo.released;
  *build_hash_low = kCryptoLibBuildInfo.scm_revision.scm_revision_low;
  *build_hash_high = kCryptoLibBuildInfo.scm_revision.scm_revision_high;

  return LAUNDERED_OTCRYPTO_OK;
}

otcrypto_lib_version_t otcrypto_lib_version(void) {
  return (otcrypto_lib_version_t)kCryptoLibVersion;
}

void otcrypto_version_decode(uint32_t version, uint32_t *major, uint32_t *minor,
                             uint32_t *patch) {
  // Uses modular multiplicative inverse mod 2^32 for decoding
  uint32_t decoded = version * 0x332ce355u;
  *major = (decoded >> 24) & 0xff;
  *minor = (decoded >> 16) & 0xff;
  *patch = (decoded >> 8) & 0xff;
}

otcrypto_status_t otcrypto_rom_version(uint32_t *rom_version) {
  *rom_version =
      abs_mmio_read32(rom_ctrl_base() + ROM_CTRL_EXP_DIGEST_1_REG_OFFSET);

  return LAUNDERED_OTCRYPTO_OK;
}
