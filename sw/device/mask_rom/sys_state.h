// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_MASK_ROM_SYS_STATE_H_
#define OPENTITAN_SW_DEVICE_MASK_ROM_SYS_STATE_H_

#include <stdalign.h>
#include <stdbool.h>
#include <stdint.h>

#include "sw/device/lib/dif/dif_hmac.h"

// Header Extern Guard (so header can be used from C and C++)
#ifdef __cplusplus
extern "C" {
#endif  // __cplusplus

#define SYS_STATE_WARN_UNUSED_RESULT __attribute__((warn_unused_result))

// NOTE: This header has pending depenencies; the type definitions below exist
// as a stop gap until they exist.
typedef uint32_t rom_ext_manifest_tag_t;
typedef uint32_t dif_lifecycle_state_t;
typedef uint32_t dif_lifecycle_debug_state_t;

/**
 * The Device ID, a 256-bit blob stored in OTP.
 */
typedef struct sys_state_device_id {
  /**
   * The bytes that make up the blob.
   */
  alignas(uint32_t) uint8_t bytes[256 / 8];
} sys_state_device_id_t;

/**
 * The result of a System State operation.
 */
typedef enum sys_state_result {
  /**
   * Indicates that the operation succeeded.
   */
  kSysStateOk = 0,
  /**
   * Indicates an error coming from an external operation.
   *
   * For example, failures at the DIF level become this error.
   */
  kSysStateExternError,
  /**
   * Indicates that cached system state data was corrupt.
   *
   * Note that this function may be returned even when calling a getter for the
   * first time, since it may indicate that a *different* cached value, or some
   * book-keeping data, is corrupt.
   */
  kSysStateCorrupt,
} sys_state_result_t;

/**
 * Returns a pointer to the ROM_EXT security descriptor.
 *
 * The first time this function is called, it will initialize the underlying
 * RAM storage for this system state datum. On every following call, it will
 * recompute the datum; if it does not match the stored value,
 * `kSysStateCorrupt` will be returned.
 *
 * The returned pointer should be stored only for as long as it is desired to
 * not re-check the RAM-cached value. In other words, the lifetime of the
 * returned pointer should only be as long as a caller feels it is acceptable to
 * use the value without re-checking it.
 *
 * The `ptr` out param may be NULL; this will perform a check without needing to
 * allocate space for the return value.
 *
 * @param[out] ptr Out-param for the pointed to the cached value (may be NULL).
 * @return The result of the operation.
 */
SYS_STATE_WARN_UNUSED_RESULT
sys_state_result_t sys_state_rom_ext_security_descriptor(
    const rom_ext_manifest_tag_t **ptr);

/**
 * Returns a pointer to the Device ID, read from OTP.
 *
 * The first time this function is called, it will initialize the underlying
 * RAM storage for this system state datum. On every following call, it will
 * recompute the datum; if it does not match the stored value,
 * `kSysStateCorrupt` will be returned.
 *
 * The returned pointer should be stored only for as long as it is desired to
 * not re-check the RAM-cached value. In other words, the lifetime of the
 * returned pointer should only be as long as a caller feels it is acceptable to
 * use the value without re-checking it.
 *
 * The `ptr` out param may be NULL; this will perform a check without needing to
 * allocate space for the return value.
 *
 * @param[out] ptr Out-param for the pointed to the cached value (may be NULL).
 * @return The result of the operation.
 */
SYS_STATE_WARN_UNUSED_RESULT
sys_state_result_t sys_state_device_id(const sys_state_device_id_t **ptr);

/**
 * Returns a pointer to the current lifecycle state.
 *
 * The first time this function is called, it will initialize the underlying
 * RAM storage for this system state datum. On every following call, it will
 * recompute the datum; if it does not match the stored value,
 * `kSysStateCorrupt` will be returned.
 *
 * The returned pointer should be stored only for as long as it is desired to
 * not re-check the RAM-cached value. In other words, the lifetime of the
 * returned pointer should only be as long as a caller feels it is acceptable to
 * use the value without re-checking it.
 *
 * The `ptr` out param may be NULL; this will perform a check without needing to
 * allocate space for the return value.
 *
 * @param[out] ptr Out-param for the pointed to the cached value (may be NULL).
 * @return The result of the operation.
 */
SYS_STATE_WARN_UNUSED_RESULT
sys_state_result_t sys_state_lifecycle_state(const dif_lifecycle_state_t **ptr);

/**
 * Returns a pointer to the current debug state.
 *
 * The first time this function is called, it will initialize the underlying
 * RAM storage for this system state datum. On every following call, it will
 * recompute the datum; if it does not match the stored value,
 * `kSysStateCorrupt` will be returned.
 *
 * The returned pointer should be stored only for as long as it is desired to
 * not re-check the RAM-cached value. In other words, the lifetime of the
 * returned pointer should only be as long as a caller feels it is acceptable to
 * use the value without re-checking it.
 *
 * The `ptr` out param may be NULL; this will perform a check without needing to
 * allocate space for the return value.
 *
 * @param[out] ptr Out-param for the pointed to the cached value (may be NULL).
 * @return The result of the operation.
 */
SYS_STATE_WARN_UNUSED_RESULT
sys_state_result_t sys_state_debug_state(
    const dif_lifecycle_debug_state_t **ptr);

/**
 * Returns a pointer to the health state, which is a combined measurement of the
 * lifecycle and debug states.
 *
 * The first time this function is called, it will initialize the underlying
 * RAM storage for this system state datum. On every following call, it will
 * recompute the datum; if it does not match the stored value,
 * `kSysStateCorrupt` will be returned.
 *
 * The returned pointer should be stored only for as long as it is desired to
 * not re-check the RAM-cached value. In other words, the lifetime of the
 * returned pointer should only be as long as a caller feels it is acceptable to
 * use the value without re-checking it.
 *
 * The `ptr` out param may be NULL; this will perform a check without needing to
 * allocate space for the return value.
 *
 * @param[out] ptr Out-param for the pointed to the cached value (may be NULL).
 * @return The result of the operation.
 */
SYS_STATE_WARN_UNUSED_RESULT
sys_state_result_t sys_state_health_state(const dif_hmac_digest_t **ptr);

/**
 * Dumps all cached state into the Key Manager.
 *
 * (This function will remain unimplemented for now, since it is not part of
 * v0.5).
 */
SYS_STATE_WARN_UNUSED_RESULT
sys_state_result_t sys_state_build_creator_root_key(void);

#ifdef __cplusplus
}  // extern "C"
#endif  // __cplusplus

#endif  // OPENTITAN_SW_DEVICE_MASK_ROM_SYS_STATE_H_
