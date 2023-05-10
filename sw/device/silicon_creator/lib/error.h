// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_ERROR_H_
#define OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_ERROR_H_

#include "sw/device/lib/base/bitfield.h"
#include "sw/device/lib/base/hardened.h"

#define USING_INTERNAL_STATUS
#include "sw/device/lib/base/internal/status.h"
#undef USING_INTERNAL_STATUS

#ifdef __cplusplus
extern "C" {
#endif

/**
 * List of modules which can produce errors.
 *
 * Choose a two-letter identifier for each module and encode the module
 * identifier the concatenated ASCII representation of those letters.
 */
#define MODULE_CODE(ch0_, ch1_) ((ch0_) << 8 | (ch1_))
enum module_ {
  // clang-format off
  kModuleUnknown = 0,
  kModuleAlertHandler = MODULE_CODE('A', 'H'),
  kModuleSigverify =    MODULE_CODE('S', 'V'),
  kModuleKeymgr =       MODULE_CODE('K', 'M'),
  kModuleManifest =     MODULE_CODE('M', 'A'),
  kModuleRom =          MODULE_CODE('M', 'R'),
  kModuleInterrupt =    MODULE_CODE('I', 'R'),
  kModuleEpmp =         MODULE_CODE('E', 'P'),
  kModuleKmac =         MODULE_CODE('K', 'C'),
  kModuleOtbn =         MODULE_CODE('B', 'N'),
  kModuleFlashCtrl =    MODULE_CODE('F', 'C'),
  kModuleBootPolicy =   MODULE_CODE('B', 'P'),
  kModuleBootstrap =    MODULE_CODE('B', 'S'),
  kModuleLog =          MODULE_CODE('L', 'G'),
  kModuleBootData =     MODULE_CODE('B', 'D'),
  kModuleSpiDevice =    MODULE_CODE('S', 'P'),
  kModuleAst =          MODULE_CODE('A', 'S'),
  KModuleRnd =          MODULE_CODE('R', 'N'),
  // clang-format on
};

/**
 * Field definitions for the different fields of the error word.
 */
#define ROM_ERROR_FIELD_ERROR ((bitfield_field32_t){.mask = 0xFF, .index = 24})
#define ROM_ERROR_FIELD_MODULE \
  ((bitfield_field32_t){.mask = 0xFFFF, .index = 8})
#define ROM_ERROR_FIELD_STATUS ((bitfield_field32_t){.mask = 0xFF, .index = 0})

/**
 * Helper macro for building up error codes.
 * @param status_ An appropriate general status code from absl_staus.h.
 * @param module_ The module identifier which produces this error.
 * @param error_ The unique error id in that module.  Error ids must not
 *               repeat within a module.
 */
#define ERROR_(error_, module_, status_) \
  ((error_ << 24) | (module_ << 8) | (status_))

// clang-format off
// Use an X-macro to facilitate writing unit tests.
// Note: This list is extend-only and you may not renumber errors after they
//       have been created.  This is required for error-space stability
//       after the ROM is frozen.
#define DEFINE_ERRORS(X) \
  X(kErrorOk,                         0x739), \
  X(kErrorUnknown,                    0xffffffff), \
  \
  X(kErrorSigverifyBadRsaSignature,   ERROR_(1, kModuleSigverify, kInvalidArgument)), \
  X(kErrorSigverifyBadSpxSignature,   ERROR_(2, kModuleSigverify, kInvalidArgument)), \
  X(kErrorSigverifyBadKey,            ERROR_(3, kModuleSigverify, kInvalidArgument)), \
  X(kErrorSigverifyBadRsaKey,         ERROR_(4, kModuleSigverify, kInvalidArgument)), \
  X(kErrorSigverifyBadSpxKey,         ERROR_(5, kModuleSigverify, kInvalidArgument)), \
  X(kErrorSigverifyLargeRsaSignature, ERROR_(6, kModuleSigverify, kInvalidArgument)), \
  \
  X(kErrorKeymgrInternal,             ERROR_(1, kModuleKeymgr, kInternal)), \
  \
  X(kErrorManifestBadEntryPoint,      ERROR_(1, kModuleManifest, kInternal)), \
  X(kErrorManifestBadCodeRegion,      ERROR_(2, kModuleManifest, kInternal)), \
  X(kErrorManifestBadSignedRegion,    ERROR_(3, kModuleManifest, kInternal)), \
  X(kErrorManifestBadExtension,       ERROR_(4, kModuleManifest, kInternal)), \
  \
  X(kErrorAlertBadIndex,              ERROR_(1, kModuleAlertHandler, kInvalidArgument)), \
  X(kErrorAlertBadClass,              ERROR_(2, kModuleAlertHandler, kInvalidArgument)), \
  X(kErrorAlertBadEnable,             ERROR_(3, kModuleAlertHandler, kInvalidArgument)), \
  X(kErrorAlertBadEscalation,         ERROR_(4, kModuleAlertHandler, kInvalidArgument)), \
  X(kErrorAlertBadCrc32,              ERROR_(5, kModuleAlertHandler, kInvalidArgument)), \
  \
  X(kErrorRomBootFailed,              ERROR_(1, kModuleRom, kFailedPrecondition)), \
  \
  /* The high-byte of kErrorInterrupt is modified with the interrupt cause */ \
  X(kErrorInterrupt,                  ERROR_(0, kModuleInterrupt, kUnknown)), \
  \
  X(kErrorEpmpBadCheck,               ERROR_(1, kModuleEpmp, kInternal)), \
  \
  X(kErrorKmacInvalidStatus,          ERROR_(1, kModuleKmac, kInternal)), \
  \
  X(kErrorOtbnInvalidArgument,        ERROR_(1, kModuleOtbn, kInvalidArgument)), \
  X(kErrorOtbnBadOffsetLen,           ERROR_(2, kModuleOtbn, kInvalidArgument)), \
  X(kErrorOtbnExecutionFailed,        ERROR_(3, kModuleOtbn, kInternal)), \
  X(kErrorOtbnSecWipeImemFailed,      ERROR_(4, kModuleOtbn, kInternal)), \
  X(kErrorOtbnSecWipeDmemFailed,      ERROR_(5, kModuleOtbn, kInternal)), \
  X(kErrorOtbnBadInsnCount,           ERROR_(6, kModuleOtbn, kInternal)), \
  X(kErrorOtbnUnavailable,            ERROR_(7, kModuleOtbn, kInternal)), \
  \
  X(kErrorFlashCtrlDataRead,          ERROR_(1, kModuleFlashCtrl, kInternal)), \
  X(kErrorFlashCtrlInfoRead,          ERROR_(2, kModuleFlashCtrl, kInternal)), \
  X(kErrorFlashCtrlDataWrite,         ERROR_(3, kModuleFlashCtrl, kInternal)), \
  X(kErrorFlashCtrlInfoWrite,         ERROR_(4, kModuleFlashCtrl, kInternal)), \
  X(kErrorFlashCtrlDataErase,         ERROR_(5, kModuleFlashCtrl, kInternal)), \
  X(kErrorFlashCtrlInfoErase,         ERROR_(6, kModuleFlashCtrl, kInternal)), \
  X(kErrorFlashCtrlDataEraseVerify,   ERROR_(7, kModuleFlashCtrl, kInternal)), \
  \
  X(kErrorBootPolicyBadIdentifier,    ERROR_(1, kModuleBootPolicy, kInternal)), \
  X(kErrorBootPolicyBadLength,        ERROR_(2, kModuleBootPolicy, kInternal)), \
  X(kErrorBootPolicyRollback,         ERROR_(3, kModuleBootPolicy, kInternal)), \
  \
  X(kErrorBootstrapEraseAddress,      ERROR_(1, kModuleBootstrap, kInvalidArgument)), \
  X(kErrorBootstrapProgramAddress,    ERROR_(2, kModuleBootstrap, kInvalidArgument)), \
  X(kErrorBootstrapInvalidState,      ERROR_(3, kModuleBootstrap, kInvalidArgument)), \
  X(kErrorBootstrapNotRequested,      ERROR_(4, kModuleBootstrap, kInternal)), \
  \
  X(kErrorLogBadFormatSpecifier,      ERROR_(1, kModuleLog, kInternal)), \
  \
  X(kErrorBootDataNotFound,           ERROR_(1, kModuleBootData, kInternal)), \
  X(kErrorBootDataWriteCheck,         ERROR_(2, kModuleBootData, kInternal)), \
  X(kErrorBootDataInvalid,            ERROR_(3, kModuleBootData, kInternal)), \
  \
  X(kErrorSpiDevicePayloadOverflow,   ERROR_(1, kModuleSpiDevice, kInternal)), \
  \
  X(kErrorAstInitNotDone,             ERROR_(1, kModuleAst, kInternal)), \
  \
  X(kErrorRndBadCrc32,                ERROR_(1, KModuleRnd, kInvalidArgument))
// clang-format on

#define ERROR_ENUM_INIT(name_, value_) name_ = value_

/**
 * Unified set of errors for ROM and ROM_EXT.
 */
typedef enum rom_error {
  DEFINE_ERRORS(ERROR_ENUM_INIT),
} rom_error_t;

/**
 * Evaluate an expression and return if the result is an error.
 *
 * @param expr_ An expression which results in a `rom_error_t`.
 */
#define RETURN_IF_ERROR(expr_)        \
  do {                                \
    rom_error_t local_error_ = expr_; \
    if (local_error_ != kErrorOk) {   \
      return local_error_;            \
    }                                 \
  } while (false)

/**
 * Hardened version of `RETURN_IF_ERROR()`.
 *
 * See `launder32()` and `HARDENED_CHECK_EQ()` in
 * `sw/device/lib/base/hardened.h` for more details.
 *
 * @param expr_ An expression which results in a `rom_error_t`.
 */
#define HARDENED_RETURN_IF_ERROR(expr_)  \
  do {                                   \
    rom_error_t error_ = expr_;          \
    if (launder32(error_) != kErrorOk) { \
      return error_;                     \
    }                                    \
    HARDENED_CHECK_EQ(error_, kErrorOk); \
  } while (false)

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_SILICON_CREATOR_LIB_ERROR_H_
