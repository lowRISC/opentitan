// Copyright lowRISC contributors (OpenTitan project).
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
  kModuleAlertHandler =    MODULE_CODE('A', 'H'),
  kModuleSigverify =       MODULE_CODE('S', 'V'),
  kModuleKeymgr =          MODULE_CODE('K', 'M'),
  kModuleManifest =        MODULE_CODE('M', 'A'),
  kModuleRom =             MODULE_CODE('M', 'R'),
  kModuleInterrupt =       MODULE_CODE('I', 'R'),
  kModuleEpmp =            MODULE_CODE('E', 'P'),
  kModuleKmac =            MODULE_CODE('K', 'C'),
  kModuleOtbn =            MODULE_CODE('B', 'N'),
  kModuleFlashCtrl =       MODULE_CODE('F', 'C'),
  kModuleBootPolicy =      MODULE_CODE('B', 'P'),
  kModuleBootstrap =       MODULE_CODE('B', 'S'),
  kModuleLog =             MODULE_CODE('L', 'G'),
  kModuleBootData =        MODULE_CODE('B', 'D'),
  kModuleSpiDevice =       MODULE_CODE('S', 'P'),
  kModuleAst =             MODULE_CODE('A', 'S'),
  kModuleRstmgr =          MODULE_CODE('R', 'S'),
  KModuleRnd =             MODULE_CODE('R', 'N'),
  kModuleBootSvc =         MODULE_CODE('B', 'C'),
  kModuleBootLog =         MODULE_CODE('B', 'L'),
  kModuleRomExt =          MODULE_CODE('R', 'E'),
  kModuleRomExtInterrupt = MODULE_CODE('R', 'I'),
  kModuleAsn1 =            MODULE_CODE('A', '1'),
  kModuleRetRam =          MODULE_CODE('R', 'R'),
  kModuleXModem =          MODULE_CODE('X', 'M'),
  kModuleRescue =          MODULE_CODE('R', 'S'),
  kModuleDice =            MODULE_CODE('D', 'C'),
  kModuleCert =            MODULE_CODE('C', 'E'),
  kModuleOwnership =       MODULE_CODE('O', 'W'),
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
  X(kErrorWriteBootdataThenReboot,    0x2ea), \
  X(kErrorUnknown,                    0xffffffff), \
  \
  X(kErrorSigverifyBadRsaSignature,   ERROR_(1, kModuleSigverify, kInvalidArgument)), \
  X(kErrorSigverifyBadSpxSignature,   ERROR_(2, kModuleSigverify, kInvalidArgument)), \
  X(kErrorSigverifyBadKey,            ERROR_(3, kModuleSigverify, kInvalidArgument)), \
  X(kErrorSigverifyBadRsaKey,         ERROR_(4, kModuleSigverify, kInvalidArgument)), \
  X(kErrorSigverifyBadSpxKey,         ERROR_(5, kModuleSigverify, kInvalidArgument)), \
  X(kErrorSigverifyLargeRsaSignature, ERROR_(6, kModuleSigverify, kInvalidArgument)), \
  X(kErrorSigverifyBadEcdsaSignature, ERROR_(7, kModuleSigverify, kInvalidArgument)), \
  X(kErrorSigverifyBadAuthPartition,  ERROR_(8, kModuleSigverify, kInvalidArgument)), \
  X(kErrorSigverifyBadEcdsaKey,       ERROR_(9, kModuleSigverify, kInvalidArgument)), \
  \
  X(kErrorKeymgrInternal,             ERROR_(1, kModuleKeymgr, kInternal)), \
  \
  X(kErrorManifestBadEntryPoint,      ERROR_(1, kModuleManifest, kInternal)), \
  X(kErrorManifestBadCodeRegion,      ERROR_(2, kModuleManifest, kInternal)), \
  X(kErrorManifestBadSignedRegion,    ERROR_(3, kModuleManifest, kInternal)), \
  X(kErrorManifestBadExtension,       ERROR_(4, kModuleManifest, kInternal)), \
  X(kErrorManifestBadVersionMajor,    ERROR_(5, kModuleManifest, kInternal)), \
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
  X(kErrorKmacInvalidKeySize,         ERROR_(2, kModuleKmac, kInvalidArgument)), \
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
  X(kErrorBootstrapDisabledRomExt,    ERROR_(5, kModuleBootstrap, kInternal)), \
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
  X(kErrorRstmgrBadInit,              ERROR_(1, kModuleRstmgr, kInternal)), \
  \
  X(kErrorRndBadCrc32,                ERROR_(1, KModuleRnd, kInvalidArgument)), \
  \
  X(kErrorBootSvcBadHeader,           ERROR_(1, kModuleBootSvc, kInternal)), \
  X(kErrorBootSvcBadSlot,             ERROR_(2, kModuleBootSvc, kInvalidArgument)), \
  X(kErrorBootSvcBadSecVer,           ERROR_(3, kModuleBootSvc, kInvalidArgument)), \
  \
  X(kErrorRomExtBootFailed,           ERROR_(1, kModuleRomExt, kFailedPrecondition)), \
  \
  X(kErrorXModemTimeoutStart,         ERROR_(1, kModuleXModem, kDeadlineExceeded)), \
  X(kErrorXModemTimeoutPacket,        ERROR_(2, kModuleXModem, kDeadlineExceeded)), \
  X(kErrorXModemTimeoutData,          ERROR_(3, kModuleXModem, kDeadlineExceeded)), \
  X(kErrorXModemTimeoutCrc,           ERROR_(4, kModuleXModem, kDeadlineExceeded)), \
  X(kErrorXModemTimeoutAck,           ERROR_(5, kModuleXModem, kDeadlineExceeded)), \
  X(kErrorXModemCrc,                  ERROR_(6, kModuleXModem, kDataLoss)), \
  X(kErrorXModemEndOfFile,            ERROR_(7, kModuleXModem, kOutOfRange)), \
  X(kErrorXModemCancel,               ERROR_(8, kModuleXModem, kCancelled)), \
  X(kErrorXModemUnknown,              ERROR_(9, kModuleXModem, kUnknown)), \
  X(kErrorXModemProtocol,             ERROR_(10, kModuleXModem, kInvalidArgument)), \
  X(kErrorXModemTooManyErrors,        ERROR_(11, kModuleXModem, kFailedPrecondition)), \
  \
  /* The high-byte of kErrorInterrupt is modified with the interrupt cause */ \
  X(kErrorRomExtInterrupt,            ERROR_(0, kModuleRomExtInterrupt, kUnknown)), \
  \
  X(kErrorBootLogInvalid,             ERROR_(1, kModuleBootLog, kInternal)), \
  \
  X(kErrorAsn1Internal,                       ERROR_(1, kModuleAsn1, kInternal)), \
  X(kErrorAsn1StartInvalidArgument,           ERROR_(2, kModuleAsn1, kInvalidArgument)), \
  X(kErrorAsn1PushBytesInvalidArgument,       ERROR_(3, kModuleAsn1, kInvalidArgument)), \
  X(kErrorAsn1PushIntegerPadInvalidArgument,  ERROR_(4, kModuleAsn1, kInvalidArgument)), \
  X(kErrorAsn1PushIntegerInvalidArgument,     ERROR_(5, kModuleAsn1, kInvalidArgument)), \
  X(kErrorAsn1FinishBitstringInvalidArgument, ERROR_(6, kModuleAsn1, kInvalidArgument)), \
  X(kErrorAsn1BufferExhausted,                ERROR_(7, kModuleAsn1, kResourceExhausted)), \
  \
  X(kErrorRetRamBadVersion,           ERROR_(1, kModuleRetRam, kUnknown)), \
  \
  X(kErrorRescueReboot,               ERROR_(0, kModuleRescue, kInternal)), \
  X(kErrorRescueBadMode,              ERROR_(1, kModuleRescue, kInvalidArgument)), \
  X(kErrorRescueImageTooBig,          ERROR_(2, kModuleRescue, kFailedPrecondition)), \
  \
  X(kErrorDiceInvalidKeyType,         ERROR_(0, kModuleDice, kInvalidArgument)), \
  \
  X(kErrorCertInternal,               ERROR_(0, kModuleCert, kInternal)), \
  X(kErrorCertInvalidArgument,        ERROR_(1, kModuleCert, kInvalidArgument)), \
  \
  X(kErrorOwnershipInvalidNonce,      ERROR_(0, kModuleOwnership, kInvalidArgument)), \
  X(kErrorOwnershipInvalidMode,       ERROR_(1, kModuleOwnership, kInvalidArgument)), \
  X(kErrorOwnershipInvalidSignature,  ERROR_(2, kModuleOwnership, kInvalidArgument)), \
  X(kErrorOwnershipInvalidState,      ERROR_(3, kModuleOwnership, kInvalidArgument)), \
  X(kErrorOwnershipInvalidRequest,    ERROR_(4, kModuleOwnership, kInvalidArgument)), \
  X(kErrorOwnershipInvalidTag,        ERROR_(5, kModuleOwnership, kInvalidArgument)), \
  X(kErrorOwnershipInvalidTagLength,  ERROR_(6, kModuleOwnership, kInvalidArgument)), \
  X(kErrorOwnershipDuplicateItem,     ERROR_(7, kModuleOwnership, kAlreadyExists)), \
  X(kErrorOwnershipFlashConfigLenth,  ERROR_(8, kModuleOwnership, kOutOfRange)), \
  X(kErrorOwnershipInvalidInfoPage,   ERROR_(9, kModuleOwnership, kInvalidArgument)), \
  X(kErrorOwnershipBadInfoPage,       ERROR_(10, kModuleOwnership, kInternal)), \
  X(kErrorOwnershipNoOwner,           ERROR_(11, kModuleOwnership, kInternal)), \
  X(kErrorOwnershipKeyNotFound,       ERROR_(12, kModuleOwnership, kNotFound)), \
  \
  /* This comment prevent clang from trying to format the macro. */

// clang-format on

#define ERROR_ENUM_INIT(name_, value_) name_ = value_

/**
 * Unified set of errors for ROM and ROM_EXT.
 */
typedef enum rom_error { DEFINE_ERRORS(ERROR_ENUM_INIT) } rom_error_t;

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
