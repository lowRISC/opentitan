// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_SW_DEVICE_LIB_UJSON_PRIVATE_STATUS_H_
#define OPENTITAN_SW_DEVICE_LIB_UJSON_PRIVATE_STATUS_H_

#include "sw/device/lib/ujson/ujson_derive.h"

#ifdef __cplusplus
extern "C" {
#endif

// Note: the PrivateStatus enum values must be in the same order as the
// values in //sw/device/lib/base/absl_status.h.

// clang-format off
#define ENUM_PRIVATE_STATUS(_, value) \
    value(_, Ok) \
    value(_, Cancelled) \
    value(_, Unknown) \
    value(_, InvalidArgument) \
    value(_, DeadlineExceeded) \
    value(_, NotFound) \
    value(_, AlreadyExists) \
    value(_, PermissionDenied) \
    value(_, ResourceExhausted) \
    value(_, FailedPrecondition) \
    value(_, Aborted) \
    value(_, OutOfRange) \
    value(_, Unimplemented) \
    value(_, Internal) \
    value(_, Unavailable) \
    value(_, DataLoss) \
    value(_, Unauthenticated)

// We don't need a serialize implementation because the printf extension for
// status_t already serializes in a JSON-compatible form.
UJSON_DECLARE_ENUM(PrivateStatus, private_status_t, ENUM_PRIVATE_STATUS);
UJSON_DESERIALIZE_ENUM(PrivateStatus, private_status_t, ENUM_PRIVATE_STATUS);

#ifdef __cplusplus
}
#endif
#endif  // OPENTITAN_SW_DEVICE_LIB_UJSON_PRIVATE_STATUS_H_
