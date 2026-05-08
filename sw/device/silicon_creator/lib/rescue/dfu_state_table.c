// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/rescue/dfu.h"

// clang-format off
// We map state transitions for every DFU request for every DFU state.
//
// The ROM_EXT will never be in the AppIdle or AppDetach states, but we include them
// so that the state table is complete.
dfu_state_transition_t dfu_state_table[kDfuReqTotalLength][kDfuStateTotalLength] = {
    [kDfuReqDetach] =
        {
            [kDfuStateAppIdle] = {kDfuActionNone, {kDfuStateAppDetach}},
            [kDfuStateAppDetach] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateIdle] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateDnLoadSync] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateDnLoadBusy] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateDnLoadIdle] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateManifestSync] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateManifest] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateManifestWaitReset] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateUpLoadIdle] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateError] = {kDfuActionStall, {kDfuStateError}},
        },
    [kDfuReqDnLoad] =
        {
            [kDfuStateAppIdle] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateAppDetach] = {kDfuActionStall, {kDfuStateError}},
            // DataXfer chooses next[0] when length == 0, next[1] otherwise.
            [kDfuStateIdle] = {kDfuActionDataXfer, {kDfuStateError, kDfuStateDnLoadSync}},
            [kDfuStateDnLoadSync] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateDnLoadBusy] = {kDfuActionStall, {kDfuStateError}},
            // DataXfer chooses next[0] when length == 0, next[1] otherwise.
            [kDfuStateDnLoadIdle] = {kDfuActionDataXfer, {kDfuStateManifestSync, kDfuStateDnLoadSync}},
            [kDfuStateManifestSync] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateManifest] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateManifestWaitReset] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateUpLoadIdle] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateError] = {kDfuActionStall, {kDfuStateError}},
        },
    [kDfuReqUpLoad] =
        {
            [kDfuStateAppIdle] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateAppDetach] = {kDfuActionStall, {kDfuStateError}},
            // DataXfer chooses next[0] when length == 0, next[1] otherwise.
            [kDfuStateIdle] = {kDfuActionDataXfer, {kDfuStateUpLoadIdle, kDfuStateUpLoadIdle}},
            [kDfuStateDnLoadSync] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateDnLoadBusy] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateDnLoadIdle] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateManifestSync] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateManifest] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateManifestWaitReset] = {kDfuActionStall, {kDfuStateError}},
            // DataXfer chooses next[0] when length == 0, next[1] otherwise.
            [kDfuStateUpLoadIdle] = {kDfuActionDataXfer, {kDfuStateIdle, kDfuStateUpLoadIdle}},
            [kDfuStateError] = {kDfuActionStall, {kDfuStateError}},
        },
    [kDfuReqGetStatus] =
        {
            [kDfuStateAppIdle] = {kDfuActionStatusResponse, {kDfuStateAppIdle}},
            [kDfuStateAppDetach] = {kDfuActionStatusResponse, {kDfuStateAppDetach}},
            [kDfuStateIdle] = {kDfuActionStatusResponse, {kDfuStateIdle}},
            [kDfuStateDnLoadSync] = {kDfuActionStatusResponse, {kDfuStateDnLoadIdle}},
            [kDfuStateDnLoadBusy] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateDnLoadIdle] = {kDfuActionStatusResponse, {kDfuStateDnLoadIdle}},
            [kDfuStateManifestSync] = {kDfuActionStatusResponse, {kDfuStateIdle}},
            [kDfuStateManifest] = {kDfuActionStatusResponse, {kDfuStateManifestSync}},
            [kDfuStateManifestWaitReset] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateUpLoadIdle] = {kDfuActionStatusResponse, {kDfuStateUpLoadIdle}},
            [kDfuStateError] = {kDfuActionStatusResponse, {kDfuStateError}},
        },
    [kDfuReqClrStatus] =
        {
            [kDfuStateAppIdle] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateAppDetach] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateIdle] = {kDfuActionStall, {kDfuStateIdle}},
            [kDfuStateDnLoadSync] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateDnLoadBusy] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateDnLoadIdle] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateManifestSync] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateManifest] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateManifestWaitReset] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateUpLoadIdle] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateError] = {kDfuActionClearError, {kDfuStateIdle}},
        },
    [kDfuReqGetState] =
        {
            [kDfuStateAppIdle] = {kDfuActionStateResponse, {kDfuStateAppIdle}},
            [kDfuStateAppDetach] = {kDfuActionStateResponse, {kDfuStateAppDetach}},
            [kDfuStateIdle] = {kDfuActionStateResponse, {kDfuStateUpLoadIdle}},
            [kDfuStateDnLoadSync] = {kDfuActionStateResponse, {kDfuStateDnLoadIdle}},
            [kDfuStateDnLoadBusy] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateDnLoadIdle] = {kDfuActionStateResponse, {kDfuStateDnLoadIdle}},
            [kDfuStateManifestSync] = {kDfuActionStateResponse, {kDfuStateManifestSync}},
            [kDfuStateManifest] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateManifestWaitReset] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateUpLoadIdle] = {kDfuActionStateResponse, {kDfuStateUpLoadIdle}},
            [kDfuStateError] = {kDfuActionStateResponse, {kDfuStateError}},
        },
    [kDfuReqAbort] =
        {
            [kDfuStateAppIdle] = {kDfuActionStall, {kDfuStateAppIdle}},
            [kDfuStateAppDetach] = {kDfuActionStall, {kDfuStateAppDetach}},
            [kDfuStateIdle] = {kDfuActionNone, {kDfuStateIdle}},
            [kDfuStateDnLoadSync] = {kDfuActionNone, {kDfuStateIdle}},
            [kDfuStateDnLoadBusy] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateDnLoadIdle] = {kDfuActionNone, {kDfuStateIdle}},
            [kDfuStateManifestSync] = {kDfuActionNone, {kDfuStateIdle}},
            [kDfuStateManifest] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateManifestWaitReset] = {kDfuActionStall, {kDfuStateError}},
            [kDfuStateUpLoadIdle] = {kDfuActionNone, {kDfuStateIdle}},
            [kDfuStateError] = {kDfuActionStall, {kDfuStateError}},
        },

};
// clang-format on
