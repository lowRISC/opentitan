// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/lib/attestation_key_diversifiers.h"

// UDS (Creator) attestation key diverisfier constants.
// Note: versions are always set to 0 so these keys are always valid from the
// perspective of the keymgr hardware.
const sc_keymgr_diversification_t kUdsKeymgrDiversifier = {
    .salt =
        {
            0xabffa6a9,
            0xc781f1ad,
            0x4c1107ad,
            0xf9210d85,
            0x0931f555,
            0x6c5aef5d,
            0xb9ba4df0,
            0x77b248d2,
        },
    .version = 0,
};

// CDI_0 (OwnerIntermediate) attestation key diverisfier constants.
const sc_keymgr_diversification_t kCdi0KeymgrDiversifier = {
    .salt =
        {
            0x3e5913c7,
            0x41156f1d,
            0x998ddb9f,
            0xfa334191,
            0x8a85380e,
            0xba76ca1a,
            0xdb17c4a7,
            0xfb8852dc,
        },
    .version = 0,
};

// CDI_1 (Owner) attestation key diverisfier constants.
const sc_keymgr_diversification_t kCdi1KeymgrDiversifier = {
    .salt =
        {
            0x2d12c2e3,
            0x6acc6876,
            0x4bfb07ee,
            0xc45fc414,
            0x5d4fa9de,
            0xf295b128,
            0x50f49882,
            0xbbdefa29,
        },
    .version = 0,
};

const sc_keymgr_diversification_t kTpmEkKeymgrDiversifier = {
    .salt =
        {
            0x3fd3bc42,
            0x5a401205,
            0xfa3fbe70,
            0xc1d035da,
            0x87292fe6,
            0x4d94f30f,
            0x2e954c30,
            0x351c28f1,
        },
    .version = 0,
};

const sc_keymgr_diversification_t kTpmCekKeymgrDiversifier = {
    .salt =
        {
            0x8a5d086c,
            0xcbe850b4,
            0x9aeab7c0,
            0x8faf44a4,
            0xc5bf5663,
            0x217359ab,
            0xb42fe0fd,
            0xd06ad674,
        },
    .version = 0,

};

const sc_keymgr_diversification_t kTpmCikKeymgrDiversifier = {
    .salt =
        {
            0x9d664be2,
            0x8a9739a9,
            0xe6f815bd,
            0x8940348b,
            0x6ee241f7,
            0xea5b14cd,
            0x9e81908b,
            0x15ff16f0,
        },
    .version = 0,
};
