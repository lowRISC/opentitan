// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/silicon_creator/mask_rom/sig_verify_keys.h"

/**
 * Public keys for signature verification.
 *
 * Note: Updating the struct below currently requires some manual steps since we
 * don't have a tool to generate them yet:
 * - `n` (modulus) can be obtained using `openssl` and converting its output to
 * little-endian,
 * - `n0_inv` can be computed using `n[0]`, and
 * - `exponent` can be obtained using `openssl`.
 *
 * Please see sw/device/silicon_creator/keys/README.md for more details.
 */
const sigverify_rsa_key_t kSigVerifyRsaKeys[kSigVerifyNumRsaKeys] = {
    // sw/device/silicon_creator/keys/fpga_key_0.public.der
    [0] =
        {
            .n = {{
                0x5801a2bd, 0xeff64a46, 0xc8cf2251, 0xa7cd62cb, 0x634a39c2,
                0x55c936d3, 0x463d61fc, 0x762ebbaa, 0x01aadfb2, 0x23da15d1,
                0x8475fdc6, 0x4ec67b7b, 0xe9364570, 0xd23ec7c7, 0x98038d63,
                0x5688a56b, 0x68037add, 0xb20ff289, 0x9d96c1ce, 0xbac0b8cd,
                0xead33d0b, 0x195f89c8, 0xd7dc110e, 0xf5bccc12, 0x8dfa33dc,
                0xedc404d2, 0x74ef8524, 0x9197c0c8, 0x79cc448e, 0x4c9c505d,
                0x4a586ad7, 0xe2d0f071, 0x589f28c2, 0x2ca7fc22, 0x0354b0e2,
                0xefb63b44, 0x33a75b04, 0x9e194454, 0x1b4b2cde, 0x8e3f78e0,
                0x5260877c, 0x05685b72, 0x4868ad4e, 0x10303ac9, 0x05ac2411,
                0x5e797381, 0xd5407668, 0xe3522348, 0xa33134f8, 0x38f7a953,
                0xd926f672, 0x136f6753, 0xb186b0ab, 0x5ccab586, 0x61e5bf2e,
                0x9fc0eebb, 0x788ed0bd, 0x47b5fc70, 0xf971262a, 0x3b40d99b,
                0x5b9fd926, 0xce3c93bf, 0xd406005e, 0x72b9e555, 0xc9b9273e,
                0xfcef747f, 0xf0a35598, 0x2761e8f6, 0xec1799df, 0x462bc52d,
                0x8e47218b, 0x429ccdae, 0xe7e7d66c, 0x70c70b03, 0x0356c3d2,
                0x3cb3e7d1, 0xd42d035d, 0x83c529a3, 0x8df9930e, 0xb082e1f0,
                0x07509c30, 0x5c33a350, 0x4f6884b9, 0x7b9d2de0, 0x0f1d16b3,
                0x38dbcf55, 0x168580ea, 0xc2f2aca4, 0x43f0ae60, 0x227dd2ed,
                0xd8dc61f4, 0x9404e8bc, 0x0db76fe3, 0x3491d3b0, 0x6ca44e27,
                0xcda63719,
            }},
            .n0_inv = 0x9c9a176b,
            .exponent = 65537,
        },
    // sw/device/silicon_creator/keys/fpga_key_1.public.der
    [1] =
        {
            .n = {{
                0xbd158913, 0xab75ea1a, 0xc04e5292, 0x68f5778a, 0xa71418c7,
                0xddc4fc1c, 0xcb09302d, 0xedf3142b, 0x656d7d85, 0xf761d32a,
                0x2d334d1b, 0x26c91770, 0x5b9ba5a0, 0x00ac6c05, 0xbabaf1bb,
                0xa8299ecc, 0xb4223f99, 0x5b676ad3, 0xcaa786c2, 0x3e2f1785,
                0x204b6991, 0x21fa118f, 0x435573ab, 0xa3353ba1, 0x1074c161,
                0x2ad5e901, 0x7310247c, 0x1e21b8e9, 0x0cfc7762, 0x0a9139b1,
                0xfc655b33, 0x6990faaf, 0xbb88faec, 0x7c7bd6ef, 0x261e4555,
                0x6bc3d813, 0x5ce6e18b, 0xdd308629, 0x37d3d54d, 0x65acd84d,
                0x97b7e0c3, 0xc0d35caa, 0xb0be177a, 0x09473af3, 0x67f43155,
                0x3b2f7661, 0xf9255df2, 0x1b42c84c, 0x355cd607, 0x835e74ca,
                0x1d011c4e, 0x46652555, 0x1566f96f, 0x6cffd2f9, 0x204e783e,
                0xa178a2eb, 0xe7297a95, 0xd7380039, 0x1a685545, 0x76ed97c9,
                0x6bc0b1b7, 0xd9b1338e, 0xa3b23005, 0x6fe7109f, 0x01c232e1,
                0x851639c5, 0xe81d338c, 0x25ebe0c4, 0x5b0202cd, 0x3690cb70,
                0xad13b664, 0x8bf7833e, 0x6017349c, 0xf6e90b08, 0x953ef3d8,
                0x4bc11817, 0xd0f6e840, 0xfe01a954, 0x9b866209, 0xb9653ff8,
                0x0d654f5c, 0xff78177c, 0x3688833c, 0x57cc0c30, 0x71965be7,
                0xf61fb728, 0xaeac8ca2, 0xbdc9848b, 0x954c529f, 0x9917ac7f,
                0x4ba4c007, 0xce2dbf0b, 0xfc7d8504, 0x2712580b, 0xd0293151,
                0xa4dbbff3,
            }},
            .n0_inv = 0x079056e5,
            .exponent = 3,
        },
};

// `extern` declarations for `inline` functions in the header.
extern uint32_t sigverify_rsa_key_id_get(const sigverify_rsa_key_t *key);
