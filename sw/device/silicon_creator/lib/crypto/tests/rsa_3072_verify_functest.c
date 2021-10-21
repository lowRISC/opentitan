// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/check.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/silicon_creator/lib/base/sec_mmio.h"
#include "sw/device/silicon_creator/lib/crypto/rsa_3072/rsa_3072_verify.h"
#include "sw/device/silicon_creator/lib/test_main.h"

static const rsa_3072_public_key_t kPublicKey = {
    .n = {.data = {0x6a6a75e1, 0xa018ddc5, 0x687bb168, 0x8e8205a5, 0x7dbfffa7,
                   0xc8722ac5, 0xf84d21cf, 0xe1312531, 0x0ce3f8a3, 0xa825f988,
                   0x57f51964, 0xb27e206a, 0x8e1dd008, 0x1c4fb8d7, 0x824fb142,
                   0x1c8be7b3, 0x7b9d6366, 0xc56ad0f2, 0xef762d5b, 0x4b1431e3,
                   0x8ae28eb9, 0xd41db7aa, 0x43cccdf7, 0x91b74a84, 0x80183850,
                   0x30e74d0d, 0xb62ed015, 0x235574d2, 0x8c28f251, 0x4f40def2,
                   0x24e2efdb, 0x9ebd1ff2, 0xfa7b49ee, 0x2819a938, 0x6e66b8c8,
                   0x24e41546, 0x4d783a7c, 0xd2947d3d, 0x1ab269e9, 0xfad39f16,
                   0xaab78f7b, 0x49d8b510, 0x35bf0dfb, 0xeb274754, 0x069eccc9,
                   0xc13c437e, 0xe3bc0f60, 0xc9e0e12f, 0xc253ac43, 0x89c240e0,
                   0xc4aba4e5, 0xedf34bc0, 0x5402c462, 0x4021b0bd, 0x996b6241,
                   0xc3d9945f, 0xa137ac60, 0xf0250bf5, 0xc8c7100f, 0xb70d6b88,
                   0x78916a8c, 0x33370e5d, 0x3970dcb9, 0xaf4c58b4, 0x5f78cb0d,
                   0xb02d90b7, 0xeb6c3d05, 0x04afc71a, 0x45185f0f, 0x987caa5b,
                   0x33976249, 0x565afdbc, 0x80a85056, 0x59e07655, 0x9a29e77d,
                   0x7a8dfb7f, 0x782e0204, 0x4d6713ff, 0x131000ea, 0xe18e1206,
                   0x21f57f30, 0xf24f038b, 0x59cf874d, 0x24c50525, 0xb52f170d,
                   0x46c9adde, 0x90e82c73, 0x1344ceaf, 0x663209f2, 0x24bd4fbf,
                   0x5e4ed04d, 0x0fce770a, 0x81f78793, 0xa792e13e, 0xa6c7bf58,
                   0xe1df9be8}},
    .e = 65537,
};

static const rsa_3072_constants_t kExpConstants = {
    .rr = {.data = {0xa3eb77fa, 0x9db9a2ac, 0x2c19d4ae, 0xfb5be1e7, 0xdd38f5fb,
                    0xd0f4fdda, 0xeb165cd3, 0x546a7cfe, 0xcd410c5c, 0x73f5cf6b,
                    0x1185bcae, 0xda2e2103, 0xbab5ae26, 0x76e77aba, 0xf49dd5f7,
                    0x32318a29, 0x689a85bc, 0x8aa862a9, 0x538c240e, 0xb61eab77,
                    0x9ccd73f2, 0x6563c81a, 0x6c65ac0e, 0x90b209bf, 0xe642e25e,
                    0x7e351549, 0x879a1830, 0xc75cbb02, 0xe0112362, 0xebc2405f,
                    0x01dc7990, 0x3d3d07f3, 0xc5b9a5be, 0x98d8cc33, 0xdd65e108,
                    0xce301343, 0x0dbdc0cb, 0xc204b9ca, 0xeabe1810, 0x9849163a,
                    0x234c8ff7, 0x9bc14e3b, 0x4b4c2226, 0x079883be, 0xba59c5f5,
                    0xd9c77317, 0x1ce689f5, 0x05f49af5, 0x7a83d42a, 0xc509b5ca,
                    0x0811a95f, 0x093520a2, 0x73649941, 0xd9691ef5, 0x6878ec0d,
                    0x4043add6, 0x7516d8b7, 0x5c7070ff, 0x4ce52e1d, 0xf209e123,
                    0xfe4319c4, 0x9774620a, 0x7a58d047, 0x524b09b7, 0x96cbf044,
                    0x2a9044a2, 0x514995dc, 0xe4b83ed6, 0xd21be300, 0x2966d4f8,
                    0xd9ee19c4, 0xb60788f6, 0xf8d074ab, 0xa7e13295, 0x93718edc,
                    0xba9fc096, 0x0ad2fbbc, 0x9fe0c363, 0x472a10b4, 0xda9c946b,
                    0x37276997, 0x04e452fc, 0xd19233b5, 0xa277ef0e, 0x49619ddd,
                    0xb5822d56, 0x6ca4d02f, 0x7d0c0fc3, 0xa29196e2, 0xb6988a4f,
                    0x785b7552, 0xeaee3c24, 0x87993424, 0xfcb49693, 0x21e64d84,
                    0x9e2dcea8}},
    .m0_inv = {0xf09b71df, 0xfd3e34f7, 0x0b908e3b, 0x95d310b2, 0x49659950,
               0xa96ced37, 0x711cad8b, 0x1dfc9779},
};

static const rsa_3072_int_t kSignature = {
    .data = {0xceb7e983, 0xe693b200, 0xf9153989, 0xcf899599, 0x1ec09fae,
             0xf2f88007, 0x2a24eed5, 0x9c5b7c4e, 0x21a153b2, 0xaf7583ae,
             0x04fdd694, 0x7550094b, 0xb2a69ac4, 0xe49d8022, 0x7ed6f162,
             0x14bb3a1b, 0xbb29d8dd, 0x5c5815c2, 0x7a80d848, 0xb122f449,
             0x59dca808, 0xbc1443e2, 0xe304ff93, 0xcc97ee4b, 0x42ef6b57,
             0x1436839f, 0xae860b45, 0x6a843a17, 0x2381fb91, 0x09fd0635,
             0xa431aac3, 0xd7220269, 0xdf3e2697, 0x35e2915e, 0xedba6956,
             0x1d387448, 0x930006df, 0x961e5f00, 0xf2a7e960, 0x884e4add,
             0x7dfe76b1, 0x4079aa79, 0x1f3a378d, 0x96c20697, 0x268aea57,
             0x2c8569a4, 0x0474f512, 0x2388555c, 0x58679953, 0xe73da3a0,
             0x43431b9a, 0x699f04d3, 0xfc0be066, 0xcce606f2, 0xd94cdfa0,
             0x6c1ddca3, 0xe96c11f6, 0xfc635db4, 0x3bdb4f69, 0xa621c3e7,
             0x9f292111, 0xb86e1e6b, 0xb74f923b, 0x592967a0, 0xc412097f,
             0x8c1c8ca7, 0x494fcdb6, 0x87c5fe0f, 0x50c01aee, 0x8a26368e,
             0xeaf12232, 0x7dade4d8, 0x39eb2ac6, 0x744f8aaa, 0xf34908ca,
             0x1e0c656c, 0xe96d4e29, 0x8575d194, 0xe439bd31, 0xa74a77e3,
             0x0f465b88, 0xf4e21152, 0x80400ad8, 0xe58501ec, 0xa29d7536,
             0x55c19326, 0x9ebbc63e, 0x20c75aee, 0xef6783d7, 0x59ffdba5,
             0x879b937b, 0x43a5c74c, 0x82b8f825, 0xfdf04b3a, 0x8fc62fbe,
             0x114e6da5}};

static const rsa_3072_int_t kMessage = {
    .data = {0x55555555, 0x55555555, 0x55555555, 0x55555555, 0x55555555,
             0x55555555, 0x55555555, 0x55555555, 0x55555555, 0x55555555,
             0x55555555, 0x55555555, 0x55555555, 0x55555555, 0x55555555,
             0x55555555, 0x55555555, 0x55555555, 0x55555555, 0x55555555,
             0x55555555, 0x55555555, 0x55555555, 0x55555555, 0x55555555,
             0x55555555, 0x55555555, 0x55555555, 0x55555555, 0x55555555,
             0x55555555, 0x55555555, 0x55555555, 0x55555555, 0x55555555,
             0x55555555, 0x55555555, 0x55555555, 0x55555555, 0x55555555,
             0x55555555, 0x55555555, 0x55555555, 0x55555555, 0x55555555,
             0x55555555, 0x55555555, 0x55555555, 0x55555555, 0x55555555,
             0x55555555, 0x55555555, 0x55555555, 0x55555555, 0x55555555,
             0x55555555, 0x55555555, 0x55555555, 0x55555555, 0x55555555,
             0x55555555, 0x55555555, 0x55555555, 0x55555555, 0x55555555,
             0x55555555, 0x55555555, 0x55555555, 0x55555555, 0x55555555,
             0x55555555, 0x55555555, 0x55555555, 0x55555555, 0x55555555,
             0x55555555, 0x55555555, 0x55555555, 0x55555555, 0x55555555,
             0x55555555, 0x55555555, 0x55555555, 0x55555555, 0x55555555,
             0x55555555, 0x55555555, 0x55555555, 0x55555555, 0x55555555,
             0x55555555, 0x55555555, 0x55555555, 0x55555555, 0x55555555,
             0x55555555}};

rom_error_t precomp_test(void) {
  rsa_3072_constants_t act_constants;

  // Precompute constants
  RETURN_IF_ERROR(rsa_3072_precomp(&kPublicKey, &act_constants));

  // Check that RR matches expected value
  for (int i = 0; i < kRsa3072NumWords; i++) {
    CHECK(act_constants.rr.data[i] == kExpConstants.rr.data[i],
          "Mismatch at word %d of R^2: expected=0x%x, actual=0x%x", i,
          kExpConstants.rr.data[i], act_constants.rr.data[i]);
  }

  // Check that m0_inv matches expected value
  for (int i = 0; i < kOtbnWideWordNumWords; i++) {
    CHECK(act_constants.m0_inv[i] == kExpConstants.m0_inv[i],
          "Mismatch at word %d of m0_inv: expected=0x%x, actual=0x%x", i,
          kExpConstants.m0_inv[i], act_constants.m0_inv[i]);
  }

  return kErrorOk;
}

rom_error_t verify_test(void) {
  hardened_bool_t result;

  RETURN_IF_ERROR(rsa_3072_verify(&kSignature, &kMessage, &kPublicKey,
                                  &kExpConstants, &result));

  CHECK(result == kHardenedBoolTrue);

  return kErrorOk;
}

const test_config_t kTestConfig;

bool test_main(void) {
  rom_error_t result = kErrorOk;

  entropy_testutils_boot_mode_init();

  EXECUTE_TEST(result, precomp_test);

  EXECUTE_TEST(result, verify_test);

  return result == kErrorOk;
}
