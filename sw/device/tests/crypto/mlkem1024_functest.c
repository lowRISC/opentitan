// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/crypto/drivers/kmac.h"
#include "sw/device/lib/crypto/impl/mlkem/mlkem.h"
#include "sw/device/lib/crypto/include/config.h"
#include "sw/device/lib/crypto/include/datatypes.h"
#include "sw/device/lib/crypto/include/integrity.h"
#include "sw/device/lib/crypto/include/mlkem.h"
#include "sw/device/lib/testing/entropy_testutils.h"
#include "sw/device/lib/testing/test_framework/check.h"
#include "sw/device/lib/testing/test_framework/ottf_alerts.h"
#include "sw/device/lib/testing/test_framework/ottf_main.h"

#include "hw/top_earlgrey/sw/autogen/top_earlgrey.h"

// Sample test vectors for ML-KEM-1024
static const uint32_t kSeedD[kMlkem1024SharedSecretWords] = {
    0xe875b87e, 0x096026e7, 0x567962a1, 0xc6888e31,
    0x3a8606b5, 0xd80bb2b0, 0xfa06a7f3, 0x3dc090f0,
};

static const uint32_t kSeedZ[kMlkem1024SharedSecretWords] = {
    0xb917e4ea, 0x75a2b70a, 0x10e9dd89, 0xb02b7ee5,
    0x2abf65f7, 0x78295e0c, 0x43bcd235, 0x79c81cdd,
};

static const uint32_t kRandomM[kMlkem1024SharedSecretWords] = {
    0x01234567, 0x89abcdef, 0x11223344, 0x55667788,
    0x99aabbcc, 0xddeeff00, 0x10203040, 0x50607080,
};

static status_t run_mlkem1024_functest(void) {
  // Blinded seed d (64 bytes: 32 bytes share0 + 32 bytes share1)
  uint32_t d_blob[64 / sizeof(uint32_t)] = {0};
  memcpy(d_blob, kSeedD, sizeof(kSeedD));

  otcrypto_blinded_key_t d = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModePqcMlkem1024,
              .key_length = 64,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = 64,
      .keyblob = d_blob,
  };
  d.checksum = otcrypto_integrity_blinded_checksum(&d);

  otcrypto_const_word32_buf_t z = {
      .data = kSeedZ,
      .len = kMlkem1024SharedSecretWords,
  };

  uint32_t pk_data[kMlkem1024PublicKeyWords];
  otcrypto_unblinded_key_t pk = {
      .key_mode = kOtcryptoKeyModePqcMlkem1024,
      .key_length = kMlkem1024PublicKeyBytes,
      .key = pk_data,
  };

  uint32_t sk_data[kMlkem1024SecretKeyWords];
  otcrypto_blinded_key_t sk = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModePqcMlkem1024,
              .key_length = kMlkem1024SecretKeyBytes / 2,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kMlkem1024SecretKeyBytes,
      .keyblob = sk_data,
  };
  sk.checksum = otcrypto_integrity_blinded_checksum(&sk);

  CHECK_STATUS_OK(mlkem1024_det_keygen_internal_start(&d, &z));

  CHECK_STATUS_OK(mlkem1024_keygen_internal_finalize(&pk, &sk));

  // Encapsulation
  otcrypto_const_word32_buf_t m = {
      .data = kRandomM,
      .len = kMlkem1024SharedSecretWords,
  };

  uint32_t ct_data[kMlkem1024CiphertextWords];
  otcrypto_word32_buf_t ct = {
      .data = ct_data,
      .len = kMlkem1024CiphertextWords,
  };

  uint32_t ss1_data[kMlkem1024SharedSecretWords];
  otcrypto_blinded_key_t ss1 = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModePqcMlkem1024,
              .key_length = kMlkem1024SharedSecretBytes / 2,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kMlkem1024SharedSecretBytes,
      .keyblob = ss1_data,
  };
  ss1.checksum = otcrypto_integrity_blinded_checksum(&ss1);

  CHECK_STATUS_OK(otcrypto_mlkem1024_encaps(&pk, &m, &ct, &ss1));

  // Decapsulation
  uint32_t ss2_data[kMlkem1024SharedSecretWords];
  otcrypto_blinded_key_t ss2 = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModePqcMlkem1024,
              .key_length = kMlkem1024SharedSecretBytes / 2,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kMlkem1024SharedSecretBytes,
      .keyblob = ss2_data,
  };
  ss2.checksum = otcrypto_integrity_blinded_checksum(&ss2);

  otcrypto_const_word32_buf_t ct_const = {
      .data = ct_data,
      .len = kMlkem1024CiphertextWords,
  };

  CHECK_STATUS_OK(otcrypto_mlkem1024_decaps(&sk, &ct_const, &ss2));

  CHECK_ARRAYS_EQ(ss1_data, ss2_data, kMlkem1024SharedSecretWords);

  return OTCRYPTO_OK;
}

// FIPS 203 / NIST ACVP Test Vector for ML-KEM-1024 (EncapDecap tgId=3,
// tcId=51).
enum {
  kPkTWords = 1536 / sizeof(uint32_t),
  kPkRhoWords = 32 / sizeof(uint32_t),
  kSkSWords = 1536 / sizeof(uint32_t),
  kSkHpkWords = 32 / sizeof(uint32_t),
  kSkZWords = 32 / sizeof(uint32_t),
  kCtUWords = 1408 / sizeof(uint32_t),
  kCtVWords = 160 / sizeof(uint32_t),
};

static const uint32_t kAcvpPkRho[8] = {
    0xc8e7a24f, 0xb80f15ec, 0x801ddbc7, 0xac25080c,
    0xe25b9118, 0xb8719752, 0xe6450939, 0x24f365da,
};
static const uint32_t kAcvpPkT[384] = {
    0x770e69f6, 0xa0471a25, 0xae3c6f12, 0x73882b22, 0x66c90eeb, 0x8fb0a79a,
    0x72aa5448, 0x491673c0, 0xa8ea60ce, 0xb89881b0, 0x23582171, 0xca83be8d,
    0x1464d7ef, 0x131ace34, 0x0a90f646, 0x4605c153, 0x901e4f2b, 0x7604689e,
    0x8f8e0c00, 0x9aff3df4, 0x5766f3c7, 0x622285bf, 0x8ce683d3, 0x4b76c8a2,
    0x23154459, 0xa7b509f0, 0x91842752, 0x9291f8db, 0xc82bb9fa, 0x5bfcdd73,
    0x919fb45f, 0xd29b7660, 0x27418428, 0x94a4dbfd, 0x58e91c9a, 0x8813fcb6,
    0xd9cae6de, 0x7b2849f5, 0x30850c7e, 0xc16a630d, 0x081f8ca6, 0xce00af60,
    0x3d3e9650, 0x51f600b2, 0x25447c14, 0x7f4662df, 0x3bbdbfb4, 0x7a33da89,
    0x404444a7, 0x73faa39b, 0x5414cdb8, 0x30c7e7f7, 0x43892f35, 0x759ce787,
    0xc177c047, 0x28329694, 0x40d5d317, 0x2f9296e4, 0x5b236310, 0xba66ea78,
    0x798e9123, 0x96775211, 0x0a76675e, 0x5391fc2f, 0x7555a80a, 0x44c34d47,
    0xfc3011f1, 0x03ecce77, 0x7f93f4ad, 0x38c8fbd7, 0x82f85bc0, 0x3b90a963,
    0xb61807a1, 0x04973ec4, 0x7a820279, 0xa8bf1a49, 0x198037d8, 0x89fc961c,
    0xa37f8124, 0x765c62ab, 0x34ea2c13, 0x743d3b27, 0x11919e58, 0x9c981642,
    0xb4c5988e, 0xa05a2eec, 0x59bb0518, 0x7e13b78c, 0x0769cb61, 0xba512a95,
    0x9e2ec554, 0x0593628c, 0x792798b7, 0x439dccd0, 0x42254ce1, 0x4e12a577,
    0xf77c2506, 0x18fc1ea6, 0x08a81861, 0xfca04bce, 0x55341bd3, 0x3b64779d,
    0x17d00be9, 0x230cc9b5, 0x12b61556, 0x2e43d658, 0x908a13e6, 0x38dab3a0,
    0x01c2c8b6, 0x014c6457, 0x32bc6b0b, 0x15b5c47a, 0x465cade2, 0x08ba63ad,
    0x646b9471, 0x4403a355, 0xcba16286, 0x461abacc, 0xeab78923, 0xa4d4af4a,
    0x5da4e211, 0xe46f1492, 0xc8948050, 0x7e74f2e4, 0x572e8a91, 0x4a934c87,
    0x134f655c, 0x70c69576, 0x50eca384, 0x77c7e7f3, 0xc0aa42dc, 0x012797aa,
    0xe3ca4655, 0x0485c676, 0xaea899aa, 0xe62b5c58, 0x01514ee8, 0x91eab524,
    0xbe56c369, 0x8ccd3902, 0x32a90d90, 0x356c7103, 0x02b8ba57, 0x19c346c8,
    0xebb2b748, 0xe02d4e06, 0x83ca9f1e, 0xe486497d, 0xd39b013a, 0x21e5dc51,
    0x6a38c18f, 0x234f6846, 0x99eaf647, 0x6a58079c, 0xa1a46de6, 0x363cfe29,
    0x075b43e1, 0x4755b115, 0x8e760070, 0x617c87f7, 0xd9cc7985, 0x43f7dc58,
    0x65c0e923, 0x1b0f4fa0, 0x1be4ac23, 0xdf69aa0f, 0xc6a23ed5, 0xb067f42a,
    0x0e8064df, 0x72fec479, 0xab589941, 0x5002471d, 0x912a12b5, 0x440ab05e,
    0xc85d54f4, 0x94a0783b, 0x1db70227, 0x5e113993, 0x96ab7f00, 0x8038fb84,
    0x2172e9b0, 0x4c7d86d5, 0x1f92a4b0, 0xa9819aa2, 0x2c1f2339, 0x29d3c51c,
    0xc3522065, 0x31024648, 0xbc2a796b, 0xe13650d5, 0xe7de1ff4, 0x1612ba02,
    0x8f9171ab, 0xec039546, 0x1a32e985, 0x7b28d4b8, 0x451937d5, 0x40f1e160,
    0xd10039fe, 0x8b584f86, 0x8d64ac4a, 0x28614716, 0xec11cd37, 0x6807736b,
    0xd8968a52, 0x0306bd25, 0xb034473a, 0xf2a62a4b, 0x45a38665, 0x78595e60,
    0x3867041f, 0x564717c5, 0x39b18341, 0x41b972e7, 0x64ebb394, 0x2d467c40,
    0xcf144cc5, 0x30ab1bc8, 0x9591901f, 0xbf975a0b, 0x0c9936f8, 0xb19a410a,
    0x8d8af0c8, 0xb9a30a20, 0x2492a168, 0x0c143be0, 0xb8588a99, 0x25cc2162,
    0x0d7f408c, 0x892a75da, 0x5d42580d, 0xcbb46962, 0xa32d0503, 0xb0ecd01c,
    0x2da4364b, 0xf9eda130, 0x1ca37085, 0xc91ea8ea, 0xc06d2f38, 0x2837f612,
    0x83598af3, 0xc6f70db5, 0x4f939154, 0xdd9cbb2c, 0xc0844271, 0x9bf76f70,
    0xb679f8b1, 0x713c42ea, 0x0afa8b19, 0x698462fb, 0x796f0ebb, 0x3f4674c1,
    0x4abaa6dd, 0xec86a878, 0x63da0f69, 0x6cb693cd, 0x43381eb0, 0x8102fe95,
    0x56b5dca7, 0xaadfb261, 0x19cc9079, 0xcc6bb9be, 0x300f7429, 0x22c7f35f,
    0x1f99a581, 0x5b13393b, 0xc1896306, 0xa2b0b7da, 0xe7eebbba, 0x399bd96b,
    0x8ea2824c, 0x435627bb, 0x21e488c2, 0xab94fcbf, 0x19d57d31, 0x52e92012,
    0x0c674975, 0x264daa67, 0xa16a8ace, 0x019662c8, 0xfb351b63, 0xc181b89f,
    0x68ca03ff, 0x914dbec2, 0x4b276932, 0x05836604, 0x12e7aca6, 0x1dc55496,
    0xa98ec7c9, 0x92487bb0, 0xc8e4a041, 0x85b2d53f, 0x4aab137a, 0x9213d7a9,
    0xe208ac02, 0xd0247687, 0x699cee7a, 0x0b7edc54, 0x60f293a6, 0x0cb814b7,
    0x11b4f692, 0x27e610d5, 0x1d456160, 0xd54ae599, 0x3b995459, 0xb3fa2496,
    0xffb0eb1d, 0xfa100b70, 0x52397c3d, 0xf48280e4, 0x70db7dd8, 0x65cb553e,
    0xa3507457, 0x4466c575, 0xb8641350, 0xdf6d7671, 0xa1ef7ce5, 0xa35c7487,
    0x9078f8b6, 0xb865acc2, 0xaeb9db9d, 0x9b0ff97a, 0x0453a3aa, 0xa482d33c,
    0x44579c08, 0xd7781ed1, 0x1fd0611a, 0x5c5c344c, 0x5c389baa, 0x725af37a,
    0x7b675c54, 0x123b36cb, 0x0392039a, 0x4f065639, 0xf4cf99c1, 0x3ad0afba,
    0x5bc61334, 0x86c15f02, 0xae905647, 0xb69d6993, 0x281bb7d0, 0x2096ba5a,
    0x6899141d, 0x86134657, 0xcf26fa5c, 0x49c2e7ea, 0xb15f5dfa, 0x52a78084,
    0x1a6868c3, 0xe2ae6959, 0xacf0a10d, 0x858162ce, 0x2b864124, 0xa1014c1b,
    0x112235c0, 0xa40492d4, 0x2cf70167, 0x4c7e2852, 0x86fd8f8a, 0x7322e068,
    0x1e4be829, 0x41478d0a, 0x4af44a8a, 0xa4cb806e, 0x4ca0a470, 0x6a151718,
    0x70abf487, 0xb39a3855, 0x6cec1db5, 0xd7b84cd6, 0x4b2d0b89, 0xb24a5eb8,
    0xa6acc30a, 0x00012b76, 0x04920f64, 0x0639e70b, 0x03818ee6, 0x536976a5,
    0x2f312021, 0x47dd0de5, 0x15190bac, 0x7b13d61f, 0x2493a016, 0xb8298694,
};
static const uint32_t kAcvpM[8] = {
    0xf63c23bf, 0x58411d12, 0xeaf04a5b, 0xf75db374,
    0x57bb52ed, 0x827a1082, 0xec4acd59, 0x617e58c3,
};
static const uint32_t kAcvpCtU[352] = {
    0x7e7fdbef, 0x192a3056, 0x9ce77b9a, 0x675f7100, 0xc024500a, 0xfd7b35fd,
    0x934a6b44, 0x5a9c0771, 0x5f4f9604, 0xb38f0c4d, 0xf6d12ad1, 0x267d00f2,
    0x9dc498f6, 0x103b1ea9, 0xc732237d, 0xd7f32d61, 0x4ffe16a2, 0x8aadc507,
    0xe82d9e1e, 0xb7d33e0e, 0xe5a3db9b, 0xa4bd8f38, 0x40791f31, 0x93d19817,
    0x69172b08, 0x8632fe2b, 0x5f2c44ca, 0x32634d7d, 0x7b0df47c, 0x8400420c,
    0x83a236c6, 0xa48334e8, 0xe688cf69, 0xf89c1269, 0xf813f068, 0x6ad76f79,
    0x75ed74e4, 0xbf3288af, 0xa458360a, 0x2ffdb3ed, 0x45a4dc37, 0x2887c786,
    0xe5264283, 0x2a73d1de, 0xc0d13e2b, 0x25a8f4db, 0x4c348c81, 0xdbd460fd,
    0x5b2e0e46, 0x5031192b, 0x092cd20d, 0x405ff48c, 0x04cb737d, 0x66a83ce8,
    0x4a240c09, 0x1386d011, 0x064b17ba, 0x3386c5f7, 0x9b6201bc, 0x691af4e2,
    0xd29a8f5e, 0xab2b9ce0, 0xac4ad34e, 0x583b30a0, 0x5de5b3f3, 0x4ba8f416,
    0xd7c6cd4b, 0x7001c2c4, 0xfdd00ddb, 0xfcb7f420, 0x8cdfe6f8, 0x0775bb7b,
    0xa12bea5e, 0x71c0af0e, 0xb2f43da8, 0xd3ad1c40, 0x9c72fb28, 0x1c1c07c5,
    0xccea9d86, 0x608bcd3f, 0x1c7b15fb, 0xd3914442, 0xe8df36ab, 0xdaf35cd1,
    0x09a114de, 0x57d114a0, 0x1f1fe9ca, 0xaf9cee7f, 0x2a3f00ac, 0xe4f3a96f,
    0x990296c6, 0xc1df1bc7, 0x7d0a7768, 0x21f54f03, 0xa09c5920, 0xe96e8805,
    0x5af1d47f, 0x09a22bf4, 0x936a2a05, 0xcddc9c06, 0x1580a391, 0xbce70c6a,
    0xd35138a7, 0x1c6c917b, 0x5aa4f593, 0x4df48db4, 0xb2d6b1d2, 0x70de913c,
    0x97c380f4, 0x8b5ac0b4, 0xd499e193, 0xe57b24ef, 0x03edfc33, 0xd320efcc,
    0x31fee213, 0xf4e46739, 0x778165de, 0x94c6d410, 0x956af07f, 0x12777708,
    0x8769c6f4, 0xa5cb3b88, 0x88c50975, 0x3a1ca7e8, 0xcf707d8c, 0xda45a950,
    0xb142a77b, 0x6875fa6c, 0x047e1256, 0x820eaed0, 0xe79ab3cb, 0x688afbad,
    0x1d81bf8a, 0xea8e9208, 0x35750433, 0x4704ba96, 0xa53c8e1b, 0x8ce930f3,
    0xe69ecdd3, 0x2ba1e9eb, 0x5844589d, 0xc1a5d594, 0x20db6b84, 0x5a5422d3,
    0x2e97c6ce, 0x71f69c82, 0xfc791bb8, 0xc50e140b, 0x1cb90d94, 0xb7469c47,
    0xd87225e9, 0x786470a7, 0x4ee02244, 0xaf753327, 0x2f9875ab, 0x2a094464,
    0x0907c52b, 0x3184dc7b, 0x21f7272c, 0x360cf758, 0x15edfb79, 0x08e89617,
    0x52b12568, 0x197e8587, 0x11590464, 0x44fb3297, 0x965b4169, 0x54a87ddb,
    0x69d2c262, 0xbfc74b17, 0x2d994b4d, 0xa94d6a0b, 0xe72baa2b, 0xacd08af8,
    0xd1bebf06, 0x834f85a5, 0x94f9ba48, 0xb4cb2867, 0xa21fb62b, 0x070fc888,
    0xf969e6cf, 0xc9477761, 0xea35c875, 0x8f4e6c47, 0x5bf688f2, 0xaf502fa8,
    0x40939e0b, 0x41ae0b96, 0xfaa6a6c6, 0x57a10fad, 0x77cba285, 0xe4af67cd,
    0x1d2c9088, 0xab2efbb7, 0x7d65e164, 0x3d5382b2, 0xaacc09c9, 0x50167a26,
    0xa825002e, 0xb65bc4b4, 0x2e26abbf, 0xfc88b367, 0x50095362, 0xff9936d9,
    0xc9218d07, 0x37491b62, 0x58b4aecd, 0x649d9558, 0x3b399f99, 0x04839ee5,
    0x6679a0df, 0x126e9b3b, 0xddf66669, 0xa14ac539, 0x87ddc993, 0x5c4eec85,
    0x298e8513, 0x41ccde14, 0x1a9bc953, 0x1c21b8d8, 0x8535fe1d, 0x6a73f98c,
    0x59b2a54c, 0x52aab1d0, 0x1d18528d, 0x1d0654fe, 0x9f930c96, 0x1eece36b,
    0x9a3bea8b, 0xecb179d5, 0x7fccd413, 0xae6631dc, 0xd4490c37, 0xd44afa5f,
    0x7130db83, 0xe2075086, 0x189507dd, 0x8d73faa2, 0x794dd9cf, 0x7cf56ad3,
    0xc46af22d, 0x797577df, 0xc1b98de1, 0x2200cb07, 0x2b9d24d0, 0x03457bdb,
    0x4a4e37cb, 0x1f06591a, 0xc60ecf05, 0xfac00a02, 0xa8ad6519, 0xb8a5ca50,
    0xffe02298, 0xfa8aac50, 0xe7734b46, 0xe7fd8bcb, 0x455230ca, 0xbbab67e8,
    0x08e4d335, 0x5935646e, 0xcb77b922, 0xcdd0ecda, 0x6a5072f2, 0xd9e1f250,
    0x9cb38d7e, 0x6af74364, 0xb4a07e0d, 0x7ebe9ee1, 0xc45108ef, 0x9fb51457,
    0x14111774, 0x89d5d5d2, 0xd5e446da, 0xc4837bde, 0xb01a5384, 0x786bb7d4,
    0x99cae76c, 0x0fc72fa2, 0x5701a98c, 0xf7cd389e, 0xb4443b44, 0xc970cccc,
    0xe03fec01, 0x784cb634, 0xb52cb1f6, 0x72746e42, 0x2875aa4e, 0xdcccdd9f,
    0x8a993d65, 0xc6c8003a, 0x587bb44c, 0xac0a1314, 0x559fd7ba, 0xf80e4ab1,
    0x4e0d441e, 0xebc8e12f, 0xfa88884d, 0xe29868ec, 0xb445ee3a, 0xe6e5f6b8,
    0xe438bc4c, 0x3470d598, 0xd4f2c3de, 0x46822644, 0x4a62cc35, 0xd7bd494b,
    0xb152bc45, 0x93c151f1, 0x775568ca, 0x394fef8f, 0x6d572ce7, 0x609fdaae,
    0xa12a6841, 0x34f1b2bb, 0xdd288021, 0x9a5882fc, 0xaba97921, 0x13f6ec70,
    0xe0a63e59, 0x3de8474a, 0x573582d8, 0x6c201086, 0x594103f6, 0x025376f3,
    0xfa61a466, 0x63639af8, 0xa26e9f26, 0x06a4f966, 0xb2f352e8, 0x361d1f08,
    0xd241cab6, 0x644c0cdc, 0xae63424e, 0x0879ee36, 0x0027351b, 0xa7c7d1a2,
    0xa24bdcba, 0x1c279142, 0x023aadf4, 0x259d78a8, 0x379e6fe1, 0x1df6e255,
    0x798d019f, 0xe5f2c7d4, 0x730e64fd, 0x5355e08c, 0x65ffdc5f, 0x03e72f1b,
    0x19861644, 0xf5b1bdbf, 0x2f22f0ac, 0x0d0789d6,
};
static const uint32_t kAcvpCtV[40] = {
    0xc158d70a, 0x2151481d, 0xd0d2c0ec, 0xfd911d4b, 0x311f8bbe, 0xec1c995f,
    0xeed05c0e, 0xbbb06530, 0x6727963d, 0x4c4d7d7a, 0xe739d5a0, 0x2d6b2d55,
    0x8e8d7589, 0xe4afa9c4, 0x96d81f1c, 0x712f91d4, 0x9fe4a5cb, 0xea180155,
    0x49670cbd, 0x422f167c, 0x6a4a2c05, 0x2a9e00a4, 0x4a5d0c21, 0x5d16e23a,
    0x72504dc4, 0xc5543312, 0x570ec842, 0xc5fe6bf8, 0x1c180055, 0x187d057e,
    0x5e7a0484, 0x54a91568, 0xd62b645b, 0x65a4c531, 0x2507a579, 0xc1fefa3f,
    0x1d388185, 0x1d49fe50, 0xb41a9a31, 0x8996d1a0,
};
static const uint32_t kAcvpSs[8] = {
    0xedeff2bc, 0x5cc3451e, 0x70e1af5f, 0xf5f4c3aa,
    0x2211efb3, 0xa2b9a60e, 0x0eb9f054, 0x946bd5e8,
};
static const uint32_t kAcvpSkS[384] = {
    0x1332e7f9, 0xe05ca5f4, 0xb40b634f, 0x1e682220, 0x73e059a5, 0x92003513,
    0x34134652, 0x37c3651a, 0x03996c3a, 0x1fcc14da, 0x5116c780, 0x44a55ec2,
    0x7c724759, 0x02cd26d9, 0x3cd95e53, 0x95c787b1, 0x06f96bc5, 0xbc868d4e,
    0x5b1c8125, 0x952eb862, 0x1f6cbf7b, 0x1b6561ed, 0x378a67c5, 0x29d9ac1c,
    0xf504b006, 0x735c88e8, 0xb658ed7b, 0x6d5557ea, 0xaa700658, 0x39322240,
    0x7538c6b3, 0x31e439f1, 0x4b46153f, 0x468883b5, 0x07ed0e09, 0x30395a32,
    0xf93f4be8, 0x414b06e0, 0xc7821793, 0x1d12a05b, 0x61275c76, 0x12d5d7cc,
    0x5fbba78f, 0x096d5974, 0x84b0af16, 0xe185d957, 0x0065ce18, 0x80ac96b0,
    0xa86762a6, 0x60679c25, 0xc965c481, 0x6a6d05cd, 0xa05bbac5, 0x6f780b5c,
    0x21bda7aa, 0x100ab92a, 0x4bfa103e, 0x193edae7, 0xa57123b6, 0x6ea4fa06,
    0x71821650, 0xf8c69c95, 0xa819c0bd, 0xad33d9d2, 0x39febf74, 0x7d039908,
    0xcf74ab35, 0x2ca25b8b, 0x788aa210, 0x201cd131, 0xe92cae2a, 0x30d95113,
    0xea08d66a, 0x36200ec6, 0x3436363c, 0xf6b5f182, 0x77856698, 0xc8cc588c,
    0xca48724e, 0x37da3140, 0xaec644a0, 0x431f5874, 0xe4aa0a95, 0x0164764b,
    0xef113178, 0x9aab4335, 0x03ea62ac, 0xea8b288c, 0x750d10d3, 0xc265ec6a,
    0xbcce7762, 0x76822a60, 0x6cb2ed94, 0x3680a254, 0x2a0b9a85, 0x71cc9552,
    0xec478bd5, 0x04b11cca, 0x9c157a99, 0x0f6963f9, 0xc8000395, 0x113529cd,
    0x35b11472, 0x0a72580a, 0x7b82acb4, 0x324b0519, 0xbbe38d39, 0x13dc6fc7,
    0xe7773a31, 0x0c4d7b12, 0x089c7da0, 0xa622537f, 0x55230f7b, 0x20e0d1a5,
    0x1f5f79b3, 0xf9232b09, 0x262aa729, 0xa4c871df, 0x321e8256, 0xbf76e2b7,
    0x0aa9baf8, 0x505a3166, 0x72948011, 0x4e5349bf, 0x47685474, 0xc980fb61,
    0xbdcea385, 0x01c85fa9, 0xbba286bb, 0x438ad624, 0xe342a3d4, 0x2ad5d516,
    0x737938be, 0x81106cbc, 0x42c2068f, 0x9351b4c8, 0xc8d02f29, 0x22827858,
    0x65a93522, 0x2cfb113a, 0xc6e83796, 0xa68f8133, 0x74f02ae1, 0x81240152,
    0x50541095, 0x860aba7a, 0x4789cb96, 0xa26a76b6, 0x9a0f1811, 0x60944367,
    0x0854e2b0, 0x97d56e6b, 0xce47db92, 0x61ace4fe, 0xf6cf8045, 0x09034a0f,
    0x37c04c49, 0xb02e5381, 0x154603c6, 0x5644f573, 0xd2e82e53, 0x67c32f83,
    0x0c42a86b, 0x40211d70, 0x1f3739b8, 0x670c30b1, 0x53adb5dc, 0x9dd05b01,
    0xa83d5c1f, 0x360dc0c8, 0x673776b1, 0xbd39fba0, 0x5cc93162, 0x6a568b86,
    0x428cb2dd, 0xd54b9071, 0x9bc59d0c, 0x0c59394d, 0xea85b644, 0xa8307424,
    0xa616a45a, 0x256d15f1, 0x709b5d7e, 0x9359b47c, 0x484bcf57, 0xbce90e6a,
    0xa69325bf, 0x249bac68, 0x72963078, 0x60632a52, 0x049d6268, 0x5d0292af,
    0xc869f2cf, 0xfa5a4302, 0x4661c789, 0xea50e9ea, 0x29ca76d4, 0x36143632,
    0xf97132c8, 0x9b980b30, 0xaa869696, 0xda0876fa, 0xfab25a3c, 0x3302f10c,
    0x2619a6e4, 0xf1f68cd2, 0xa3b3b1c4, 0x4c5bd604, 0xa131caa0, 0x91c1a9b3,
    0xd8767586, 0xead651ca, 0x9b65595e, 0xcdc711a1, 0x0be62c73, 0xad8bc86f,
    0x3468186b, 0xbb043a79, 0x26a9d0b4, 0x523d2020, 0x2a537a05, 0x4e07245e,
    0x003d66d3, 0xf8ce2b7b, 0x1f360cbb, 0x8669a5ea, 0x735a3693, 0x7e4ab5c8,
    0x03c2e24a, 0x762103b4, 0x722077a8, 0xfa67bc61, 0xd5784913, 0xad127e13,
    0x026cc6d0, 0xa45c2dca, 0x61935da4, 0x64a60b9d, 0xd7237483, 0x76e13b4c,
    0x72bbe34d, 0x63f46d67, 0x5d859aa6, 0x29cc570b, 0x5bb76540, 0x066a914f,
    0x5b4cb5af, 0xf538b5c8, 0xb6a342a1, 0xaa378a7c, 0x6a2266f5, 0xac041d38,
    0xc398f6f7, 0xc92178db, 0x09465f91, 0x354fb9da, 0x60b91e6b, 0x97fa8728,
    0x56959c96, 0xb8ff0137, 0x56010b69, 0x246c400b, 0x73744108, 0x02a2a48e,
    0x7f3d9606, 0xd912a484, 0x304c24cc, 0x7b276198, 0x513d52e7, 0xb8693393,
    0xf16adb83, 0x215f39a9, 0x30e45736, 0x3a215c5b, 0x3b0cbf5a, 0x4f91db8f,
    0x0414056a, 0x57cc0602, 0x42347620, 0x6e6c6b66, 0xca7450eb, 0x88b2a360,
    0xa2b7c95d, 0x86be35b6, 0x4045a19a, 0x549e2551, 0xbbd8cb4b, 0x02a2503a,
    0xda0b91a3, 0x66233302, 0x7f53f0a4, 0x7fb6c96b, 0xa30e36ec, 0x36d9c508,
    0x0a50068c, 0x5a184138, 0x6fbb4129, 0x2b5d503e, 0x222d384a, 0xc519ff69,
    0x1b236bec, 0x69f57144, 0x818c4664, 0xc484852b, 0x5af2cba8, 0x7307054c,
    0x491d0155, 0x25f6b406, 0x77414092, 0xd25020a9, 0x53d9419c, 0x4b6b62a3,
    0x4a3c80d8, 0x05f04905, 0x8e43f9ad, 0x6e7eb141, 0x186d3aac, 0xbdbc8928,
    0x854d7a5e, 0xf750b4cb, 0x652b0d0c, 0x1d2f8b92, 0x13b92366, 0x0e506e6a,
    0x4372371b, 0x45ca3102, 0xafb46e39, 0xe58bebe7, 0xd97c73d8, 0x1ce19466,
    0xb8b30af1, 0x878dba94, 0x5f277c75, 0xea5cabae, 0xb52f68c5, 0x31d36e49,
    0x7c355784, 0x3a42425a, 0x679045a3, 0x979f0740, 0x525cc1c5, 0x5bc1aa9f,
    0xa004c951, 0x3b979ad0, 0x773c0e2c, 0xf78e01c8, 0x021b6f95, 0x18fbfcb7,
    0xe4b94c7b, 0xe1f0b629, 0x5a0538a2, 0x895a82b6, 0x817616ec, 0xcd87919d,
    0x71227294, 0x907aa6ec, 0x8389fda0, 0x0611c08f, 0x808b923b, 0x859a7d78,
    0x0c73f6c2, 0xbb429910, 0x802cb248, 0x53ca7324, 0x16a31947, 0x3bd399b4,
    0x4d0cbd00, 0xf2f98469, 0xc0558dce, 0x6fcdf77b, 0x49d31311, 0x51a36d3b,
    0xc9b43628, 0x8615c88b, 0x56166744, 0x849f758e, 0x12170763, 0x32513b0b,
    0x311f7704, 0x9c412550, 0x2ed0f3a4, 0xf5bc845f, 0x2c9f6866, 0xb4894a55,
};
static const uint32_t kAcvpSkHpk[8] = {
    0x05cb9e95, 0x9bb75722, 0x5a533fa3, 0xc19334bf,
    0x92457ddf, 0x9febf23f, 0xedbc500d, 0xc28ca3b4,
};
static const uint32_t kAcvpSkZ[8] = {
    0xd8ae4893, 0x4c27b28f, 0x0267962b, 0xb0102e7d,
    0x7365a9b1, 0xbcdb18bc, 0x008a5106, 0x691476c9,
};

static status_t run_mlkem1024_testvector_encaps_test(void) {
  uint32_t pk_data[kMlkem1024PublicKeyWords];
  memcpy(pk_data, kAcvpPkT, sizeof(kAcvpPkT));
  memcpy(pk_data + kPkTWords, kAcvpPkRho, sizeof(kAcvpPkRho));

  otcrypto_unblinded_key_t pk = {
      .key_mode = kOtcryptoKeyModePqcMlkem1024,
      .key_length = kMlkem1024PublicKeyBytes,
      .key = pk_data,
  };

  otcrypto_const_word32_buf_t m = {
      .data = kAcvpM,
      .len = kMlkem1024SharedSecretWords,
  };

  uint32_t ct_data[kMlkem1024CiphertextWords];
  otcrypto_word32_buf_t ct = {
      .data = ct_data,
      .len = kMlkem1024CiphertextWords,
  };

  uint32_t ss_data[kMlkem1024SharedSecretWords];
  otcrypto_blinded_key_t ss = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModePqcMlkem1024,
              .key_length = kMlkem1024SharedSecretBytes / 2,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kMlkem1024SharedSecretBytes,
      .keyblob = ss_data,
  };
  ss.checksum = otcrypto_integrity_blinded_checksum(&ss);

  HARDENED_TRY(otcrypto_mlkem1024_encaps(&pk, &m, &ct, &ss));

  // Verify ciphertext
  uint32_t expected_ct[kMlkem1024CiphertextWords];
  memcpy(expected_ct, kAcvpCtU, sizeof(kAcvpCtU));
  memcpy(expected_ct + kCtUWords, kAcvpCtV, sizeof(kAcvpCtV));
  CHECK_ARRAYS_EQ(ct_data, expected_ct, kMlkem1024CiphertextWords);

  // Verify shared secret
  CHECK_ARRAYS_EQ(ss_data, kAcvpSs, kMlkem1024SharedSecretWords);
  return OTCRYPTO_OK;
}

static status_t run_mlkem1024_testvector_decaps_test(void) {
  uint32_t sk_data[kMlkem1024SecretKeyWords];
  memcpy(sk_data, kAcvpSkS, sizeof(kAcvpSkS));
  memcpy(sk_data + kSkSWords, kAcvpPkT, sizeof(kAcvpPkT));
  memcpy(sk_data + kSkSWords + kPkTWords, kAcvpPkRho, sizeof(kAcvpPkRho));
  memcpy(sk_data + kSkSWords + kPkTWords + kPkRhoWords, kAcvpSkHpk,
         sizeof(kAcvpSkHpk));
  memcpy(sk_data + kSkSWords + kPkTWords + kPkRhoWords + kSkHpkWords, kAcvpSkZ,
         sizeof(kAcvpSkZ));

  otcrypto_blinded_key_t sk = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModePqcMlkem1024,
              .key_length = kMlkem1024SecretKeyBytes / 2,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kMlkem1024SecretKeyBytes,
      .keyblob = sk_data,
  };
  sk.checksum = otcrypto_integrity_blinded_checksum(&sk);

  uint32_t ct_data[kMlkem1024CiphertextWords];
  memcpy(ct_data, kAcvpCtU, sizeof(kAcvpCtU));
  memcpy(ct_data + kCtUWords, kAcvpCtV, sizeof(kAcvpCtV));

  otcrypto_const_word32_buf_t ct = {
      .data = ct_data,
      .len = kMlkem1024CiphertextWords,
  };

  uint32_t ss_data[kMlkem1024SharedSecretWords];
  otcrypto_blinded_key_t ss = {
      .config =
          {
              .version = kOtcryptoLibVersion1,
              .key_mode = kOtcryptoKeyModePqcMlkem1024,
              .key_length = kMlkem1024SharedSecretBytes / 2,
              .hw_backed = kHardenedBoolFalse,
              .security_level = kOtcryptoKeySecurityLevelLow,
          },
      .keyblob_length = kMlkem1024SharedSecretBytes,
      .keyblob = ss_data,
  };
  ss.checksum = otcrypto_integrity_blinded_checksum(&ss);

  HARDENED_TRY(otcrypto_mlkem1024_decaps(&sk, &ct, &ss));

  // Verify shared secret
  CHECK_ARRAYS_EQ(ss_data, kAcvpSs, kMlkem1024SharedSecretWords);
  return OTCRYPTO_OK;
}

OTTF_DEFINE_TEST_CONFIG();

bool test_main(void) {
  CHECK_STATUS_OK(entropy_testutils_auto_mode_init());
  CHECK_STATUS_OK(kmac_hwip_default_configure());

  CHECK_STATUS_OK(otcrypto_init(kOtcryptoKeySecurityLevelLow));

  LOG_INFO("Running ML-KEM-1024 Encaps-Decaps Test");
  status_t result = run_mlkem1024_functest();
  if (!status_ok(result)) {
    return false;
  }

  LOG_INFO("Running ML-KEM-1024 Encapsulation Test");
  result = run_mlkem1024_testvector_encaps_test();
  if (!status_ok(result)) {
    return false;
  }

  LOG_INFO("Running ML-KEM-1024 Decapsulation Test");
  result = run_mlkem1024_testvector_decaps_test();
  if (!status_ok(result)) {
    return false;
  }

  return true;
}
