// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca/sha2_otbn_sca.h"

#include "sw/device/lib/base/memory.h"
#include "sw/device/lib/base/status.h"
#include "sw/device/lib/crypto/drivers/otbn.h"
#include "sw/device/lib/crypto/drivers/rv_core_ibex.h"
#include "sw/device/lib/runtime/log.h"
#include "sw/device/lib/testing/test_framework/ujson_ottf.h"
#include "sw/device/lib/ujson/ujson.h"
#include "sw/device/sca/lib/prng.h"
#include "sw/device/tests/penetrationtests/firmware/lib/pentest_lib.h"
#include "sw/device/tests/penetrationtests/json/otbn_sca_commands.h"

enum {
  kSha256StateWords = 8,
  kSha256BlockBytes = 64,
  kSha256BlockWords = 16,
  kSha512StateWords = 16,
  kSha512BlockBytes = 128,
  kSha512BlockWords = 32,
  kSha384DigestWords = 12,
  kSha512DigestWords = 16,
  kSha2ScaMaxBatchSize = 200,
};

const uint8_t *otbn_sca_loaded_app_imem = NULL;

static status_t otbn_sca_load_app_cached(const otbn_app_t app) {
  if (otbn_sca_loaded_app_imem != app.imem_compressed_start) {
    TRY(otbn_load_app(app));
    otbn_sca_loaded_app_imem = app.imem_compressed_start;
  }
  return OK_STATUS();
}

static const uint32_t kSha256InitialState[kSha256StateWords] = {
    0x5be0cd19, 0x1f83d9ab, 0x9b05688c, 0x510e527f,
    0xa54ff53a, 0x3c6ef372, 0xbb67ae85, 0x6a09e667,
};

static const uint32_t kSha384InitialState[kSha512StateWords] = {
    0xbefa4fa4, 0x47b5481d, 0x64f98fa7, 0xdb0c2e0d, 0x68581511, 0x8eb44a87,
    0xffc00b31, 0x67332667, 0xf70e5939, 0x152fecd8, 0x3070dd17, 0x9159015a,
    0x367cd507, 0x629a292a, 0xc1059ed8, 0xcbbb9d5d,
};

static const uint32_t kSha512InitialState[kSha512StateWords] = {
    0x137e2179, 0x5be0cd19, 0xfb41bd6b, 0x1f83d9ab, 0x2b3e6c1f, 0x9b05688c,
    0xade682d1, 0x510e527f, 0x5f1d36f1, 0xa54ff53a, 0xfe94f82b, 0x3c6ef372,
    0x84caa73b, 0xbb67ae85, 0xf3bcc908, 0x6a09e667,
};

OTBN_DECLARE_APP_SYMBOLS(run_sha256);
OTBN_DECLARE_SYMBOL_ADDR(run_sha256, state_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_sha256, state_s1);
OTBN_DECLARE_SYMBOL_ADDR(run_sha256, msg_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_sha256, msg_s1);
OTBN_DECLARE_SYMBOL_ADDR(run_sha256, num_msg_chunks);

OTBN_DECLARE_APP_SYMBOLS(run_sha384);
OTBN_DECLARE_SYMBOL_ADDR(run_sha384, state_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_sha384, state_s1);
OTBN_DECLARE_SYMBOL_ADDR(run_sha384, msg_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_sha384, msg_s1);
OTBN_DECLARE_SYMBOL_ADDR(run_sha384, n_chunks);

OTBN_DECLARE_APP_SYMBOLS(run_sha512);
OTBN_DECLARE_SYMBOL_ADDR(run_sha512, state_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_sha512, state_s1);
OTBN_DECLARE_SYMBOL_ADDR(run_sha512, msg_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_sha512, msg_s1);
OTBN_DECLARE_SYMBOL_ADDR(run_sha512, n_chunks);

static uint8_t sha2_batch_msgs[kSha2ScaMaxBatchSize]
                              [OTBNSCA_CMD_MAX_SHA2_MSG_BYTES];

static status_t sha256_otbn_sca_run(const uint8_t *msg, size_t msg_len,
                                    bool en_masks, uint8_t *digest_out) {
  const otbn_app_t kApp = OTBN_APP_T_INIT(run_sha256);
  TRY(otbn_sca_load_app_cached(kApp));

  const otbn_addr_t kAddrStateS0 = OTBN_ADDR_T_INIT(run_sha256, state_s0);
  const otbn_addr_t kAddrStateS1 = OTBN_ADDR_T_INIT(run_sha256, state_s1);
  const otbn_addr_t kAddrMsgS0 = OTBN_ADDR_T_INIT(run_sha256, msg_s0);
  const otbn_addr_t kAddrMsgS1 = OTBN_ADDR_T_INIT(run_sha256, msg_s1);
  const otbn_addr_t kAddrNumChunks =
      OTBN_ADDR_T_INIT(run_sha256, num_msg_chunks);

  uint32_t state_s0[kSha256StateWords];
  uint32_t state_s1[kSha256StateWords];
  for (size_t i = 0; i < kSha256StateWords; ++i) {
    state_s1[i] = en_masks ? ibex_rnd32_read() : 0;
    state_s0[i] = kSha256InitialState[i] ^ state_s1[i];
  }
  TRY(otbn_dmem_write(kSha256StateWords, state_s0, kAddrStateS0));
  TRY(otbn_dmem_write(kSha256StateWords, state_s1, kAddrStateS1));

  uint32_t padded[2 * kSha256BlockWords];
  memset(padded, 0, sizeof(padded));
  if (msg_len > 0) {
    memcpy(padded, msg, msg_len);
  }
  ((uint8_t *)padded)[msg_len] = 0x80;

  uint32_t num_chunks = (msg_len + 1 + 8 > kSha256BlockBytes) ? 2 : 1;
  uint64_t total_bits = ((uint64_t)msg_len) << 3;
  size_t total_words = num_chunks * kSha256BlockWords;
  padded[total_words - 1] =
      __builtin_bswap32((uint32_t)(total_bits & UINT32_MAX));
  padded[total_words - 2] = __builtin_bswap32((uint32_t)(total_bits >> 32));

  uint32_t msg_s0[2 * kSha256BlockWords];
  uint32_t msg_s1[2 * kSha256BlockWords];
  for (size_t i = 0; i < total_words; ++i) {
    msg_s1[i] = en_masks ? ibex_rnd32_read() : 0;
    msg_s0[i] = padded[i] ^ msg_s1[i];
  }
  TRY(otbn_dmem_write(total_words, msg_s0, kAddrMsgS0));
  TRY(otbn_dmem_write(total_words, msg_s1, kAddrMsgS1));
  TRY(otbn_dmem_write(1, &num_chunks, kAddrNumChunks));

  pentest_set_trigger_high();
  asm volatile(NOP30);
  otbn_execute();
  otbn_busy_wait_for_done();
  pentest_set_trigger_low();

  TRY(otbn_dmem_read(kSha256StateWords, kAddrStateS0, state_s0));
  TRY(otbn_dmem_read(kSha256StateWords, kAddrStateS1, state_s1));

  uint32_t digest_words[kSha256StateWords];
  for (size_t i = 0; i < kSha256StateWords; ++i) {
    uint32_t h = state_s0[kSha256StateWords - 1 - i] ^
                 state_s1[kSha256StateWords - 1 - i];
    digest_words[i] = __builtin_bswap32(h);
  }
  memcpy(digest_out, digest_words, sizeof(digest_words));

  return OK_STATUS();
}

static status_t sha512_family_otbn_sca_run(const uint8_t *msg, size_t msg_len,
                                           bool is_sha384, bool en_masks,
                                           uint8_t *digest_out) {
  otbn_addr_t addr_state_s0;
  otbn_addr_t addr_state_s1;
  otbn_addr_t addr_msg_s0;
  otbn_addr_t addr_msg_s1;
  otbn_addr_t addr_n_chunks;
  const uint32_t *init_state;

  if (is_sha384) {
    const otbn_app_t kApp = OTBN_APP_T_INIT(run_sha384);
    TRY(otbn_sca_load_app_cached(kApp));
    addr_state_s0 = OTBN_ADDR_T_INIT(run_sha384, state_s0);
    addr_state_s1 = OTBN_ADDR_T_INIT(run_sha384, state_s1);
    addr_msg_s0 = OTBN_ADDR_T_INIT(run_sha384, msg_s0);
    addr_msg_s1 = OTBN_ADDR_T_INIT(run_sha384, msg_s1);
    addr_n_chunks = OTBN_ADDR_T_INIT(run_sha384, n_chunks);
    init_state = kSha384InitialState;
  } else {
    const otbn_app_t kApp = OTBN_APP_T_INIT(run_sha512);
    TRY(otbn_sca_load_app_cached(kApp));
    addr_state_s0 = OTBN_ADDR_T_INIT(run_sha512, state_s0);
    addr_state_s1 = OTBN_ADDR_T_INIT(run_sha512, state_s1);
    addr_msg_s0 = OTBN_ADDR_T_INIT(run_sha512, msg_s0);
    addr_msg_s1 = OTBN_ADDR_T_INIT(run_sha512, msg_s1);
    addr_n_chunks = OTBN_ADDR_T_INIT(run_sha512, n_chunks);
    init_state = kSha512InitialState;
  }

  uint32_t state_s0[kSha512StateWords];
  uint32_t state_s1[kSha512StateWords];
  for (size_t i = 0; i < kSha512StateWords; ++i) {
    state_s1[i] = en_masks ? ibex_rnd32_read() : 0;
    state_s0[i] = init_state[i] ^ state_s1[i];
  }
  TRY(otbn_dmem_write(kSha512StateWords, state_s0, addr_state_s0));
  TRY(otbn_dmem_write(kSha512StateWords, state_s1, addr_state_s1));

  uint32_t padded[kSha512BlockWords];
  memset(padded, 0, sizeof(padded));
  if (msg_len > 0) {
    memcpy(padded, msg, msg_len);
  }
  ((uint8_t *)padded)[msg_len] = 0x80;

  uint64_t total_bits = ((uint64_t)msg_len) << 3;
  padded[kSha512BlockWords - 1] =
      __builtin_bswap32((uint32_t)(total_bits & UINT32_MAX));
  padded[kSha512BlockWords - 2] =
      __builtin_bswap32((uint32_t)(total_bits >> 32));

  uint32_t msg_s0[kSha512BlockWords];
  uint32_t msg_s1[kSha512BlockWords];
  for (size_t i = 0; i < kSha512BlockWords; ++i) {
    msg_s1[i] = en_masks ? ibex_rnd32_read() : 0;
    msg_s0[i] = padded[i] ^ msg_s1[i];
  }
  uint32_t num_chunks = 1;
  TRY(otbn_dmem_write(kSha512BlockWords, msg_s0, addr_msg_s0));
  TRY(otbn_dmem_write(kSha512BlockWords, msg_s1, addr_msg_s1));
  TRY(otbn_dmem_write(1, &num_chunks, addr_n_chunks));

  pentest_set_trigger_high();
  asm volatile(NOP30);
  otbn_execute();
  otbn_busy_wait_for_done();
  pentest_set_trigger_low();

  TRY(otbn_dmem_read(kSha512StateWords, addr_state_s0, state_s0));
  TRY(otbn_dmem_read(kSha512StateWords, addr_state_s1, state_s1));

  uint32_t h[kSha512StateWords];
  for (size_t i = 0; i < kSha512StateWords; ++i) {
    h[i] = state_s0[i] ^ state_s1[i];
  }

  size_t digest_words_cnt = is_sha384 ? kSha384DigestWords : kSha512DigestWords;
  uint32_t digest_words[kSha512DigestWords];
  for (size_t k = 0; k < digest_words_cnt / 2; ++k) {
    digest_words[2 * k] = __builtin_bswap32(h[15 - 2 * k]);
    digest_words[2 * k + 1] = __builtin_bswap32(h[14 - 2 * k]);
  }
  memcpy(digest_out, digest_words, digest_words_cnt * sizeof(uint32_t));

  return OK_STATUS();
}

static status_t sha2_otbn_sca_dispatch(const uint8_t *msg, size_t msg_len,
                                       uint32_t mode, bool en_masks,
                                       uint8_t *digest_out) {
  if (msg_len > OTBNSCA_CMD_MAX_SHA2_MSG_BYTES) {
    return OUT_OF_RANGE();
  }
  memset(digest_out, 0, OTBNSCA_CMD_MAX_SHA2_DIGEST_BYTES);
  if (mode == 0 || mode == 256) {
    return sha256_otbn_sca_run(msg, msg_len, en_masks, digest_out);
  } else if (mode == 1 || mode == 384) {
    return sha512_family_otbn_sca_run(msg, msg_len, /*is_sha384=*/true,
                                      en_masks, digest_out);
  } else if (mode == 2 || mode == 512) {
    return sha512_family_otbn_sca_run(msg, msg_len, /*is_sha384=*/false,
                                      en_masks, digest_out);
  } else {
    return INVALID_ARGUMENT();
  }
}

status_t handle_otbn_sca_sha2_single(ujson_t *uj) {
  penetrationtest_otbn_sca_sha2_cfg_t uj_cfg;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_sha2_cfg_t(uj, &uj_cfg));

  penetrationtest_otbn_sca_sha2_digest_t uj_output;
  TRY(sha2_otbn_sca_dispatch(uj_cfg.msg, uj_cfg.msg_len, uj_cfg.mode,
                             uj_cfg.en_masks, uj_output.digest));

  RESP_OK(ujson_serialize_penetrationtest_otbn_sca_sha2_digest_t, uj,
          &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_sca_sha2_batch_fvsr(ujson_t *uj) {
  penetrationtest_otbn_sca_num_traces_t uj_num_traces;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_num_traces_t(uj,
                                                              &uj_num_traces));
  penetrationtest_otbn_sca_sha2_cfg_t uj_cfg;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_sha2_cfg_t(uj, &uj_cfg));

  if (uj_num_traces.num_traces == 0 ||
      uj_num_traces.num_traces > kSha2ScaMaxBatchSize ||
      uj_cfg.msg_len > OTBNSCA_CMD_MAX_SHA2_MSG_BYTES) {
    return OUT_OF_RANGE();
  }

  bool sample_fixed = true;
  for (size_t it = 0; it < uj_num_traces.num_traces; ++it) {
    memset(sha2_batch_msgs[it], 0, OTBNSCA_CMD_MAX_SHA2_MSG_BYTES);
    if (sample_fixed) {
      memcpy(sha2_batch_msgs[it], uj_cfg.msg, uj_cfg.msg_len);
    } else {
      prng_rand_bytes(sha2_batch_msgs[it], uj_cfg.msg_len);
    }
    sample_fixed = prng_rand_byte() & 0x1;
  }

  penetrationtest_otbn_sca_sha2_digest_t uj_output;
  for (size_t it = 0; it < uj_num_traces.num_traces; ++it) {
    TRY(sha2_otbn_sca_dispatch(sha2_batch_msgs[it], uj_cfg.msg_len, uj_cfg.mode,
                               uj_cfg.en_masks, uj_output.digest));
  }

  RESP_OK(ujson_serialize_penetrationtest_otbn_sca_sha2_digest_t, uj,
          &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_sca_sha2_batch_random(ujson_t *uj) {
  penetrationtest_otbn_sca_num_traces_t uj_num_traces;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_num_traces_t(uj,
                                                              &uj_num_traces));
  penetrationtest_otbn_sca_sha2_cfg_t uj_cfg;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_sha2_cfg_t(uj, &uj_cfg));

  if (uj_num_traces.num_traces == 0 ||
      uj_num_traces.num_traces > kSha2ScaMaxBatchSize ||
      uj_cfg.msg_len > OTBNSCA_CMD_MAX_SHA2_MSG_BYTES) {
    return OUT_OF_RANGE();
  }

  for (size_t it = 0; it < uj_num_traces.num_traces; ++it) {
    memset(sha2_batch_msgs[it], 0, OTBNSCA_CMD_MAX_SHA2_MSG_BYTES);
    prng_rand_bytes(sha2_batch_msgs[it], uj_cfg.msg_len);
  }

  penetrationtest_otbn_sca_sha2_digest_t uj_output;
  for (size_t it = 0; it < uj_num_traces.num_traces; ++it) {
    TRY(sha2_otbn_sca_dispatch(sha2_batch_msgs[it], uj_cfg.msg_len, uj_cfg.mode,
                               uj_cfg.en_masks, uj_output.digest));
  }

  RESP_OK(ujson_serialize_penetrationtest_otbn_sca_sha2_digest_t, uj,
          &uj_output);
  return OK_STATUS();
}
