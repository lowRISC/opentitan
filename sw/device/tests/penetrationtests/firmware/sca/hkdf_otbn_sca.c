// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/tests/penetrationtests/firmware/sca/hkdf_otbn_sca.h"

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
  kHkdfScaMaxBatchSize = 128,
  kHkdfScaMaxDigestWords = 16,
  kHkdfScaMaxOkmWords = 16,
};

OTBN_DECLARE_APP_SYMBOLS(run_hkdf_sha256);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, salt);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, ikm_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, ikm_s1);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, ikm_len);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, info);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, info_len);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, num_okm_blocks);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, prk_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, prk_s1);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, okm_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha256, okm_s1);

OTBN_DECLARE_APP_SYMBOLS(run_hkdf_sha384);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, salt);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, ikm_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, ikm_s1);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, ikm_len);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, info);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, info_len);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, num_okm_blocks);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, prk_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, prk_s1);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, okm_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha384, okm_s1);

OTBN_DECLARE_APP_SYMBOLS(run_hkdf_sha512);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, salt);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, ikm_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, ikm_s1);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, ikm_len);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, info);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, info_len);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, num_okm_blocks);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, prk_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, prk_s1);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, okm_s0);
OTBN_DECLARE_SYMBOL_ADDR(run_hkdf_sha512, okm_s1);

typedef struct hkdf_sca_app_cfg {
  otbn_addr_t addr_salt;
  otbn_addr_t addr_ikm_s0;
  otbn_addr_t addr_ikm_s1;
  otbn_addr_t addr_ikm_len;
  otbn_addr_t addr_info;
  otbn_addr_t addr_info_len;
  otbn_addr_t addr_num_okm_blocks;
  otbn_addr_t addr_prk_s0;
  otbn_addr_t addr_prk_s1;
  otbn_addr_t addr_okm_s0;
  otbn_addr_t addr_okm_s1;
  size_t digest_words;
  size_t block_words;
  size_t ikm_words;
  size_t max_okm_blocks;
} hkdf_sca_app_cfg_t;

static uint8_t hkdf_batch_ikm[kHkdfScaMaxBatchSize]
                             [OTBNSCA_CMD_MAX_HKDF_IKM_BYTES];
static uint8_t hkdf_batch_salt[kHkdfScaMaxBatchSize]
                              [OTBNSCA_CMD_MAX_HKDF_SALT_BYTES];

static status_t hkdf_otbn_sca_load_and_cfg(uint32_t mode,
                                           hkdf_sca_app_cfg_t *cfg) {
  if (mode == 0 || mode == 256) {
    const otbn_app_t kApp = OTBN_APP_T_INIT(run_hkdf_sha256);
    TRY(otbn_load_app(kApp));
    *cfg = (hkdf_sca_app_cfg_t){
        .addr_salt = OTBN_ADDR_T_INIT(run_hkdf_sha256, salt),
        .addr_ikm_s0 = OTBN_ADDR_T_INIT(run_hkdf_sha256, ikm_s0),
        .addr_ikm_s1 = OTBN_ADDR_T_INIT(run_hkdf_sha256, ikm_s1),
        .addr_ikm_len = OTBN_ADDR_T_INIT(run_hkdf_sha256, ikm_len),
        .addr_info = OTBN_ADDR_T_INIT(run_hkdf_sha256, info),
        .addr_info_len = OTBN_ADDR_T_INIT(run_hkdf_sha256, info_len),
        .addr_num_okm_blocks =
            OTBN_ADDR_T_INIT(run_hkdf_sha256, num_okm_blocks),
        .addr_prk_s0 = OTBN_ADDR_T_INIT(run_hkdf_sha256, prk_s0),
        .addr_prk_s1 = OTBN_ADDR_T_INIT(run_hkdf_sha256, prk_s1),
        .addr_okm_s0 = OTBN_ADDR_T_INIT(run_hkdf_sha256, okm_s0),
        .addr_okm_s1 = OTBN_ADDR_T_INIT(run_hkdf_sha256, okm_s1),
        .digest_words = 8,
        .block_words = 16,
        .ikm_words = 24,
        .max_okm_blocks = 8,
    };
    return OK_STATUS();
  } else if (mode == 1 || mode == 384) {
    const otbn_app_t kApp = OTBN_APP_T_INIT(run_hkdf_sha384);
    TRY(otbn_load_app(kApp));
    *cfg = (hkdf_sca_app_cfg_t){
        .addr_salt = OTBN_ADDR_T_INIT(run_hkdf_sha384, salt),
        .addr_ikm_s0 = OTBN_ADDR_T_INIT(run_hkdf_sha384, ikm_s0),
        .addr_ikm_s1 = OTBN_ADDR_T_INIT(run_hkdf_sha384, ikm_s1),
        .addr_ikm_len = OTBN_ADDR_T_INIT(run_hkdf_sha384, ikm_len),
        .addr_info = OTBN_ADDR_T_INIT(run_hkdf_sha384, info),
        .addr_info_len = OTBN_ADDR_T_INIT(run_hkdf_sha384, info_len),
        .addr_num_okm_blocks =
            OTBN_ADDR_T_INIT(run_hkdf_sha384, num_okm_blocks),
        .addr_prk_s0 = OTBN_ADDR_T_INIT(run_hkdf_sha384, prk_s0),
        .addr_prk_s1 = OTBN_ADDR_T_INIT(run_hkdf_sha384, prk_s1),
        .addr_okm_s0 = OTBN_ADDR_T_INIT(run_hkdf_sha384, okm_s0),
        .addr_okm_s1 = OTBN_ADDR_T_INIT(run_hkdf_sha384, okm_s1),
        .digest_words = 12,
        .block_words = 32,
        .ikm_words = 32,
        .max_okm_blocks = 6,
    };
    return OK_STATUS();
  } else if (mode == 2 || mode == 512) {
    const otbn_app_t kApp = OTBN_APP_T_INIT(run_hkdf_sha512);
    TRY(otbn_load_app(kApp));
    *cfg = (hkdf_sca_app_cfg_t){
        .addr_salt = OTBN_ADDR_T_INIT(run_hkdf_sha512, salt),
        .addr_ikm_s0 = OTBN_ADDR_T_INIT(run_hkdf_sha512, ikm_s0),
        .addr_ikm_s1 = OTBN_ADDR_T_INIT(run_hkdf_sha512, ikm_s1),
        .addr_ikm_len = OTBN_ADDR_T_INIT(run_hkdf_sha512, ikm_len),
        .addr_info = OTBN_ADDR_T_INIT(run_hkdf_sha512, info),
        .addr_info_len = OTBN_ADDR_T_INIT(run_hkdf_sha512, info_len),
        .addr_num_okm_blocks =
            OTBN_ADDR_T_INIT(run_hkdf_sha512, num_okm_blocks),
        .addr_prk_s0 = OTBN_ADDR_T_INIT(run_hkdf_sha512, prk_s0),
        .addr_prk_s1 = OTBN_ADDR_T_INIT(run_hkdf_sha512, prk_s1),
        .addr_okm_s0 = OTBN_ADDR_T_INIT(run_hkdf_sha512, okm_s0),
        .addr_okm_s1 = OTBN_ADDR_T_INIT(run_hkdf_sha512, okm_s1),
        .digest_words = 16,
        .block_words = 32,
        .ikm_words = 32,
        .max_okm_blocks = 4,
    };
    return OK_STATUS();
  }
  return INVALID_ARGUMENT();
}

static status_t hkdf_otbn_sca_run(const uint8_t *ikm, size_t ikm_len,
                                  const uint8_t *salt, size_t salt_len,
                                  const uint8_t *info, size_t info_len,
                                  uint32_t okm_blocks, uint32_t mode,
                                  bool en_masks, uint8_t *prk_out,
                                  uint8_t *okm_out) {
  if (ikm_len > OTBNSCA_CMD_MAX_HKDF_IKM_BYTES ||
      salt_len > OTBNSCA_CMD_MAX_HKDF_SALT_BYTES ||
      info_len > OTBNSCA_CMD_MAX_HKDF_INFO_BYTES) {
    return OUT_OF_RANGE();
  }

  hkdf_sca_app_cfg_t cfg;
  TRY(hkdf_otbn_sca_load_and_cfg(mode, &cfg));

  uint32_t num_blocks = (okm_blocks == 0) ? 1 : okm_blocks;
  if (num_blocks > cfg.max_okm_blocks) {
    return OUT_OF_RANGE();
  }

  uint32_t salt_buf[32];
  memset(salt_buf, 0, sizeof(salt_buf));
  if (salt_len > 0) {
    memcpy(salt_buf, salt, salt_len);
  }
  TRY(otbn_dmem_write(cfg.block_words, salt_buf, cfg.addr_salt));

  uint32_t ikm_words_buf[32];
  memset(ikm_words_buf, 0, sizeof(ikm_words_buf));
  if (ikm_len > 0) {
    memcpy(ikm_words_buf, ikm, ikm_len);
  }

  uint32_t ikm_s0_buf[32];
  uint32_t ikm_s1_buf[32];
  for (size_t i = 0; i < cfg.ikm_words; ++i) {
    uint32_t r = en_masks ? ibex_rnd32_read() : 0;
    ikm_s1_buf[i] = r;
    ikm_s0_buf[i] = ikm_words_buf[i] ^ r;
  }
  TRY(otbn_dmem_write(cfg.ikm_words, ikm_s0_buf, cfg.addr_ikm_s0));
  TRY(otbn_dmem_write(cfg.ikm_words, ikm_s1_buf, cfg.addr_ikm_s1));

  uint32_t ikm_len_u32 = (uint32_t)ikm_len;
  TRY(otbn_dmem_write(1, &ikm_len_u32, cfg.addr_ikm_len));

  uint32_t info_buf[24];
  memset(info_buf, 0, sizeof(info_buf));
  if (info_len > 0) {
    memcpy(info_buf, info, info_len);
  }
  uint32_t info_len_u32 = (uint32_t)info_len;
  TRY(otbn_dmem_write(24, info_buf, cfg.addr_info));
  TRY(otbn_dmem_write(1, &info_len_u32, cfg.addr_info_len));

  TRY(otbn_dmem_write(1, &num_blocks, cfg.addr_num_okm_blocks));

  pentest_set_trigger_high();
  asm volatile(NOP30);
  otbn_execute();
  otbn_busy_wait_for_done();
  pentest_set_trigger_low();

  memset(prk_out, 0, OTBNSCA_CMD_MAX_HKDF_OKM_BYTES);
  memset(okm_out, 0, OTBNSCA_CMD_MAX_HKDF_OKM_BYTES);

  uint32_t prk_s0[kHkdfScaMaxDigestWords];
  uint32_t prk_s1[kHkdfScaMaxDigestWords];
  uint32_t prk_unmasked[kHkdfScaMaxDigestWords];
  TRY(otbn_dmem_read(cfg.digest_words, cfg.addr_prk_s0, prk_s0));
  TRY(otbn_dmem_read(cfg.digest_words, cfg.addr_prk_s1, prk_s1));
  for (size_t i = 0; i < cfg.digest_words; ++i) {
    prk_unmasked[i] = prk_s0[i] ^ prk_s1[i];
  }
  memcpy(prk_out, prk_unmasked, cfg.digest_words * sizeof(uint32_t));

  size_t okm_words_total = num_blocks * cfg.digest_words;
  size_t okm_words_read = (okm_words_total > kHkdfScaMaxOkmWords)
                              ? kHkdfScaMaxOkmWords
                              : okm_words_total;
  uint32_t okm_s0[kHkdfScaMaxOkmWords];
  uint32_t okm_s1[kHkdfScaMaxOkmWords];
  uint32_t okm_unmasked[kHkdfScaMaxOkmWords];
  TRY(otbn_dmem_read(okm_words_read, cfg.addr_okm_s0, okm_s0));
  TRY(otbn_dmem_read(okm_words_read, cfg.addr_okm_s1, okm_s1));
  for (size_t i = 0; i < okm_words_read; ++i) {
    okm_unmasked[i] = okm_s0[i] ^ okm_s1[i];
  }
  memcpy(okm_out, okm_unmasked, okm_words_read * sizeof(uint32_t));

  TRY(otbn_dmem_sec_wipe());
  return OK_STATUS();
}

status_t handle_otbn_sca_hkdf_single(ujson_t *uj) {
  penetrationtest_otbn_sca_hkdf_cfg_t uj_cfg;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_hkdf_cfg_t(uj, &uj_cfg));

  penetrationtest_otbn_sca_hkdf_out_t uj_output;
  TRY(hkdf_otbn_sca_run(uj_cfg.ikm, uj_cfg.ikm_len, uj_cfg.salt,
                        uj_cfg.salt_len, uj_cfg.info, uj_cfg.info_len,
                        uj_cfg.okm_blocks, uj_cfg.mode, uj_cfg.en_masks,
                        uj_output.prk, uj_output.okm));

  RESP_OK(ujson_serialize_penetrationtest_otbn_sca_hkdf_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_sca_hkdf_batch_fvsr(ujson_t *uj) {
  penetrationtest_otbn_sca_num_traces_t uj_num_traces;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_num_traces_t(uj,
                                                              &uj_num_traces));
  penetrationtest_otbn_sca_hkdf_cfg_t uj_cfg;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_hkdf_cfg_t(uj, &uj_cfg));

  if (uj_num_traces.num_traces == 0 ||
      uj_num_traces.num_traces > kHkdfScaMaxBatchSize ||
      uj_cfg.ikm_len > OTBNSCA_CMD_MAX_HKDF_IKM_BYTES ||
      uj_cfg.salt_len > OTBNSCA_CMD_MAX_HKDF_SALT_BYTES ||
      uj_cfg.info_len > OTBNSCA_CMD_MAX_HKDF_INFO_BYTES) {
    return OUT_OF_RANGE();
  }

  bool sample_fixed = true;
  for (size_t it = 0; it < uj_num_traces.num_traces; ++it) {
    memset(hkdf_batch_ikm[it], 0, OTBNSCA_CMD_MAX_HKDF_IKM_BYTES);
    if (sample_fixed) {
      memcpy(hkdf_batch_ikm[it], uj_cfg.ikm, uj_cfg.ikm_len);
    } else {
      prng_rand_bytes(hkdf_batch_ikm[it], uj_cfg.ikm_len);
    }
    sample_fixed = prng_rand_byte() & 0x1;
  }

  penetrationtest_otbn_sca_hkdf_out_t uj_output;
  for (size_t it = 0; it < uj_num_traces.num_traces; ++it) {
    TRY(hkdf_otbn_sca_run(hkdf_batch_ikm[it], uj_cfg.ikm_len, uj_cfg.salt,
                          uj_cfg.salt_len, uj_cfg.info, uj_cfg.info_len,
                          uj_cfg.okm_blocks, uj_cfg.mode, uj_cfg.en_masks,
                          uj_output.prk, uj_output.okm));
  }

  RESP_OK(ujson_serialize_penetrationtest_otbn_sca_hkdf_out_t, uj, &uj_output);
  return OK_STATUS();
}

status_t handle_otbn_sca_hkdf_batch_random(ujson_t *uj) {
  penetrationtest_otbn_sca_num_traces_t uj_num_traces;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_num_traces_t(uj,
                                                              &uj_num_traces));
  penetrationtest_otbn_sca_hkdf_cfg_t uj_cfg;
  TRY(ujson_deserialize_penetrationtest_otbn_sca_hkdf_cfg_t(uj, &uj_cfg));

  if (uj_num_traces.num_traces == 0 ||
      uj_num_traces.num_traces > kHkdfScaMaxBatchSize ||
      uj_cfg.ikm_len > OTBNSCA_CMD_MAX_HKDF_IKM_BYTES ||
      uj_cfg.salt_len > OTBNSCA_CMD_MAX_HKDF_SALT_BYTES ||
      uj_cfg.info_len > OTBNSCA_CMD_MAX_HKDF_INFO_BYTES) {
    return OUT_OF_RANGE();
  }

  for (size_t it = 0; it < uj_num_traces.num_traces; ++it) {
    memset(hkdf_batch_ikm[it], 0, OTBNSCA_CMD_MAX_HKDF_IKM_BYTES);
    memset(hkdf_batch_salt[it], 0, OTBNSCA_CMD_MAX_HKDF_SALT_BYTES);
    prng_rand_bytes(hkdf_batch_ikm[it], uj_cfg.ikm_len);
    prng_rand_bytes(hkdf_batch_salt[it], uj_cfg.salt_len);
  }

  penetrationtest_otbn_sca_hkdf_out_t uj_output;
  for (size_t it = 0; it < uj_num_traces.num_traces; ++it) {
    TRY(hkdf_otbn_sca_run(hkdf_batch_ikm[it], uj_cfg.ikm_len,
                          hkdf_batch_salt[it], uj_cfg.salt_len, uj_cfg.info,
                          uj_cfg.info_len, uj_cfg.okm_blocks, uj_cfg.mode,
                          uj_cfg.en_masks, uj_output.prk, uj_output.okm));
  }

  RESP_OK(ujson_serialize_penetrationtest_otbn_sca_hkdf_out_t, uj, &uj_output);
  return OK_STATUS();
}
