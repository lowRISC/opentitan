// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "sw/device/lib/testing/alert_handler_testutils.h"

#include "sw/device/lib/base/math.h"
#include "sw/device/lib/dif/dif_alert_handler.h"
#include "sw/device/lib/dif/dif_base.h"
#include "sw/device/lib/dif/dif_rstmgr.h"
#include "sw/device/lib/testing/test_framework/check.h"

#include "alert_handler_regs.h"  // Generated

/**
 * This is used to traverse the dump treating it as an array of bits, and
 * extract a number of bits placing them in a uint32_t. The word and bit index
 * are updated by num_bits before returning.
 */
static uint32_t get_next_n_bits(
    int num_bits, const dif_rstmgr_alert_info_dump_segment_t *dump,
    int *word_index, int *bit_index) {
  CHECK(num_bits <= 32);
  CHECK(*bit_index < 32);
  uint32_t word = dump[*word_index] >> *bit_index;
  if (*bit_index + num_bits >= 32) {
    (*word_index) += 1;
    *bit_index = *bit_index + num_bits - 32;
  } else {
    *bit_index += num_bits;
  }
  word &= (1 << num_bits) - 1;
  return word;
}

status_t alert_handler_testutils_info_parse(
    const dif_rstmgr_alert_info_dump_segment_t *dump, int dump_size,
    alert_handler_testutils_info_t *info) {
  int word_index = 0;
  int bit_index = 0;
  for (int i = 0; i < ALERT_HANDLER_PARAM_N_CLASSES; ++i) {
    info->class_esc_state[i] =
        get_next_n_bits(3, dump, &word_index, &bit_index);
  }
  for (int i = 0; i < ALERT_HANDLER_PARAM_N_CLASSES; ++i) {
    info->class_esc_cnt[i] = get_next_n_bits(32, dump, &word_index, &bit_index);
  }
  for (int i = 0; i < ALERT_HANDLER_PARAM_N_CLASSES; ++i) {
    info->class_accum_cnt[i] =
        (uint16_t)get_next_n_bits(16, dump, &word_index, &bit_index);
  }
  info->loc_alert_cause =
      (uint8_t)get_next_n_bits(7, dump, &word_index, &bit_index);
  TRY_CHECK(word_index < dump_size);
  for (int i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
    info->alert_cause[i] = get_next_n_bits(1, dump, &word_index, &bit_index);
  }
  TRY_CHECK(word_index < dump_size);
  return OK_STATUS();
}

void alert_handler_testutils_info_dump(
    const alert_handler_testutils_info_t *info) {
  LOG_INFO("alert_info:");
  LOG_INFO("esc_state [0]=%x, [1]=%x, [2]=%x, [3]=%x", info->class_esc_state[0],
           info->class_esc_state[1], info->class_esc_state[2],
           info->class_esc_state[3]);
  LOG_INFO("esc_cnt [0]=0x%x, [1]=0x%x, [2]=0x%x, [3]=0x%x",
           info->class_esc_cnt[0], info->class_esc_cnt[1],
           info->class_esc_cnt[2], info->class_esc_cnt[3]);
  LOG_INFO("accum_cnt [0]=0x%x, [1]=0x%x, [2]=0x%x, [3]=0x%x",
           info->class_accum_cnt[0], info->class_accum_cnt[1],
           info->class_accum_cnt[2], info->class_accum_cnt[3]);
  LOG_INFO("loc_alert_cause=0x%x", info->loc_alert_cause);
  int set_count = 0;
  LOG_INFO("alert_cause bits set:");
  // Typically very few bits are set, so it is more clear to only show the
  // on bits.
  for (int i = 0; i < ALERT_HANDLER_PARAM_N_ALERTS; ++i) {
    if (info->alert_cause[i]) {
      LOG_INFO("alert_cause[%d] = 1", i);
      ++set_count;
    }
  }
  if (set_count == 0) {
    LOG_INFO("No bits set");
  }
}

status_t alert_handler_testutils_configure_all(
    const dif_alert_handler_t *alert_handler, dif_alert_handler_config_t config,
    dif_toggle_t locked) {
  TRY_CHECK(alert_handler != NULL);
  TRY_CHECK(dif_is_valid_toggle(locked));

  // Check lengths of alert, local alert, and class arrays.
  TRY_CHECK((config.alerts_len > 0 && config.alerts != NULL &&
             config.alert_classes != NULL) ||
            (config.alerts_len == 0 && config.alerts == NULL &&
             config.alert_classes == NULL));
  TRY_CHECK((config.local_alerts_len > 0 && config.local_alerts != NULL &&
             config.local_alert_classes != NULL) ||
            (config.local_alerts_len == 0 && config.local_alerts == NULL &&
             config.local_alert_classes == NULL));
  TRY_CHECK((config.classes_len > 0 && config.classes != NULL &&
             config.class_configs != NULL) ||
            (config.classes_len == 0 && config.classes == NULL &&
             config.class_configs == NULL));

  // Check that the provided ping timeout actually fits in the timeout
  // register, which is smaller than a native word length.
  TRY_CHECK(
      config.ping_timeout <=
      ALERT_HANDLER_PING_TIMEOUT_CYC_SHADOWED_PING_TIMEOUT_CYC_SHADOWED_MASK);

  // Configure and enable the requested alerts.
  for (int i = 0; i < config.alerts_len; ++i) {
    TRY(dif_alert_handler_configure_alert(alert_handler, config.alerts[i],
                                          config.alert_classes[i],
                                          kDifToggleEnabled, locked));
  }

  // Configure and enable the requested local alerts.
  for (int i = 0; i < config.local_alerts_len; ++i) {
    TRY(dif_alert_handler_configure_local_alert(
        alert_handler, config.local_alerts[i], config.local_alert_classes[i],
        kDifToggleEnabled, locked));
  }

  // Configure and enable the requested classes.
  for (int i = 0; i < config.classes_len; ++i) {
    TRY(dif_alert_handler_configure_class(alert_handler, config.classes[i],
                                          config.class_configs[i],
                                          kDifToggleEnabled, locked));
  }

  // Configure the ping timer.
  TRY(dif_alert_handler_configure_ping_timer(alert_handler, config.ping_timeout,
                                             kDifToggleEnabled, locked));

  return OK_STATUS();
}

status_t alert_handler_testutils_get_cycles_from_us(uint64_t microseconds,
                                                    uint32_t *cycles) {
  uint64_t cycles_ = udiv64_slow(microseconds * kClockFreqPeripheralHz, 1000000,
                                 /*rem_out=*/NULL);
  TRY_CHECK(cycles_ < UINT32_MAX,
            "The value 0x%08x%08x can't fit into the 32 bits timer counter.",
            (cycles_ >> 32), (uint32_t)cycles_);
  *cycles = (uint32_t)cycles_;
  return OK_STATUS();
}

uint32_t alert_handler_testutils_cycle_rescaling_factor() {
  return kDeviceType == kDeviceSimDV ? 1 : 10;
}
