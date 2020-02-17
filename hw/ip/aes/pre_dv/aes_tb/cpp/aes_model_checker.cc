// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "aes_model_checker.h"

#include "aes.h"
#include "crypto.h"

AESModelChecker::AESModelChecker(Vaes_sim *rtl) : rtl_(rtl) {
  state_model_.cipher_op = false;
  state_model_.key_expand_op = false;
  state_model_.key_len = 16;
  state_model_.start = false;
  state_model_.init = false;
  state_model_.done = false;
  state_model_.busy = false;
  state_model_.round = 0;
  state_model_.num_rounds = 0;
  state_model_.key_init[32] = {0};
  state_model_.data_in[16] = {0};
  state_model_.state_d[16] = {0};
  state_model_.state_q[16] = {0};
  state_model_.sub_bytes_out[16] = {0};
  state_model_.shift_rows_out[16] = {0};
  state_model_.mix_columns_out[16] = {0};
  state_model_.add_round_key_out[16] = {0};
  state_model_.full_key[32] = {0};
  state_model_.round_key[16] = {0};
  state_model_.rcon = 0;
  state_model_.data_out[16] = {0};
  state_rtl_.cipher_op = false;
  state_rtl_.key_expand_op = false;
  state_rtl_.key_len = 16;
  state_rtl_.start = false;
  state_rtl_.init = false;
  state_rtl_.done = false;
  state_rtl_.busy = false;
  state_rtl_.round = 0;
  state_rtl_.key_init[32] = {0};
  state_rtl_.num_rounds = 0;
  state_rtl_.data_in[16] = {0};
  state_rtl_.state_d[16] = {0};
  state_rtl_.state_q[16] = {0};
  state_rtl_.sub_bytes_out[16] = {0};
  state_rtl_.shift_rows_out[16] = {0};
  state_rtl_.mix_columns_out[16] = {0};
  state_rtl_.add_round_key_out[16] = {0};
  state_rtl_.full_key[32] = {0};
  state_rtl_.round_key[16] = {0};
  state_rtl_.rcon = 0;
  state_rtl_.data_out[16] = {0};
}

int AESModelChecker::CheckModel() {
  int status = 0;

  // Update RTL state
  MonitorSignals();

  // Update Model
  UpdateModel();

  // Visual comparison of RTL and model state
  if (DEBUG_LEVEL > 0) {
    Print();
  }

  // Compare Model vs. RTL
  status = Compare();

  return status;
}

void AESModelChecker::Print() {
  if ((state_rtl_.busy) && (state_rtl_.key_expand_op == state_rtl_.cipher_op)) {
    if (state_model_.round == 0) {  // this was the initial round
      printf("Init state_q RTL         ");
      aes_print_block(&state_rtl_.state_q[0], 16);
      printf("Init state_q model       ");
      aes_print_block(&state_model_.state_q[0], 16);
      printf("Init round_key RTL       ");
      aes_print_block(&state_rtl_.round_key[0], 16);
      printf("Init round_key model     ");
      aes_print_block(&state_model_.round_key[0], 16);
    } else if ((state_model_.round > 0) &&
               (state_model_.round <
                state_model_.num_rounds)) {  // normal rounds
      printf("Round %2i state_q RTL     ", state_model_.round - 1);
      aes_print_block(&state_rtl_.state_q[0], 16);
      printf("Round %2i state_q model   ", state_model_.round - 1);
      aes_print_block(&state_model_.state_q[0], 16);
      printf("Round %2i round_key RTL   ", state_model_.round - 1);
      aes_print_block(&state_rtl_.round_key[0], 16);
      printf("Round %2i round_key model ", state_model_.round - 1);
      aes_print_block(&state_model_.round_key[0], 16);
    } else if (state_model_.round == state_model_.num_rounds) {  // last round
      printf("Round %2i state_q RTL     ", state_model_.round - 1);
      aes_print_block(&state_rtl_.state_q[0], 16);
      printf("Round %2i state_q model   ", state_model_.round - 1);
      aes_print_block(&state_model_.state_q[0], 16);
      printf("Round %2i round_key RTL   ", state_model_.round - 1);
      aes_print_block(&state_rtl_.round_key[0], 16);
      printf("Round %2i round_key model ", state_model_.round - 1);
      aes_print_block(&state_model_.round_key[0], 16);

      printf("Output RTL               ");
      aes_print_block(&state_rtl_.data_out[0], 16);
      printf("Output model             ");
      aes_print_block(&state_model_.data_out[0], 16);
    }
  }

  return;
}

int AESModelChecker::Compare() {
  int status;

  // compare model vs RTL
  if (state_rtl_.busy && !state_rtl_.start && !state_rtl_.init &&
      (state_rtl_.round >= 0)) {
    // full key
    status = CompareBlock(state_model_.full_key, state_rtl_.full_key,
                          state_rtl_.key_len);
    if (status) {
      printf("ERROR: mismatch between model and RTL:\n");
      printf("Round %i full_key RTL\t", state_rtl_.round);
      aes_print_block(&state_rtl_.full_key[0], state_rtl_.key_len);
      printf("Round %i full_key model\t", state_rtl_.round);
      aes_print_block(&state_model_.full_key[0], state_rtl_.key_len);
      return status;
    }

    if (state_rtl_.key_expand_op == state_rtl_.cipher_op) {
      // round key
      status = CompareBlock(state_model_.round_key, state_rtl_.round_key, 16);
      if (status) {
        printf("ERROR: mismatch between model and RTL:\n");
        printf("Round %i round_key RTL\t", state_rtl_.round);
        aes_print_block(&state_rtl_.round_key[0], 16);
        printf("Round %i round_key model\t", state_rtl_.round);
        aes_print_block(&state_model_.round_key[0], 16);
        return status;
      }

      // state_q
      status = CompareBlock(state_model_.state_q, state_rtl_.state_q, 16);
      if (status) {
        printf("ERROR: mismatch between model and RTL:\n");
        printf("Round %i state_q RTL\t", state_rtl_.round);
        aes_print_block(&state_rtl_.state_q[0], 16);
        printf("Round %i state_q model\t", state_rtl_.round);
        aes_print_block(&state_model_.state_q[0], 16);
        return status;
      }

      // sub_bytes_out
      status = CompareBlock(state_model_.sub_bytes_out,
                            state_rtl_.sub_bytes_out, 16);
      if (status) {
        printf("ERROR: mismatch between model and RTL:\n");
        printf("Round %i sub_bytes_out RTL\t", state_rtl_.round);
        aes_print_block(&state_rtl_.sub_bytes_out[0], 16);
        printf("Round %i sub_bytes_out model\t", state_rtl_.round);
        aes_print_block(&state_model_.sub_bytes_out[0], 16);
        return status;
      }

      // shift_rows_out
      status = CompareBlock(state_model_.shift_rows_out,
                            state_rtl_.shift_rows_out, 16);
      if (status) {
        printf("ERROR: mismatch between model and RTL:\n");
        printf("Round %i shift_rows_out RTL\t", state_rtl_.round);
        aes_print_block(&state_rtl_.shift_rows_out[0], 16);
        printf("Round %i shift_rows_out model\t", state_rtl_.round);
        aes_print_block(&state_model_.shift_rows_out[0], 16);
        return status;
      }

      // mix_columns_out
      if (state_rtl_.round < state_model_.num_rounds - 1) {
        status = CompareBlock(state_model_.mix_columns_out,
                              state_rtl_.mix_columns_out, 16);
        if (status) {
          printf("ERROR: mismatch between model and RTL:\n");
          printf("Round %i mix_columns_out RTL\t", state_rtl_.round);
          aes_print_block(&state_rtl_.mix_columns_out[0], 16);
          printf("Round %i mix_columns_out model\t", state_rtl_.round);
          aes_print_block(&state_model_.mix_columns_out[0], 16);
          return status;
        }
      }

      // add_round_key_out
      status = CompareBlock(state_model_.add_round_key_out,
                            state_rtl_.add_round_key_out, 16);
      if (status) {
        printf("ERROR: mismatch between model and RTL:\n");
        printf("Round %i add_round_key_out RTL\t", state_rtl_.round);
        aes_print_block(&state_rtl_.add_round_key_out[0], 16);
        printf("Round %i add_round_key_out model\t", state_rtl_.round);
        aes_print_block(&state_model_.add_round_key_out[0], 16);
        return status;
      }

      // data_out
      if (state_rtl_.done) {
        status = CompareBlock(state_model_.data_out, state_rtl_.data_out, 16);
        if (status) {
          printf("ERROR: mismatch between model and RTL:\n");
          printf("Round %i data_out RTL\t", state_rtl_.round);
          aes_print_block(&state_rtl_.data_out[0], 16);
          printf("Round %i data_out model\t", state_rtl_.round);
          aes_print_block(&state_model_.data_out[0], 16);
          return status;
        }

        // call OpenSSL/BoringSSL to verify
        unsigned char crypto_input[16];
        unsigned char crypto_output[16];
        unsigned char iv[16];
        memset(iv, 0, 16);
        CopyBlock(crypto_input, state_model_.data_in);
        if (!state_model_.cipher_op) {
          crypto_encrypt(crypto_output, iv, crypto_input, 16,
                         state_model_.key_init, state_model_.key_len,
                         kCryptoAesEcb);
        } else {
          crypto_decrypt(crypto_output, iv, crypto_input, 16,
                         state_model_.key_init, state_model_.key_len,
                         kCryptoAesEcb);
        }
        status = CompareBlock(crypto_output, state_rtl_.data_out, 16);
        if (status) {
          printf("ERROR: mismatch between OpenSSL/BoringSSL and RTL:\n");
          printf("Output RTL\t\t\t");
          aes_print_block(&state_rtl_.data_out[0], 16);
          printf("Output OpenSSL/BoringSSL\t");
          aes_print_block(&crypto_output[0], 16);
          aes_print_block(&state_model_.data_in[0], 16);
          aes_print_block(&state_model_.key_init[0], 32);
          return status;
        } else {
          printf("SUCCESS: OpenSSL/BoringSSL matches RTL\n");
        }
      }
    }  // op
  }    // busy

  return 0;
}

void AESModelChecker::UpdateModel() {
  if (state_rtl_.start) {
    // start
    state_model_.cipher_op = state_rtl_.cipher_op;
    state_model_.key_expand_op = state_rtl_.key_expand_op;
    state_model_.key_len = state_rtl_.key_len;
    state_model_.round = -1;
    state_model_.num_rounds = aes_get_num_rounds(state_model_.key_len);
    state_model_.rcon = 0;
    // save data_in for later check of final result
    CopyBlock(state_model_.data_in, state_rtl_.data_in);
  } else if (state_rtl_.busy) {
    // Update model
    if (state_model_.round == -1) {
      // init:
      // - state_q and key_full_q were loaded in last cycle, values now
      // available
      CopyBlock(state_model_.state_q, state_rtl_.state_q);
      CopyKey(state_model_.full_key, state_rtl_.full_key);
      // - state_d gets state_q + round_key
      CopyBlock(state_model_.state_d, state_model_.state_q);
      GetInitRoundKey();
      aes_add_round_key(state_model_.state_d, state_model_.round_key);
      // - backup initial key for later check of final result
      if (!state_model_.key_expand_op) {
        CopyKey(state_model_.key_init, state_model_.full_key);
      }
    } else {
      // rounds
      // 1. update state_q
      CopyBlock(state_model_.state_q, state_model_.state_d);
      // 2. load initial state_d
      CopyBlock(state_model_.state_d, state_model_.state_q);
      // 3. do stuff with state_d
      if (!state_model_.cipher_op || !state_model_.key_expand_op) {  // encrypt
        aes_sub_bytes(state_model_.state_d);
        CopyBlock(state_model_.sub_bytes_out, state_model_.state_d);
        aes_shift_rows(state_model_.state_d);
        CopyBlock(state_model_.shift_rows_out, state_model_.state_d);
        if (state_model_.round < state_model_.num_rounds - 1) {
          aes_mix_columns(state_model_.state_d);
          CopyBlock(state_model_.mix_columns_out, state_model_.state_d);
        }
        aes_key_expand(state_model_.round_key, state_model_.full_key,
                       state_model_.key_len, &state_model_.rcon,
                       state_model_.round);
        aes_add_round_key(state_model_.state_d, state_model_.round_key);
        CopyBlock(state_model_.add_round_key_out, state_model_.state_d);
        if (state_model_.round == state_model_.num_rounds - 1) {
          CopyBlock(state_model_.data_out, state_model_.state_d);
        }
      } else {  // decrypt
        unsigned char mixed_round_key[16];

        aes_inv_sub_bytes(state_model_.state_d);
        CopyBlock(state_model_.sub_bytes_out, state_model_.state_d);
        aes_inv_shift_rows(state_model_.state_d);
        CopyBlock(state_model_.shift_rows_out, state_model_.state_d);
        if (state_model_.round < state_model_.num_rounds - 1) {
          aes_inv_mix_columns(state_model_.state_d);
          CopyBlock(state_model_.mix_columns_out, state_model_.state_d);
        }
        aes_inv_key_expand(state_model_.round_key, state_model_.full_key,
                           state_model_.key_len, &state_model_.rcon,
                           state_model_.round);
        CopyBlock(mixed_round_key, state_model_.round_key);
        if (state_model_.round < state_model_.num_rounds - 1) {
          aes_inv_mix_columns(mixed_round_key);
          CopyBlock(state_model_.round_key, mixed_round_key);
        }
        aes_add_round_key(state_model_.state_d, mixed_round_key);
        CopyBlock(state_model_.add_round_key_out, state_model_.state_d);
        if (state_model_.round == state_model_.num_rounds - 1) {
          CopyBlock(state_model_.data_out, state_model_.state_d);
        }
      }
    }

    // increment round
    state_model_.round++;
  }

  return;
}

void AESModelChecker::GetInitRoundKey() {
  if (state_model_.key_len == 16) {
    CopyBlock(state_model_.round_key, state_model_.full_key);
  } else if (state_model_.key_len == 24) {
    if (!state_model_.key_expand_op) {
      CopyBlock(state_model_.round_key, state_model_.full_key);
    } else {
      CopyBlock(state_model_.round_key, &state_model_.full_key[8]);
    }
  } else {  // state_model_.key_len == 32
    if (!state_model_.key_expand_op) {
      CopyBlock(state_model_.round_key, state_model_.full_key);
    } else {
      CopyBlock(state_model_.round_key, &state_model_.full_key[16]);
    }
  }

  return;
}

void AESModelChecker::MonitorSignals() {
  state_rtl_.cipher_op = rtl_->aes_sim__DOT__cipher_op;
  state_rtl_.key_expand_op = rtl_->aes_sim__DOT__key_expand_op;

  // translate key_len
  int temp = rtl_->aes_sim__DOT__key_len;
  if (temp & 0x1) {
    state_rtl_.key_len = 16;
  } else if (temp & 0x2) {
    state_rtl_.key_len = 24;
  } else if (temp & 0x4) {
    state_rtl_.key_len = 32;
  } else {
    printf("ERROR: Invalid key_len value\n");
  }

  state_rtl_.start = rtl_->aes_sim__DOT__start;
  state_rtl_.init = rtl_->aes_sim__DOT__init;
  state_rtl_.done = rtl_->aes_sim__DOT__done;
  state_rtl_.busy = rtl_->aes_sim__DOT__busy;

  state_rtl_.round = rtl_->aes_sim__DOT__round;

  // helper variables
  AESState *state = &state_rtl_;
  int unsigned *rtl_data_in, *rtl_data_out_d, *rtl_key_full_q;

  // read bytes
  CopyBlock(state->state_d, rtl_->aes_sim__DOT__state_d);
  CopyBlock(state->state_q, rtl_->aes_sim__DOT__state_q);
  CopyBlock(state->sub_bytes_out, rtl_->aes_sim__DOT__sub_bytes_out);
  CopyBlock(state->shift_rows_out, rtl_->aes_sim__DOT__shift_rows_out);
  CopyBlock(state->mix_columns_out, rtl_->aes_sim__DOT__mix_columns_out);
  CopyBlock(state->add_round_key_out, rtl_->aes_sim__DOT__add_round_key_out);
  CopyBlock(state->round_key, rtl_->aes_sim__DOT__round_key);

  // read words - convert to bytes for model - data
  rtl_data_in = &rtl_->aes_sim__DOT__data_in[0];
  rtl_data_out_d = &rtl_->aes_sim__DOT__data_out_d[0];
  for (int i = 0; i < 4; i++) {
    state->data_in[4 * i + 0] = (rtl_data_in[i] & 0x000000FF) >> 0;
    state->data_in[4 * i + 1] = (rtl_data_in[i] & 0x0000FF00) >> 8;
    state->data_in[4 * i + 2] = (rtl_data_in[i] & 0x00FF0000) >> 16;
    state->data_in[4 * i + 3] = (rtl_data_in[i] & 0xFF000000) >> 24;
    state->data_out[4 * i + 0] = (rtl_data_out_d[i] & 0x000000FF) >> 0;
    state->data_out[4 * i + 1] = (rtl_data_out_d[i] & 0x0000FF00) >> 8;
    state->data_out[4 * i + 2] = (rtl_data_out_d[i] & 0x00FF0000) >> 16;
    state->data_out[4 * i + 3] = (rtl_data_out_d[i] & 0xFF000000) >> 24;
  }

  // read words - convert to bytes for model - key
  rtl_key_full_q = &rtl_->aes_sim__DOT__key_full_q[0];
  for (int i = 0; i < 8; i++) {
    state->full_key[4 * i + 0] = (rtl_key_full_q[i] & 0x000000FF) >> 0;
    state->full_key[4 * i + 1] = (rtl_key_full_q[i] & 0x0000FF00) >> 8;
    state->full_key[4 * i + 2] = (rtl_key_full_q[i] & 0x00FF0000) >> 16;
    state->full_key[4 * i + 3] = (rtl_key_full_q[i] & 0xFF000000) >> 24;
  }

  state_rtl_.rcon = rtl_->aes_sim__DOT__rcon_q;

  return;
}

int AESModelChecker::CompareBlock(const unsigned char *sample_a,
                                  const unsigned char *sample_b,
                                  const int len) {
  for (int i = 0; i < len; i++) {
    if (sample_a[i] != sample_b[i]) {
      return 1;
    }
  }

  return 0;
}

void AESModelChecker::CopyBlock(unsigned char *dest, unsigned char *source) {
  memcpy((void *)dest, (const void *)source, (size_t)16);

  return;
}

void AESModelChecker::CopyKey(unsigned char *dest, unsigned char *source) {
  memcpy((void *)dest, (const void *)source, (size_t)32);

  return;
}
