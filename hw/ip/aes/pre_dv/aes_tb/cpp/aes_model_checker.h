// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_IP_AES_PRE_DV_AES_TB_CPP_AES_MODEL_CHECKER_H_
#define OPENTITAN_HW_IP_AES_PRE_DV_AES_TB_CPP_AES_MODEL_CHECKER_H_

#include <cstdint>
#include "Vaes_sim.h"
#include "crypto.h"

#define DEBUG_LEVEL 0

struct AESState {
 public:
  bool op;
  crypto_mode_t mode;
  bool cipher_op;
  bool key_expand_op;
  int key_len;
  bool start;
  bool init;
  bool done;
  bool busy;
  bool stall;
  bool step;
  int round;
  int num_rounds;
  unsigned char key_init[32];
  unsigned char iv[16];
  unsigned char data_in[16];
  unsigned char state_d[16];
  unsigned char state_q[16];
  unsigned char sub_bytes_out[16];
  unsigned char shift_rows_out[16];
  unsigned char mix_columns_out[16];
  unsigned char add_round_key_out[16];
  unsigned char full_key[32];
  unsigned char round_key[16];
  unsigned char rcon;
  unsigned char data_out[16];
};

class AESModelChecker {
 public:
  AESModelChecker(Vaes_sim *rtl);

  int CheckModel();

 private:
  int Compare();
  void Print();
  void UpdateModel();
  void GetInitRoundKey();
  void MonitorSignals();
  int CompareBlock(const unsigned char *sample_a, const unsigned char *sample_b,
                   const int len);
  void CopyBlock(unsigned char *dest, unsigned char *source);
  void CopyKey(unsigned char *dest, unsigned char *source);
  Vaes_sim *rtl_;
  AESState state_model_;
  AESState state_rtl_;
};

#endif  // OPENTITAN_HW_IP_AES_PRE_DV_AES_TB_CPP_AES_MODEL_CHECKER_H_
