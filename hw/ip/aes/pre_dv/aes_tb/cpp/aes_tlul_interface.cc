// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#include "aes_tlul_interface.h"

#include "aes_tlul_sequence_0.h"
//#include "aes_tlul_sequence_1.h"

AESTLULInterface::AESTLULInterface(Vaes_sim *rtl) : rtl_(rtl) {
  rtl_->tl_i[0] = 0;
  rtl_->tl_i[1] = 0;
  rtl_->tl_i[2] = 0;
  rtl_->tl_i[3] = 0;
  tl_i_.a_valid = false;
  tl_i_.a_opcode = 0;
  tl_i_.a_size = 0;
  tl_i_.a_address = 0;
  tl_i_.a_address = 0;
  tl_i_.a_mask = 0;
  tl_i_.a_data = 0;
  tl_i_.a_data = 0;
  tl_i_.d_ready = false;
  tl_o_.d_valid = false;
  tl_o_.d_opcode = 0;
  tl_o_.d_param = 0;
  tl_o_.d_size = 0;
  tl_o_.d_source = 0;
  tl_o_.d_sink = 0;
  tl_o_.d_data = 0;
  tl_o_.d_user = 0;
  tl_o_.d_error = 0;
  tl_o_.a_ready = false;
  got_handshake_a_ = false;
  got_handshake_d_ = false;
  num_transactions_ = -1;
  num_responses_ = 0;
}

void AESTLULInterface::HandleInterface() {
  bool interface_ready;
  bool got_exp_resp;

  MonitorSignals();
  got_exp_resp = CheckResp();
  interface_ready = CheckReady();

  // prepare interface for transaction only if the interface is ready
  // repeat previous transaction if we did not get the expected response
  if (interface_ready) {
    GetTransaction(got_exp_resp);
  }

  DriveSignals();

  return;
}

int AESTLULInterface::GetNumTransactions() { return num_transactions_; }

int AESTLULInterface::GetNumResponses() { return num_responses_; }

bool AESTLULInterface::StatusDone() {
  bool done = false;

  if ((num_responses_ >= num_responses_max) &&
      (num_transactions_ >= num_transactions_max)) {
    done = true;
  }

  return done;
}

void AESTLULInterface::GetTransaction(bool get_next) {
  if (get_next) {
    num_transactions_++;
  }
  if (num_transactions_ < num_transactions_max) {
    tl_i_ = tl_i_transactions[num_transactions_];
  } else {
    tl_i_ = {false, 0, 0, 0, 0, 0, 0, 0, 0, false};
  }

  return;
}

bool AESTLULInterface::CheckReady() {
  bool ready = false;

  // check for handshakes
  if (tl_i_.a_valid && tl_o_.a_ready) {
    got_handshake_a_ = true;
  }
  if (tl_i_.d_ready && tl_o_.d_valid) {
    got_handshake_d_ = true;
  }

  // deassert valid/ready
  if (got_handshake_a_) {
    tl_i_.a_valid = false;
  }
  if (got_handshake_d_) {
    tl_i_.d_ready = false;
  }

  // we cannot drive the next transaction unless
  // - we completed both handshakes
  // - or were not driving before
  // both cases are given if a_valid == d_valid == false
  if (!tl_i_.a_valid && !tl_i_.d_ready) {
    got_handshake_a_ = false;
    got_handshake_d_ = false;
    ready = true;
  }

  return ready;
}

bool AESTLULInterface::CheckResp() {
  bool match = false;
  EXP_RESP exp_resp = tl_o_exp_resp[num_responses_];

  // do not check if not waiting for a response
  if (!tl_i_.d_ready) {
    match = true;
  }
  // only do the check during a data handshake
  else if (tl_i_.d_ready && tl_o_.d_valid) {
    // non-read operations are not checked
    if (tl_i_.a_opcode != 4) {
      match = true;
    }
    // do the actual check
    else if ((exp_resp.mask & tl_o_.d_data) ==
             (exp_resp.mask & exp_resp.exp_resp)) {
      match = true;
      num_responses_++;
    }
  }

  return match;
}

void AESTLULInterface::MonitorSignals() {
  // just montior handshakes, error and resp data
  tl_o_.d_valid = (rtl_->tl_o[2] & 0x8) >> 3;
  tl_o_.d_data =
      ((rtl_->tl_o[1] & 0x3FFFF) << 14) | ((rtl_->tl_o[0] >> 18) & 0x3FFF);
  tl_o_.d_error = (rtl_->tl_o[0] & 0x2) >> 1;
  tl_o_.a_ready = rtl_->tl_o[0] & 0x1;

  return;
}

void AESTLULInterface::DriveSignals() {
  // clear
  rtl_->tl_i[3] = 0;
  rtl_->tl_i[2] = 0;
  rtl_->tl_i[1] = 0;
  rtl_->tl_i[0] = 0;

  // tl_i bits:
  // a_valid   - 1   - [101]    - [3][5]
  // a_opcode  - 3   - [100:98] - [3][4:2]
  // a_param   - 3   - [97:95]  - [2][31] - [3][1:0]
  // a_size    - 2   - [94:93]  - [2][30:29]
  // a_source  - 8   - [92:85]  - [2][28:21]
  // a_address - 32  - [84:53]  - [1][31:21] - [2][20:0]
  // a_mask    - 4   - [52:49]  - [1][20:17]
  // a_data    - 32  - [48:17]  - [0][31:17] - [1][16:0]
  // a_user    - 16  - [16:1]   - [0][16:1]
  // d_ready   - 1   - [0]      - [0][0]

  // set required bits
  rtl_->tl_i[3] |= (tl_i_.a_valid & 0x1) << 5;
  rtl_->tl_i[3] |= (tl_i_.a_opcode & 0x7) << 2;
  // param = 0
  rtl_->tl_i[2] |= (tl_i_.a_size & 0x3) << 29;
  // source = 0
  rtl_->tl_i[2] |= (tl_i_.a_address & 0xFFFFF800) >> 11;
  rtl_->tl_i[1] |= (tl_i_.a_address & 0x000007FF) << 21;
  rtl_->tl_i[1] |= (tl_i_.a_mask & 0xF) << 17;
  rtl_->tl_i[1] |= (tl_i_.a_data & 0xFFFF8000) >> 15;
  rtl_->tl_i[0] |= (tl_i_.a_data & 0x00007FFF) << 17;
  // a_user = 0
  rtl_->tl_i[0] |= (tl_i_.d_ready & 0x1);

  return;
}
