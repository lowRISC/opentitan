// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

#ifndef OPENTITAN_HW_IP_AES_PRE_DV_AES_TB_CPP_AES_TLUL_INTERFACE_H_
#define OPENTITAN_HW_IP_AES_PRE_DV_AES_TB_CPP_AES_TLUL_INTERFACE_H_

#include <cstdint>
#include "Vaes_sim.h"

struct TLI {
 public:
  bool a_valid;
  uint8_t a_opcode;
  uint8_t a_param;
  uint8_t a_size;
  uint8_t a_source;
  uint32_t a_address;
  uint8_t a_mask;
  uint32_t a_data;
  uint32_t a_user;
  bool d_ready;
};

struct TLO {
 public:
  bool d_valid;
  uint8_t d_opcode;
  uint8_t d_param;
  uint8_t d_size;
  uint8_t d_source;
  uint8_t d_sink;
  uint32_t d_data;
  uint32_t d_user;
  bool d_error;
  bool a_ready;
};

struct EXP_RESP {
 public:
  uint32_t mask;
  uint32_t exp_resp;
};

class AESTLULInterface {
 public:
  AESTLULInterface(Vaes_sim *rtl);

  /**
   * Handle TLUL interface
   *
   * Issue next transaction if there are any and the DUT is ready.
   */
  void HandleInterface();

  /**
   * Read the number of transactions issued
   *
   * @return The number of transactions issued
   */
  int GetNumTransactions();

  /**
   * Read the number of expected responses received
   *
   * @return The number of received expected responses
   */
  int GetNumResponses();

  /**
   * Check if the interface has finished all specified transactions
   *
   * @return True if all transactions have been finished, false otherwise
   */
  bool StatusDone();

 private:
  void GetTransaction(bool get_next);
  bool CheckReady();
  bool CheckResp();
  void MonitorSignals();
  void DriveSignals();
  Vaes_sim *rtl_;
  TLI tl_i_;
  TLO tl_o_;
  bool got_handshake_a_;
  bool got_handshake_d_;
  int num_transactions_;
  int num_responses_;
};

#endif  // OPENTITAN_HW_IP_AES_PRE_DV_AES_TB_CPP_AES_TLUL_INTERFACE_H_
