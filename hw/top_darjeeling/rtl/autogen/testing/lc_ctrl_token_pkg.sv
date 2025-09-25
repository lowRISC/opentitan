// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Life cycle state encoding definition.
//
// ------------------- W A R N I N G: A U T O - G E N E R A T E D   C O D E !! -------------------//
// PLEASE DO NOT HAND-EDIT THIS FILE. IT HAS BEEN AUTO-GENERATED

package lc_ctrl_token_pkg;

  import lc_ctrl_state_pkg::lc_token_t;

  ///////////////////////////////////////////
  // Hashed RAW unlock and all-zero tokens //
  ///////////////////////////////////////////

  parameter lc_token_t AllZeroToken = {
    128'h0
  };
  parameter lc_token_t RndCnstRawUnlockToken = {
    128'hE4225DC332EA1FDA63B4C524556ED4D4
  };
  parameter lc_token_t AllZeroTokenHashed = {
    128'h3852305BAECF5FF1D5C1D25F6DB9058D
  };
  parameter lc_token_t RndCnstRawUnlockTokenHashed = {
    128'hF51C9CB753A5AADEA5FDC7D23AB29F6D
  };

endpackage : lc_ctrl_token_pkg
