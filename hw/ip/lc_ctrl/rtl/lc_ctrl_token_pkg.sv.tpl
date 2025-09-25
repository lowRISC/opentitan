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

<% token_size = lc_st_enc.config['token_size'] %>\
% for token in lc_st_enc.config['tokens']:
  parameter lc_token_t ${token['name']} = {
    ${"{0:}'h{1:0X}".format(token_size, token['value'])}
  };
% endfor

endpackage : lc_ctrl_token_pkg
