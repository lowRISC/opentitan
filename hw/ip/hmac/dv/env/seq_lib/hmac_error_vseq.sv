// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// this sequence test error cases in hmac, and making sure the core is not locked

class hmac_error_vseq extends hmac_long_msg_vseq;
  `uvm_object_utils(hmac_error_vseq)
  `uvm_object_new

  function void pre_randomize();
    this.legal_seq_c.constraint_mode(0);
  endfunction

endclass : hmac_error_vseq
