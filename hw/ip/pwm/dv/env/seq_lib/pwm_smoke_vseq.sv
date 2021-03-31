// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// smoke test vseq: accessing a major datapath within the pwm
class pwm_smoke_vseq extends pwm_rx_tx_vseq;
  `uvm_object_utils(pwm_smoke_vseq)
  `uvm_object_new

endclass : pwm_smoke_vseq
