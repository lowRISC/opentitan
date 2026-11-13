// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class rram_ctrl_smoke_vseq extends rram_ctrl_base_vseq;
  `uvm_object_utils(rram_ctrl_smoke_vseq)

  extern function new(string name="");
  extern task body();
endclass : rram_ctrl_smoke_vseq

function rram_ctrl_smoke_vseq::new(string name="");
  super.new(name);
endfunction : new

task rram_ctrl_smoke_vseq::body();
  otp_macro_rsp_seq_item rsp;
  bit                    saw_reset;

  // TODO(#31293): add software controller and host traffic, in parallel with the OTP traffic.
  otp_macro_init(rsp);
  otp_macro_rand_rw(.num_locations(50), .saw_reset(saw_reset));
endtask : body
