// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Smoke test: brings the DUT out of reset (via dut_init()/rram_ctrl_init()), then plays otp_ctrl
// on the OTP macro interface: Init, followed by reads and writes of a few random OTP locations.
// Software and host traffic are still TODO(#31293).
class rram_ctrl_smoke_vseq extends rram_ctrl_base_vseq;
  `uvm_object_utils(rram_ctrl_smoke_vseq)

  extern function new(string name="");
  extern task body();
endclass : rram_ctrl_smoke_vseq

function rram_ctrl_smoke_vseq::new(string name="");
  super.new(name);
endfunction : new

task rram_ctrl_smoke_vseq::body();
  // TODO(#31293): add software controller and host traffic, in parallel with the OTP traffic.
  otp_macro_init();
  otp_macro_rand_rw(num_trans);
endtask : body
