// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Directed sequence to cover the remaining hard to reach RTL hole:
//   - StLenHi->StIdle FSM transition
class hmac_directed_vseq extends hmac_smoke_vseq;
  `uvm_object_utils(hmac_directed_vseq)

  // Constraints
  extern constraint num_trans_c;
  extern constraint msg_c;

  // Standard SV/UVM methods
  extern function new(string name="");
  extern task body();
endclass: hmac_directed_vseq


constraint hmac_directed_vseq::num_trans_c {
  num_trans == 20;
}

constraint hmac_directed_vseq::msg_c {
  msg.size() dist {
    [  1:  62] :/ 1,  // Less than a SHA-2 256 block (512-bit)
    [ 66: 126] :/ 1,  // Less than a SHA-2 384/512 block (1024-bit) or two 512-bit blocks
    [500:1000] :/ 1   // Bigger blocks
  };
}

function hmac_directed_vseq::new(string name="");
  super.new(name);
endfunction : new

task hmac_directed_vseq::body();
  bit [2:0] sha2_pad_fsm_val   = 0;
  string    sha2_pad_fsm_path  =
    "tb.dut.u_prim_sha2_512.gen_multimode_logic.u_prim_sha2_multimode.u_pad.st_q";
  fork begin
    forever begin
      // Wait until the state is well established
      cfg.clk_rst_vif.wait_n_clks(1);
      void'(uvm_hdl_read(sha2_pad_fsm_path, sha2_pad_fsm_val));
      // Wait for StLenHi state
      if (sha2_pad_fsm_val == 'h4) begin
        apply_resets_concurrently();
      end
    end
  end join_none
  super.body();
endtask : body
