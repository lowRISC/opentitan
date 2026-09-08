// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Which of rram_ctrl_otp_key_if's two independent DUT key-request lines a
// rram_ctrl_otp_key_driver instance answers.
typedef enum bit {
  RramCtrlOtpKeyAddr,
  RramCtrlOtpKeyData
} rram_ctrl_otp_key_phase_e;

// Answers one of rram_ctrl_otp_key_if's two independent DUT key-request lines (address or data
// scrambling), selected by `phase_kind`. The environment instantiates one of each, both driving
// the same interface: safe because the DUT will never assert addr_req and data_req at the same
// time.
//
// Randomizes a single key/rand_key pair once and answers every request with it for the life of
// the test, matching real key-derivation semantics (the key doesn't change without
// re-provisioning).
class rram_ctrl_otp_key_driver extends uvm_component;
  `uvm_component_utils(rram_ctrl_otp_key_driver)

  // Which request line this instance answers. Set by the env right after construction, before
  // the run phase starts.
  rram_ctrl_otp_key_phase_e phase_kind;

  virtual rram_ctrl_otp_key_if vif;

  rand bit [KeyWidth-1:0] key;
  rand bit [KeyWidth-1:0] rand_key;

  // Number of otp_clk cycles to wait after a request before asserting ack. Re-randomized for
  // every request: a real otp_ctrl's response latency isn't fixed, and the DUT must tolerate
  // any value here. Only the ack *deassertion* is same-cycle-constrained (see
  // prim_sync_reqack.sv's SyncReqAckAckNeedsReq). The assertion delay is unconstrained.
  rand int unsigned ack_delay_cycles;
  constraint ack_delay_cycles_c { ack_delay_cycles inside {[0:5]}; }

  extern function new(string name, uvm_component parent);
  extern function void build_phase(uvm_phase phase);
  extern task run_phase(uvm_phase phase);

  // Waits for key requests and responds with scrambling keys.
  extern task provide_scrambling_keys();
endclass : rram_ctrl_otp_key_driver

function rram_ctrl_otp_key_driver::new(string name, uvm_component parent);
  super.new(name, parent);
endfunction : new

function void rram_ctrl_otp_key_driver::build_phase(uvm_phase phase);
  super.build_phase(phase);
  if (!uvm_config_db#(otp_key_vif_t)::get(this, "", "otp_key_vif", vif)) begin
    `uvm_fatal(`gfn, "Failed to get otp_key_vif from uvm_config_db")
  end

  // key/rand_key are sized KeyWidth but drive fields sized NvmKeyWidth. Catch a mismatch
  // instead of silently truncating/zero-extending.
  `DV_CHECK_EQ_FATAL(KeyWidth, otp_ctrl_pkg::NvmKeyWidth,
                     "rram_ctrl_pkg::KeyWidth doesn't match otp_ctrl_pkg::NvmKeyWidth")
endfunction : build_phase

task rram_ctrl_otp_key_driver::run_phase(uvm_phase phase);
  `DV_CHECK_RANDOMIZE_FATAL(this)

  forever begin
    // Idle output state, driven both at startup and on every reset.
    vif.host_cb.rsp.addr_ack   <= 1'b0;
    vif.host_cb.rsp.data_ack   <= 1'b0;
    vif.host_cb.rsp.seed_valid <= 1'b0;
    vif.host_cb.rsp.key        <= '0;
    vif.host_cb.rsp.rand_key   <= '0;

    wait (vif.rst_n);

    // Race handling one request against reset so it restarts instead of driving stale state.
    fork
      provide_scrambling_keys();
      begin : reset_kill
        wait (!vif.rst_n);
      end
    join_any
    disable fork;
  end
endtask : run_phase

task rram_ctrl_otp_key_driver::provide_scrambling_keys();
  bit req;

  // Wait for a new request, sampled once per otp_clk cycle via the clocking block, which
  // avoids racing the DUT's own posedge-triggered updates.
  do begin
    @(vif.host_cb);
    req = (phase_kind == RramCtrlOtpKeyAddr) ? vif.host_cb.req.addr_req :
                                               vif.host_cb.req.data_req;
  end while (!req);

  // Pick how many cycles to wait before acking. A real otp_ctrl's response latency isn't
  // fixed and the DUT must tolerate any value here.
  `DV_CHECK_MEMBER_RANDOMIZE_FATAL(ack_delay_cycles)
  repeat (ack_delay_cycles) @(vif.host_cb);

  `uvm_info("sending_key", $sformatf(
      "OTP %0s key applied to DUT: key: %0x, rand_key: %0x, delay: %0d",
      phase_kind.name(), key, rand_key, ack_delay_cycles), UVM_MEDIUM)
  vif.host_cb.rsp.key        <= key;
  vif.host_cb.rsp.rand_key   <= rand_key;
  vif.host_cb.rsp.seed_valid <= 1'b1;
  if (phase_kind == RramCtrlOtpKeyAddr) begin
    vif.host_cb.rsp.addr_ack <= 1'b1;
  end else begin
    vif.host_cb.rsp.data_ack <= 1'b1;
  end

  // Wait for next clock edge to lower the ack and seed_valid.
  @(vif.host_cb);

  if (phase_kind == RramCtrlOtpKeyAddr) begin
    vif.host_cb.rsp.addr_ack <= 1'b0;
  end else begin
    vif.host_cb.rsp.data_ack <= 1'b0;
  end
  vif.host_cb.rsp.seed_valid <= 1'b0;
endtask : provide_scrambling_keys
