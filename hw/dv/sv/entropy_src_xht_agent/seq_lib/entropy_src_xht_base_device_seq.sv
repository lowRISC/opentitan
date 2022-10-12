// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_xht_base_device_seq extends dv_base_seq #(
  .REQ         (entropy_src_xht_item),
  .CFG_T       (entropy_src_xht_agent_cfg),
  .SEQUENCER_T (entropy_src_xht_sequencer)
);

  bit [RNG_BUS_WIDTH - 1:0] window_data_q[$];
  bit [15:0]                test_cnt_hi;
  bit [15:0]                test_cnt_lo;

  `uvm_object_utils(entropy_src_xht_base_device_seq)

  `uvm_object_new

  virtual function void update_item_rsp(entropy_src_xht_item item);
    if (item.req.clear) begin
       window_data_q.delete();
       test_cnt_hi = ENTROPY_SRC_XHT_RSP_DEFAULT.test_cnt_hi;
       test_cnt_lo = ENTROPY_SRC_XHT_RSP_DEFAULT.test_cnt_lo;
    end else begin
      if (item.req.active && item.req.entropy_bit_valid) begin
        window_data_q.push_back(item.req.entropy_bit);
        if (window_data_q.size() == item.req.health_test_window) begin
          // Use a hash function to create output values that cover the
          // complete range of test_cnt's, but also depend deterministically
          // on the window data.
          `uvm_info(`gfn, "Generating SHA3 hash", UVM_FULL)
          test_cnt_hash(test_cnt_hi, test_cnt_lo);
        end
      end
      if (item.req.active && item.req.window_wrap_pulse) begin
        window_data_q.delete();
      end
    end

    item.rsp.test_cnt_hi = test_cnt_hi;
    item.rsp.test_cnt_lo = test_cnt_lo;
    item.rsp.test_fail_hi_pulse = test_cnt_hi > item.req.thresh_hi;
    item.rsp.test_fail_lo_pulse = test_cnt_lo < item.req.thresh_lo;
    item.rsp.continuous_test = 1'b0;
  endfunction

  // For generating hypothetical HT results here we apply three basic requirements
  // 1. The outputs should be deterministic with respect to the input data
  // 2. The test outputs should have good coverage over the whole range of test_cnts (16 bits)
  // 3. The low output should be less than or equal the high output.
  // Given these three constraints, this function arbitrarily generates a SHA3 hash of the input
  // data, and extracts the lowest 32 bits of the digest to create two synthetic test_cnt outputs.
  function void test_cnt_hash(output bit [15:0] hi, output bit [15:0] lo);
    localparam int ShaWidth = 384;
    localparam int RngWordsPerByte = 8/RNG_BUS_WIDTH;

    bit [7:0]  sha_msg[];
    int        msg_size;
    int        msg_idx = 0;
    bit [7:0]  sha_digest[ShaWidth / 8];
    int        rng_cntr = 0;
    bit        whole_byte;
    bit [7:0]  sha_byte = '0;
    bit [15:0] output_a, output_b;

    // The "message" will be equal to the number of bytes in the window
    // rounding up to include any partial bytes.
    msg_size = (window_data_q.size() + RngWordsPerByte - 1) / RngWordsPerByte;
    sha_msg = new[msg_size];

    for (int i = 0; i < window_data_q.size(); i++) begin
      sha_byte = {sha_byte[(8 - RNG_BUS_WIDTH - 1):0], window_data_q[i]};
      rng_cntr++;
      whole_byte = (rng_cntr == RngWordsPerByte);
      // Add data to the message whenever we have a whole byte,
      // or if there is ever a dangling nibble.
      if (whole_byte || (i == (window_data_q.size() - 1)) ) begin
        sha_msg[msg_idx] = sha_byte;
        msg_idx++;
        rng_cntr = 0;
      end
    end

    digestpp_dpi_pkg::c_dpi_sha3_384(sha_msg, msg_idx, sha_digest);
    // Arbitrarily capture the lowest 4 bytes as a pair of outputs.
    output_a = {sha_digest[3], sha_digest[2]};
    output_b = {sha_digest[1], sha_digest[0]};

    hi = (output_a < output_b) ? output_b : output_a;
    lo = (output_a < output_b) ? output_a : output_b;

  endfunction

  virtual task body();
    entropy_src_xht_item req_q[$];
    `uvm_info(`gfn, "Starting seq", UVM_HIGH)
    fork
      forever begin : get_req
        p_sequencer.req_analysis_fifo.get(req);
        req_q.push_back(req);
      end : get_req
      forever begin : send_rsp
        `uvm_info(`gfn, "Waiting for activity", UVM_DEBUG)
        `DV_SPINWAIT_EXIT(wait(req_q.size());, wait(cfg.in_reset))
        if (cfg.in_reset) begin
          `uvm_info(`gfn, "Reset detected!", UVM_DEBUG)
          test_cnt_hi = ENTROPY_SRC_XHT_RSP_DEFAULT.test_cnt_hi;
          test_cnt_lo = ENTROPY_SRC_XHT_RSP_DEFAULT.test_cnt_lo;
          wait (!cfg.in_reset)
          req_q.delete();
          window_data_q.delete();
        end else begin
          `uvm_info(`gfn, "Got Item!", UVM_DEBUG)
          rsp = req_q.pop_front();
          start_item(rsp);
          update_item_rsp(rsp);
          finish_item(rsp);
          get_response(rsp);
        end
      end : send_rsp
    join
  endtask

endclass
