// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class entropy_src_xht_base_device_seq extends dv_base_seq #(
  .REQ         (entropy_src_xht_item),
  .CFG_T       (entropy_src_xht_agent_cfg),
  .SEQUENCER_T (entropy_src_xht_sequencer)
);

  bit [`RNG_BUS_WIDTH - 1:0] window_data_q[$];
  bit [15:0]                test_cnt_hi;
  bit [15:0]                test_cnt_lo;

  `uvm_object_utils(entropy_src_xht_base_device_seq)

  `uvm_object_new

  virtual function void update_item_rsp(entropy_src_xht_item item);
    if (item.req.clear) begin
       window_data_q.delete();
       test_cnt_hi = ENTROPY_SRC_XHT_META_RSP_DEFAULT.test_cnt_hi;
       test_cnt_lo = ENTROPY_SRC_XHT_META_RSP_DEFAULT.test_cnt_lo;
    end else begin
      if (item.req.active && item.entropy_valid) begin
        window_data_q.push_back(item.entropy_bits);
        if (window_data_q.size() == item.health_test_window) begin
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

    // RngBytesPerWord indicates how many full bytes are in each RNG_BUS_WIDTH chunk,
    // and RngBitsRemainder is the number of remaining bits if RNG_BUS_WIDTH is not a multiple of 8.
    localparam int RngBytesPerWord   = `RNG_BUS_WIDTH / 8;
    localparam int RngBitsRemainder  = `RNG_BUS_WIDTH % 8;

    bit [7:0]  sha_msg[];
    int        msg_idx = 0; // Use msg_idx consistently for adding to sha_msg
    bit [7:0]  sha_digest[ShaWidth / 8];
    bit [7:0]  sha_byte_accumulator = '0; // Used to accumulate bits for partial bytes
    int        bits_in_accumulator = 0;   // Count of bits in sha_byte_accumulator
    bit [15:0] output_a, output_b;

    // The "message" will be equal to the number of bytes in the window.
    // This calculation needs to account for partial bytes at the end.
    // Total bits = window_data_q.size() * `RNG_BUS_WIDTH
    // Total bytes = ceil(Total bits / 8)
    int msg_size = (window_data_q.size() * `RNG_BUS_WIDTH + 7) / 8;
    sha_msg = new[msg_size];

    for (int i = 0; i < window_data_q.size(); i++) begin
      bit [`RNG_BUS_WIDTH-1:0] current_rng_word = window_data_q[i];

      // Case 1: RNG_BUS_WIDTH is a multiple of 8
      // Directly extract full bytes. No bit accumulation needed.
      if (RngBitsRemainder == 0) begin
        for (int j = 0; j < RngBytesPerWord; j++) begin
          sha_msg[msg_idx] = current_rng_word[j*8 +: 8];
          msg_idx++;
        end
      end
      // Case 2: RNG_BUS_WIDTH is not a multiple of 8
      // We need to accumulate bits to form full bytes.
      else begin
        // Add the current RNG word's bits to the accumulator.
        // This handles both `RNG_BUS_WIDTH < 8` and `RNG_BUS_WIDTH > 8` (with remainder) cases.
        sha_byte_accumulator = (sha_byte_accumulator >> `RNG_BUS_WIDTH) |
                                // Shift old accumulator bits to make room and add new
                               (current_rng_word << bits_in_accumulator);
        bits_in_accumulator += `RNG_BUS_WIDTH;

        // Extract full bytes as long as there are 8 or more bits in the accumulator
        while (bits_in_accumulator >= 8) begin
          sha_msg[msg_idx] = sha_byte_accumulator[7:0];
          sha_byte_accumulator = sha_byte_accumulator >> 8;
          bits_in_accumulator -= 8;
          msg_idx++;
        end
      end
    end

    // After the loop, if there are any remaining bits in the accumulator
    // (only if RngBitsRemainder != 0),they form the last (partial) byte of the message.
    if (bits_in_accumulator > 0) begin
      sha_msg[msg_idx] = sha_byte_accumulator;
      msg_idx++;
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
          test_cnt_hi = ENTROPY_SRC_XHT_META_RSP_DEFAULT.test_cnt_hi;
          test_cnt_lo = ENTROPY_SRC_XHT_META_RSP_DEFAULT.test_cnt_lo;
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
