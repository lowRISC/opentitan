// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Read every partition through the software config window, then the window past the last partition
//
// Random words of each unbuffered partition are first programmed with nonzero data through the DAI.
// A read in an unbuffered partition returns data. A read anywhere else gets an error response, and
// each one is followed by a STATUS read and a read of a programmed word, to check that the error
// changed no status and that the window still returns the right data.
class otp_ctrl_sw_window_access_vseq extends otp_ctrl_base_vseq;
  // Number of words programmed in each unbuffered partition before the window reads
  rand int unsigned num_prog_words;

  // Number of random words read in each range, on top of its first and last word
  rand int unsigned num_rand_words;

  // OTP byte addresses of the programmed words, filled by body
  local int unsigned prog_words[$];

  `uvm_object_utils(otp_ctrl_sw_window_access_vseq)

  constraint num_prog_words_c {
    num_prog_words inside {[1:4]};
  }

  constraint num_rand_words_c {
    num_rand_words inside {[1:4]};
  }

  // Standard SV/UVM methods
  extern function new(string name = "");
  extern task body();

  // Class specific methods

  // Program num_prog_words random words of an unbuffered partition with random nonzero data
  //
  // Digest words and Zeroize markers are skipped, because a DAI write there is an access error.
  extern local task program_words(int unsigned part_idx);

  // Read the first word, the last word and num_rand_words random words of a range of OTP bytes
  //
  //    start_addr: OTP byte address of the first word of the range
  //    end_addr:   OTP byte address just past the last word of the range
  extern local task window_rd_range(int unsigned start_addr, int unsigned end_addr);

  // Read one word through the window and check the response
  //
  // The read expects an error unless the window maps dai_addr. After an error, read STATUS and then
  // a random programmed word.
  extern local task window_rd(int unsigned dai_addr);
endclass : otp_ctrl_sw_window_access_vseq


function otp_ctrl_sw_window_access_vseq::new(string name = "");
  super.new(name);
endfunction : new

task otp_ctrl_sw_window_access_vseq::body();
  int unsigned part_order[$];

  prog_words.delete();
  for (int unsigned i = 0; i < NumPart; i++) begin
    part_order.push_back(i);
    if (is_sw_part_idx(i)) begin
      program_words(i);
    end
  end
  part_order.shuffle();

  foreach (part_order[i]) begin
    int unsigned part_idx  = part_order[i];
    part_idx_e   part_name = part_idx_e'(part_idx);

    `uvm_info(`gfn, $sformatf("Reading partition %0s through the window", part_name.name()),
              UVM_LOW)
    window_rd_range(PartInfo[part_idx].offset, get_part_end_addr(part_idx));
  end

  if (get_part_end_addr(NumPart - 1) < SW_WINDOW_SIZE) begin
    `uvm_info(`gfn, "Reading the window past the last partition", UVM_LOW)
    window_rd_range(get_part_end_addr(NumPart - 1), SW_WINDOW_SIZE);
  end
endtask : body

task otp_ctrl_sw_window_access_vseq::program_words(int unsigned part_idx);
  int unsigned words[$];
  int unsigned end_addr = get_part_end_addr(part_idx);

  for (int unsigned addr = PartInfo[part_idx].offset; addr < end_addr; addr += 4) begin
    if (!is_digest(addr) && !touches_zeroize_marker(addr)) begin
      words.push_back(addr);
    end
  end
  words.shuffle();

  foreach (words[i]) begin
    bit [TL_DW-1:0] wdata;

    if (i == num_prog_words) begin
      break;
    end
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(wdata, wdata != 0;)
    dai_wr(words[i], wdata);
    prog_words.push_back(words[i]);
  end
endtask : program_words

task otp_ctrl_sw_window_access_vseq::window_rd_range(int unsigned start_addr,
                                                     int unsigned end_addr);
  window_rd(start_addr);
  window_rd(end_addr - 4);
  repeat (num_rand_words) begin
    window_rd($urandom_range(start_addr / 4, end_addr / 4 - 1) * 4);
  end
endtask : window_rd_range

task otp_ctrl_sw_window_access_vseq::window_rd(int unsigned dai_addr);
  bit [TL_DW-1:0] rdata;
  bit             mapped = is_sw_window_mapped(dai_addr);

  `uvm_info(`gfn,
            $sformatf("Window read at OTP byte address 0x%0h, expecting %0s",
                      dai_addr, mapped ? "data" : "an error response"),
            UVM_HIGH)
  tl_access(.addr(cfg.ral.get_addr_from_offset(get_sw_window_offset(dai_addr))), .write(0),
            .data(rdata), .exp_err_rsp(!mapped), .blocking(1));

  if (!mapped) begin
    uvm_reg_data_t status;

    // The scoreboard checks STATUS against its prediction, which an unmapped read leaves unchanged
    csr_rd(.ptr(ral.status), .value(status));
    window_rd(prog_words[$urandom_range(0, prog_words.size() - 1)]);
  end
endtask : window_rd
