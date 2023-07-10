// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for prim_present, drives various test vectors into all
// implementations and compares intermediate and final output against
// C-reference model, for both encryption and decryption.
//
// This testbench only tests the PRESENT block cipher in its 64-bit data
// and 128-bit key configuration, other configurations with different sets of
// widths remain untested.

module prim_present_tb;
  `include "dv_macros.svh"

  import crypto_dpi_present_pkg::MaxRounds;
  import crypto_dpi_present_pkg::MaxKeyWidth;
  import crypto_dpi_present_pkg::DataWidth;

//////////////////////////////////////////////////////
// config
//////////////////////////////////////////////////////

`ifndef KEY_WIDTH
  `define KEY_WIDTH 128
`endif

  // Key width can be set with a define, but must be 80 or 128
  localparam int unsigned KeyWidth = `KEY_WIDTH;

  // used to index the data arrays
  localparam bit Encrypt = 1'b0;
  localparam bit Decrypt = 1'b1;
  localparam bit SingleRound = 1'b0;
  localparam bit FullRound   = 1'b1;

  localparam int NumDuts = 4;

  // This bit can be set from the command line to indicate that we are running a smoke regression,
  // and to run just a single iteration of the test.
  // This helps drastically reduce runtimes in the CI flows.
  bit smoke_test;

//////////////////////////////////////////////////////
// DUTs for both encryption and decryption
//////////////////////////////////////////////////////

  // data_in[0]: encryption, data_in[1]: decryption.
  // Same scheme used for key_in, data_out, key_out.
  logic [1:0][NumDuts-1:0][DataWidth-1:0] data_in;
  logic [1:0][NumDuts-1:0][KeyWidth-1 :0] key_in;
  logic [1:0][NumDuts-1:0][4:0]           idx_in;
  logic [1:0][NumDuts-1:0][DataWidth-1:0] data_out;
  logic [1:0][NumDuts-1:0][KeyWidth-1 :0] key_out;
  logic [1:0][NumDuts-1:0][4:0]           idx_out;

  for (genvar j = 0; j < 2; j++) begin : gen_encrypt_decrypt
    for (genvar k = 0; k < 2; k++) begin : gen_duts
      localparam int NumRounds = (k > 0) ? MaxRounds : 1;
      prim_present #(
        .DataWidth     ( DataWidth ),
        .KeyWidth      ( KeyWidth  ),
        .NumRounds     ( MaxRounds ),
        .NumPhysRounds ( NumRounds ),
        .Decrypt       ( j         )
      ) dut (
        .data_i     ( data_in[j][k]  ),
        .key_i      ( key_in[j][k]   ),
        .idx_i      ( idx_in[j][k]   ),
        .data_o     ( data_out[j][k] ),
        .key_o      ( key_out[j][k]  ),
        .idx_o      ( idx_out[j][k]  )
      );
    end
  end

//////////////////////////////////////////////////////
// API called by the testbench to drive/check stimulus
//////////////////////////////////////////////////////

  // Top level API task that should be called to run a full pass
  // of encryption and decryption on some input data and key.
  task automatic test_present(bit [DataWidth-1:0] plaintext,
                              bit [KeyWidth-1:0]  key);

    bit [DataWidth-1:0] ciphertext;
    check_encryption(plaintext, key, ciphertext);
    check_decryption(ciphertext, key, key_out[Encrypt]);
  endtask


  // Helper task to drive plaintext and key into each encryption instance.
  // Calls a subroutine to perform checks on the outputs (once they are available).
  task automatic check_encryption(input bit  [DataWidth-1:0] plaintext,
                                  input bit  [KeyWidth-1:0]  key,
                                  output bit [DataWidth-1:0] expected_ciphertext);

    // Drive input into encryption instances.
    data_in[Encrypt] <= '{default: plaintext};
    key_in[Encrypt]  <= '{default: key};
    idx_in[Encrypt]  <= '{default: 5'd1};

    // Iterate MaxRounds times for the single-round instance.
    for (int unsigned i = 0; i < MaxRounds-1; i++) begin
      #10ns;
      data_in[Encrypt][SingleRound] <= data_out[Encrypt][SingleRound];
      key_in[Encrypt][SingleRound]  <= key_out[Encrypt][SingleRound];
      idx_in[Encrypt][SingleRound]  <= idx_out[Encrypt][SingleRound];
    end

    // Wait a bit for the DUTs to finish calculations.
    #10ns;

    crypto_dpi_present_pkg::sv_dpi_present_encrypt(plaintext, MaxKeyWidth'(key),
                                                   KeyWidth, MaxRounds, expected_ciphertext);
    check_output(data_out[Encrypt][SingleRound],
                 expected_ciphertext,
                 $sformatf("Single Round Encryption; %0d rounds, key width %0d",
                           MaxRounds, KeyWidth));
    check_output(data_out[Encrypt][FullRound],
                 expected_ciphertext,
                 $sformatf("Full Round Encryption; %0d rounds, key width %0d",
                           MaxRounds, KeyWidth));
  endtask


  // Helper task to drive ciphertext and key into each decryption instance.
  // Calls a subroutine to perform checks on the outputs (once they are available).
  task automatic check_decryption(input bit [DataWidth-1:0]              ciphertext,
                                  input bit [KeyWidth-1:0]               key,
                                  input bit [NumDuts-1:0][KeyWidth-1:0]  decryption_keys);
    bit [DataWidth-1:0] expected_plaintext;

    // Drive input into decryption instances.
    data_in[Decrypt] <= '{default: ciphertext};
    key_in[Decrypt]  <= decryption_keys;
    idx_in[Decrypt]  <= '{default: 5'(MaxRounds)};

    // Iterate MaxRounds times for the single-round instance.
    for (int unsigned i = 0; i < MaxRounds-1; i++) begin
      #10ns;
      data_in[Decrypt][SingleRound] <= data_out[Decrypt][SingleRound];
      key_in[Decrypt][SingleRound]  <= key_out[Decrypt][SingleRound];
      idx_in[Decrypt][SingleRound]  <= idx_out[Decrypt][SingleRound];
    end

    // Wait a bit for the DUTs to finish calculations.
    #10ns;

    crypto_dpi_present_pkg::sv_dpi_present_decrypt(ciphertext, MaxKeyWidth'(key),
                                                   KeyWidth, MaxRounds, expected_plaintext);
    check_output(data_out[Decrypt][SingleRound],
                 expected_plaintext,
                 $sformatf("Single Round Decryption; %0d rounds, key width %0d",
                           MaxRounds, KeyWidth));
    check_output(data_out[Decrypt][FullRound],
                 expected_plaintext,
                 $sformatf("Full Round Decryption; %0d rounds, key width %0d",
                           MaxRounds, KeyWidth));
  endtask


  // Helper subroutine to compare key and data output values from
  // the C-reference model and the DUTs.
  function automatic void check_output(bit [DataWidth-1:0] dut_value,
                                       bit [DataWidth-1:0] exp_value,
                                       string              desc);
    if (dut_value != exp_value) begin
      $error("%s: MISMATCH. Expected[0x%0x] - Actual[0x%0x]", desc, exp_value, dut_value);
      dv_test_status_pkg::dv_test_status(.passed(1'b0));
    end
  endfunction


//////////////////////////////////////////////////////
// main testbench body
//////////////////////////////////////////////////////

  initial begin : p_stimuli
    int num_trans;

    // The key and plaintext/ciphertext to be fed into PRESENT instances.
    bit [KeyWidth-1:0] key;
    bit [DataWidth-1:0] plaintext;

    $timeformat(-12, 0, " ps", 12);

    /////////////////////////////
    // Test the 4 golden vectors.
    /////////////////////////////

    plaintext = '0;
    key = '0;
    test_present(plaintext, key);

    plaintext = '0;
    key = '1;
    test_present(plaintext, key);

    plaintext = '1;
    key = '0;
    test_present(plaintext, key);

    plaintext = '1;
    key = '1;
    test_present(plaintext, key);

    // Test random vectors
    void'($value$plusargs("smoke_test=%0b", smoke_test));
    num_trans = smoke_test ? 1 : $urandom_range(5000, 25000);
    for (int i = 0; i < num_trans; i++) begin
      randomize(plaintext);
      randomize(key);
      test_present(plaintext, key);
    end

    // Final error checking and print out the test signature (expected by simulation flow).
    $display("All encryption and decryption passes were successful!");
    dv_test_status_pkg::dv_test_status(.passed(1'b1));
    $finish();
  end

  initial begin
    bit poll_for_stop;
    int unsigned poll_for_stop_interval_ns;

    poll_for_stop = 1'b1;
    void'($value$plusargs("poll_for_stop=%0b", poll_for_stop));
    poll_for_stop_interval_ns = 1000;
    void'($value$plusargs("poll_for_stop_interval_ns=%0d", poll_for_stop_interval_ns));
    if (poll_for_stop) dv_utils_pkg::poll_for_stop(.interval_ns(poll_for_stop_interval_ns));
  end

endmodule : prim_present_tb
