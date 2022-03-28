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

  // Key width can be set with a define, but must be 80 or 128
`ifdef KEY_WIDTH
  localparam int unsigned KeyWidth = `KEY_WIDTH;
`else
  localparam int unsigned KeyWidth = 128;
`endif

  localparam string MSG_ID = $sformatf("%m");

  // used to index the data arrays
  localparam bit Encrypt = 1'b0;
  localparam bit Decrypt = 1'b1;

  // This bit can be set from the command line to indicate that we are running a smoke regression,
  // and to run just a single iteration of the test.
  // This helps drastically reduce runtimes in the CI flows.
  bit smoke_test;

//////////////////////////////////////////////////////
// DUTs for both encryption and decryption
//////////////////////////////////////////////////////

  // data_in[0]: encryption, data_in[1]: decryption.
  // Same scheme used for key_in, data_out, key_out.
  logic [1:0][MaxRounds-1:0][DataWidth-1:0] data_in;
  logic [1:0][MaxRounds-1:0][KeyWidth-1 :0] key_in;
  logic [1:0][MaxRounds-1:0][4:0]           idx_in;
  logic [1:0][MaxRounds-1:0][DataWidth-1:0] data_out;
  logic [1:0][MaxRounds-1:0][KeyWidth-1 :0] key_out;
  logic [1:0][MaxRounds-1:0][4:0]           idx_out;

  for (genvar j = 0; j < 2; j++) begin : gen_encrypt_decrypt
    for (genvar k = 0; k < MaxRounds; k++) begin : gen_duts
      if (j == 0) begin : gen_encrypt
        assign idx_in[j][k] = 5'd1;
      end else begin : gen_decrypt
        assign idx_in[j][k] = 5'(k+1);
      end
      prim_present #(
        .DataWidth  ( DataWidth ),
        .KeyWidth   ( KeyWidth  ),
        .NumRounds  ( k+1       ),
        .Decrypt    ( j         )
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

    bit [MaxRounds-1:0][DataWidth-1:0] encrypted_text;

    check_encryption(plaintext, key, encrypted_text);
    check_decryption(encrypted_text, key, key_out[Encrypt]);
  endtask


  // Helper task to drive plaintext and key into each encryption instance.
  // Calls a subroutine to perform checks on the outputs (once they are available).
  task automatic check_encryption(input bit [DataWidth-1:0]                 plaintext,
                                  input bit [KeyWidth-1:0]                  key,
                                  output bit [MaxRounds-1:0][DataWidth-1:0] expected_ciphertext);

    // Drive input into encryption instances.
    for (int unsigned i = 0; i < MaxRounds; i++) begin
      data_in[Encrypt][i] = plaintext;
      key_in[Encrypt][i]  = key;
    end

    // Wait a bit for the DUTs to finish calculations.
    #100ns;

    for (int unsigned i = 0; i < MaxRounds; i++) begin
      crypto_dpi_present_pkg::sv_dpi_present_encrypt(plaintext, MaxKeyWidth'(key),
                                                     KeyWidth, i + 1, expected_ciphertext[i]);

      check_output(data_out[Encrypt][i],
                   expected_ciphertext[i],
                   $sformatf("Encryption; %0d rounds, key width %0d", i + 1, KeyWidth));
    end
  endtask


  // Helper task to drive ciphertext and key into each decryption instance.
  // Calls a subroutine to perform checks on the outputs (once they are available).
  task automatic check_decryption(input bit [MaxRounds-1:0][DataWidth-1:0]  ciphertext,
                                  input bit [KeyWidth-1:0]                  key,
                                  input bit [MaxRounds-1:0][KeyWidth-1:0]   decryption_keys);

    // Drive input into decryption instances.
    data_in[Decrypt] = ciphertext;
    key_in[Decrypt] = decryption_keys;

    // Wait a bit for the DUTs to finish calculations.
    #100ns;

    // query DPI model for expected decrypted output.
    for (int unsigned i = 0; i < MaxRounds; i++) begin
      bit [DataWidth-1:0] expected_plaintext;
      crypto_dpi_present_pkg::sv_dpi_present_decrypt(ciphertext[i],
                                                     key, KeyWidth,
                                                     i + 1,
                                                     expected_plaintext);
      check_output(data_out[Decrypt][i],
                   expected_plaintext,
                   $sformatf("Decryption; %0d rounds, key width %0d", i + 1, KeyWidth));
    end
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
      `DV_CHECK_STD_RANDOMIZE_FATAL(plaintext, "", MSG_ID)
      `DV_CHECK_STD_RANDOMIZE_FATAL(key, "", MSG_ID)
      test_present(plaintext, key);
    end

    // Final error checking and print out the test signature (expected by simulation flow).
    $display("All encryption and decryption passes were successful!");
    dv_test_status_pkg::dv_test_status(.passed(1'b1));
    $finish();
  end

  // TODO: perhaps wrap this in a macro?
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
