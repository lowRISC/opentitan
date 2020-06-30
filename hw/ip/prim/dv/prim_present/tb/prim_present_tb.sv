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

//////////////////////////////////////////////////////
// config
//////////////////////////////////////////////////////

// Default to {data_width:64, key_width:128} configuration.
// Data width and key width can be overriden from command-line if desired.

`ifdef DATA_WIDTH
  localparam int unsigned DataWidth = `DATA_WIDTH;
`else
  localparam int unsigned DataWidth = 64;
`endif

`ifdef KEY_WIDTH
  localparam int unsigned KeyWidth = `KEY_WIDTH;
`else
  localparam int unsigned KeyWidth = 128;
`endif

  // Max number of rounds according to spec.
  // We redefine this parameter here to avoid clutter from the long package identifier.
  localparam int unsigned NumRounds = crypto_dpi_present_pkg::NumRounds;

  // used to index the data arrays
  localparam bit Encrypt = 1'b0;
  localparam bit Decrypt = 1'b1;

  // this parameter is required for the DPI model.
  localparam KeySize80 = (KeyWidth == 80);


//////////////////////////////////////////////////////
// DUTs for both encryption and decryption
//////////////////////////////////////////////////////

  // data_in[0]: encryption, data_in[1]: decryption.
  // Same scheme used for key_in, data_out, key_out.
  logic [1:0][NumRounds-1:0][DataWidth-1:0] data_in;
  logic [1:0][NumRounds-1:0][KeyWidth-1 :0] key_in;
  logic [1:0][NumRounds-1:0][DataWidth-1:0] data_out;
  logic [1:0][NumRounds-1:0][KeyWidth-1 :0] key_out;

  for (genvar j = 0; j < 2; j++) begin : gen_encrypt_decrypt
    for (genvar k = 0; k < NumRounds; k++) begin : gen_duts
      prim_present #(
        .DataWidth  ( DataWidth ),
        .KeyWidth   ( KeyWidth  ),
        .NumRounds  ( k+1       ),
        .Decrypt    ( j         )
      ) dut (
        .data_i     ( data_in[j][k]  ),
        .key_i      ( key_in[j][k]   ),
        .data_o     ( data_out[j][k] ),
        .key_o      ( key_out[j][k]  )
      );
    end
  end


//////////////////////////////////////////////////////
// API called by the testbench to drive/check stimulus
//////////////////////////////////////////////////////

  // Top level API task that should be called to run a full pass
  // of encryption and decryption on some input data and key.
  task test_present(bit [DataWidth-1:0] plaintext,
                    bit [KeyWidth-1:0]  key);

    bit [NumRounds:0][63:0] key_schedule;
    bit [NumRounds-1:0][DataWidth-1:0] encrypted_text;

    crypto_dpi_present_pkg::sv_dpi_present_get_key_schedule(key, KeySize80, key_schedule);

    $display("Starting encryption pass with data[0x%0x] and key[0x%0x]!", plaintext, key);
    check_encryption(plaintext, key, key_schedule, encrypted_text);

    $display("Starting decryption pass!");
    check_decryption(encrypted_text, key, key_out[Encrypt]);

  endtask



  // Helper task to drive plaintext and key into each encryption instance.
  // Calls a subroutine to perform checks on the outputs (once they are available).
  task check_encryption(input bit [DataWidth-1:0]                 plaintext,
                        input bit [KeyWidth-1:0]                  key,
                        input bit [NumRounds:0][63:0]             key_schedule,
                        output bit [NumRounds-1:0][DataWidth-1:0] expected_ciphertext);

    // Drive input into encryption instances.
    for (int unsigned i = 0; i < NumRounds; i++) begin
      data_in[Encrypt][i] = plaintext;
      key_in[Encrypt][i]  = key;
    end

    // Wait a bit for the DUTs to finish calculations.
    #100ns;

    // query DPI model for expected encrypted output.
    crypto_dpi_present_pkg::sv_dpi_present_encrypt(plaintext, key,
                                                   KeySize80, expected_ciphertext);

    check_output(key_schedule[NumRounds:1], expected_ciphertext,
                 key_out[Encrypt], data_out[Encrypt], "Encryption");
  endtask


  // Helper task to drive ciphertext and key into each decryption instance.
  // Calls a subroutine to perform checks on the outputs (once they are available).
  task check_decryption(input bit [NumRounds-1:0][DataWidth-1:0]  ciphertext,
                        input bit [KeyWidth-1:0]                  key,
                        input bit [NumRounds-1:0][KeyWidth-1:0]   decryption_keys);

    // the expected plaintext after decryption will be provided by the C model.
    bit [NumRounds-1:0][DataWidth-1:0] expected_plaintext;

    // the expected key after decryption will simply be the original key.
    // the C model only provides a key schedule, which is not useful here.
    bit [NumRounds-1:0][63:0] expected_key;
    for (int i = 0; i < NumRounds; i++) begin
      expected_key[i] = key[KeyWidth-1:KeyWidth-64];
    end

    // Drive input into decryption instances.
    data_in[Decrypt] = ciphertext;
    key_in[Decrypt] = decryption_keys;

    // Wait a bit for the DUTs to finish calculations.
    #100ns;

    // query DPI model for expected decrypted output.
    crypto_dpi_present_pkg::sv_dpi_present_decrypt(ciphertext, key, KeySize80, expected_plaintext);

    check_output(expected_key, expected_plaintext,
                 key_out[Decrypt], data_out[Decrypt], "Decryption");
  endtask


  // Helper subroutine to compare key and data output values from
  // the C-reference model and the DUTs.
  //
  // For each instance of PRESENT (whether encryption or decryption),
  // we need to perform two checks:
  //    1) Check that the output key matches the corresponding key in the schedule.
  //    2) Check that the output data matches the output of the reference model.
  //
  // If any comparison error is seen, this task short-circuits immediately,
  // printing out some debug information and the correct failure signature.
  task check_output(input bit [NumRounds-1:0][63:0]           expected_key,
                    input bit [NumRounds-1:0][DataWidth-1:0]  expected_text,
                    input bit [NumRounds-1:0][KeyWidth-1:0]   actual_key,
                    input bit [NumRounds-1:0][DataWidth-1:0]  actual_data,
                    input string msg);

    bit error = 1'b0;

    for (int unsigned i = 0; i < NumRounds; i++) begin
      // compare the output key to the corresponding key in the schedule.
      if (expected_key[i] != actual_key[i][KeyWidth-1:KeyWidth-64]) begin
        error = 1'b1;
        $error("%s output key mismatch at round %0d! Expected[0x%0x] - Actual[0x%0x]",
               msg, i, expected_key[i], actual_key[i][KeyWidth-1:KeyWidth-64]);
        break;
      end
      // compare encrypted output text to reference model
      if (expected_text[i] != actual_data[i]) begin
        error = 1'b1;
        $error("%s output text mismatch at round %0d! Expected[0x%0x] - Actual[0x%0x]",
               msg, i, expected_text[i], actual_data[i]);
        break;
      end
    end
    if (error) $fatal("TEST FAILED CHECKS");
  endtask


//////////////////////////////////////////////////////
// main testbench body
//////////////////////////////////////////////////////

  initial begin : p_stimuli

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
    for (int i = 0; i < 5000; i++) begin
      if (!std::randomize(plaintext)) begin
        $fatal("Randomization of plaintext failed!");
      end
      if (!std::randomize(key)) begin
        $fatal("Randomization of key failed!");
      end
      test_present(plaintext, key);
    end


    // Final error checking and print out the test signature (expected by simulation flow).
    $display("All encryption and decryption passes were successful!");
    $display("TEST PASSED CHECKS");
    $finish();
  end


endmodule : prim_present_tb
