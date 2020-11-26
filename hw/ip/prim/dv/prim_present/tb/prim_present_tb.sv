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

  // used to index data arrays
  localparam bit Unrolled = 1'b0;
  localparam bit Iterative = 1'b1;

  // this parameter is required for the DPI model.
  localparam bit KeySize80 = (KeyWidth == 80);

  // This bit can be set from the command line to indicate that we are running a smoke regression,
  // and to run just a single iteration of the test.
  // This helps drastically reduce runtimes in the CI flows.
  bit smoke_test;

//////////////////////////////////////////////////////
// DUTs for both encryption and decryption
//////////////////////////////////////////////////////

  // Inputs for the unrolled PRESENT instances.
  // data_in[0]: encryption, data_in[1]: decryption - same scheme for key/idx.
  logic [1:0][NumRounds-1:0][DataWidth-1:0] data_in;
  logic [1:0][NumRounds-1:0][KeyWidth-1 :0] key_in;
  logic [1:0][NumRounds-1:0][4:0]           idx_in;

  // Intermediate input/output arrays for the iterative PRESENT instances.
  // data_iter_in[0]: encryption, data_iter_in[1]: decryption - same scheme for key/idx.
  logic [1:0][NumRounds-1:0][NumRounds-1:0][DataWidth-1:0]  data_iter_in;
  logic [1:0][NumRounds-1:0][NumRounds-1:0][KeyWidth-1:0]   key_iter_in;
  logic [1:0][NumRounds-1:0][NumRounds-1:0][4:0]            idx_iter_in;
  logic [1:0][NumRounds-1:0][NumRounds-1:0][DataWidth-1:0]  data_iter_out;
  logic [1:0][NumRounds-1:0][NumRounds-1:0][KeyWidth-1:0]   key_iter_out;
  logic [1:0][NumRounds-1:0][NumRounds-1:0][4:0]            idx_iter_out;

  // Final output arrays used for correctness checking.
  logic [1:0][1:0][NumRounds-1:0][DataWidth-1:0] data_out;
  logic [1:0][1:0][NumRounds-1:0][KeyWidth-1:0]  key_out;
  logic [1:0][1:0][NumRounds-1:0][4:0]           idx_out;

  // Unrolled PRESENT instances.
  //
  // Generate NumRounds number of PRESENT instances, each with its NumRounds parameter set to N,
  // where 1<N<NumRounds+1.
  for (genvar j = 0; j < 2; j++) begin : gen_unrolled_encrypt_decrypt
    for (genvar k = 0; k < NumRounds; k++) begin : gen_unrolled_duts
      if (j == 0) begin : gen_encrypt
        assign idx_in[j][k] = 5'd1;
      end else begin : gen_decrypt
        assign idx_in[j][k] = 5'(k+1);
      end
      prim_present #(
        .DataWidth     ( DataWidth ),
        .KeyWidth      ( KeyWidth  ),
        .NumRounds     ( k+1       ),
        .NumPhysRounds ( k+1       ),
        .Decrypt       ( j         )
      ) dut (
        .data_i        ( data_in[j][k]            ),
        .key_i         ( key_in[j][k]             ),
        .idx_i         ( idx_in[j][k]             ),
        .data_o        ( data_out[Unrolled][j][k] ),
        .key_o         ( key_out[Unrolled][j][k]  ),
        .idx_o         ( idx_out[Unrolled][j][k]  )
      );
    end
  end

  // Iterative PRESENT instances.
  //
  // For 1<N<NumRounds+1, generate N chained PRESENT instances,
  // each running 1 physical round of the algorithm.
  //
  // This should produce equivalent results as the PRESENT instances running N internal rounds.
  for (genvar i = 0; i < 2; i++) begin : gen_iterative_encrypt_decrypt
    for (genvar j = 0; j < NumRounds; j++) begin : gen_iterative_duts
      for (genvar k = 0; k <= j; k++) begin : gen_numrounds_duts
        // assign encryption/decryption indices
        assign idx_iter_in[i][j][k] = (i == 0) ? 5'(k+1) : 5'(j+1-k);
        if (k == 0) begin : gen_first
          // Assign the very first set of inputs to the requested plaintext/key.
          assign data_iter_in[i][j][k] = data_in[i][j];
          assign key_iter_in[i][j][k] = key_in[i][j];
        end else begin : gen_others
          // assign the data/key inputs of round K+1 to the outputs of round K.
          assign data_iter_in[i][j][k] = data_iter_out[i][j][k-1];
          assign key_iter_in[i][j][k] = key_iter_out[i][j][k-1];
        end
          // On the last round, assign the correct final outputs.
        if (k == j) begin : gen_last
          assign data_out[Iterative][i][j] = data_iter_out[i][j][k];
          assign key_out[Iterative][i][j] = key_iter_out[i][j][k];
          assign idx_out[Iterative][i][j] = idx_iter_out[i][j][k];
        end

        prim_present #(
          .DataWidth     ( DataWidth ),
          .KeyWidth      ( KeyWidth  ),
          .NumRounds     ( j+1       ),
          .NumPhysRounds ( 1         ),
          .Decrypt       ( i         )
        ) dut (
          .data_i ( data_iter_in[i][j][k]  ),
          .key_i  ( key_iter_in[i][j][k]   ),
          .idx_i  ( idx_iter_in[i][j][k]   ),
          .data_o ( data_iter_out[i][j][k] ),
          .key_o  ( key_iter_out[i][j][k]  ),
          .idx_o  ( idx_iter_out[i][j][k]  )
        );
      end
    end
  end


//////////////////////////////////////////////////////
// API called by the testbench to drive/check stimulus
//////////////////////////////////////////////////////

  // Top level API task that should be called to run a full pass
  // of encryption and decryption on some input data and key.
  task automatic test_present(bit [DataWidth-1:0] plaintext,
                              bit [KeyWidth-1:0]  key);

    bit [NumRounds:0][63:0] key_schedule;
    bit [NumRounds-1:0][DataWidth-1:0] encrypted_text;

    crypto_dpi_present_pkg::sv_dpi_present_get_key_schedule(key, KeySize80, key_schedule);

    check_encryption(plaintext, key, key_schedule, encrypted_text);

    check_decryption(encrypted_text, key, key_out[Encrypt]);

  endtask


  // Helper task to drive plaintext and key into each encryption instance.
  // Calls a subroutine to perform checks on the outputs (once they are available).
  task automatic check_encryption(input bit [DataWidth-1:0]                 plaintext,
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

    // Test encryption with unrolled PRESENT instances.
    check_output(key_schedule[NumRounds:1], expected_ciphertext,
                 key_out[Unrolled][Encrypt], data_out[Unrolled][Encrypt],
                 "Unrolled encryption");

    // Test encryption with iterative PRESENT instances.
    check_output(key_schedule[NumRounds:1], expected_ciphertext,
                 key_out[Iterative][Encrypt], data_out[Iterative][Encrypt],
                 "Iterative encryption");
  endtask


  // Helper task to drive ciphertext and key into each decryption instance.
  // Calls a subroutine to perform checks on the outputs (once they are available).
  task automatic check_decryption(input bit [NumRounds-1:0][DataWidth-1:0]  ciphertext,
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

    // Test decryption with unrolled PRESENT instances.
    check_output(expected_key, expected_plaintext,
                 key_out[Unrolled][Decrypt], data_out[Unrolled][Decrypt],
                 "Unrolled decryption");

    // Test decryption with iterative PRESENT instances.
    check_output(expected_key, expected_plaintext,
                 key_out[Iterative][Decrypt], data_out[Iterative][Decrypt],
                 "Iterative decryption");
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
  task automatic check_output(input bit [NumRounds-1:0][63:0]           expected_key,
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
    if (error) dv_test_status_pkg::dv_test_status(.passed(1'b0));
  endtask


//////////////////////////////////////////////////////
// main testbench body
//////////////////////////////////////////////////////

  initial begin : p_stimuli
    int num_trans;
    string msg_id = $sformatf("%m");

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
      `DV_CHECK_STD_RANDOMIZE_FATAL(plaintext, "", msg_id)
      `DV_CHECK_STD_RANDOMIZE_FATAL(key, "", msg_id)
      test_present(plaintext, key);
    end

    // Final error checking and print out the test signature (expected by simulation flow).
    $display("All encryption and decryption passes were successful!");
    dv_test_status_pkg::dv_test_status(.passed(1'b1));
    $finish();
  end

  // TODO: perhaps wrap this in a macro?
  initial begin
    bit poll_for_stop = 1'b1;
    int unsigned poll_for_stop_interval_ns = 1000;
    void'($value$plusargs("poll_for_stop=%0b", poll_for_stop));
    void'($value$plusargs("poll_for_stop_interval_ns=%0d", poll_for_stop_interval_ns));
    if (poll_for_stop) dv_utils_pkg::poll_for_stop(.interval_ns(poll_for_stop_interval_ns));
  end

endmodule : prim_present_tb
