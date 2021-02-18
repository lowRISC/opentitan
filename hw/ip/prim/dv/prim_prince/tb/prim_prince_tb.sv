// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for prim_prince, drives various test vectors into all
// implementations and compares intermediate and final output against
// C-reference model, for both encryption and decryption.
//
// This testbench only tests the PRINCE block cipher in its 64-bit data
// and 128-bit key configuration, other configurations with different sets of
// widths remain untested.

module prim_prince_tb;
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

  // Max number of half-rounds according to spec.
  // Duplicate parameter definition here to avoid clutter due to long identifier.
  localparam int unsigned NumRoundsHalf = crypto_dpi_prince_pkg::NumRoundsHalf;

  // Use these to index the data/key arrays.
  localparam bit Unregistered = 1'b0;
  localparam bit Registered = 1'b1;

  localparam bit NewKeySched = 1'b0;
  localparam bit OldKeySched = 1'b1;

  localparam time ClkPeriod = 10000;

  // This bit can be set from the command line to indicate that we are running a smoke regression,
  // and to run just a single iteration of the test.
  // This helps drastically reduce runtimes in the CI flows.
  bit smoke_test;

//////////////////////////////////////////////////////
// Clock interface
//////////////////////////////////////////////////////

  wire clk, rst_n;

  clk_rst_if clk_if (
    .clk,
    .rst_n
  );

//////////////////////////////////////////////////////
// DUTs for both encryption and decryption
//////////////////////////////////////////////////////

  logic [1:0][1:0][NumRoundsHalf-1:0][DataWidth-1:0]  data_in;
  logic [1:0][1:0][NumRoundsHalf-1:0][DataWidth-1:0]  data_out;
  logic [1:0][1:0][NumRoundsHalf-1:0]                 valid_out;
  logic                                               valid_in;
  logic [KeyWidth-1:0]                                key_in;
  logic                                               dec_in;

  for (genvar i = 0; i < 2; i++) begin : gen_new_key_schedule
    for (genvar j = 0; j < 2; j++) begin : gen_registered_variant
      for (genvar k = 0; k < NumRoundsHalf; k++) begin : gen_duts
        prim_prince #(
          .DataWidth      ( DataWidth           ),
          .KeyWidth       ( KeyWidth            ),
          .NumRoundsHalf  ( k+1                 ),
          .UseOldKeySched ( i                   ),
          .HalfwayDataReg ( j                   ),
          .HalfwayKeyReg  ( j                   )
        ) dut (
          .clk_i          ( clk                 ),
          .rst_ni         ( rst_n               ),
          .valid_i        ( valid_in            ),
          .data_i         ( data_in[i][j][k]    ),
          .key_i          ( key_in              ),
          .dec_i          ( dec_in              ),
          .valid_o        ( valid_out[i][j][k]  ),
          .data_o         ( data_out[i][j][k]   )
        );
      end : gen_duts
    end : gen_registered_variant
  end : gen_new_key_schedule

//////////////////////////////////////////////////////
// API called by the testbench to drive/check stimulus
//////////////////////////////////////////////////////

  // Top level API task that should be called to run a full pass
  // of encryption and decryption on some input data and key.
  task automatic test_prince(bit [DataWidth-1:0] plaintext,
                             bit [KeyWidth-1:0]  key);

    bit [1:0][1:0][NumRoundsHalf-1:0][DataWidth-1:0] encrypted_text;

    check_encryption(plaintext, key, encrypted_text);

    check_decryption(encrypted_text, key);

  endtask


  // Helper task to drive plaintext and key into each encryption instance.
  // Calls a subroutine to perform checks on the outputs (once they are available).
  task automatic check_encryption(
      input bit  [DataWidth-1:0]                              plaintext,
      input bit  [KeyWidth-1:0]                               key,
      output bit [1:0][1:0][NumRoundsHalf-1:0][DataWidth-1:0] expected_cipher);

    // Drive input into encryption instances.
    key_in    = key;
    dec_in    = 0;
    valid_in  = 1;
    for (int unsigned i = 0; i < 2; i++) begin
      for (int unsigned j = 0; j < 2; j++) begin
        for (int unsigned k = 0; k < NumRoundsHalf; k++) begin
          data_in[i][j][k] = plaintext;
        end
      end
    end
    // Wait for the DUTs to finish calculations.
    clk_if.wait_clks(2);
    wait(&valid_out == 1);
    valid_in = 0;
    // query DPI model for expected encrypted output.
    for (int i = 0; i < 2; i++) begin
      for (int j = 0; j < 2; j++) begin
        crypto_dpi_prince_pkg::sv_dpi_prince_encrypt(plaintext, key, i,
                                                     expected_cipher[i][j]);
      end
    end
    check_output(expected_cipher[OldKeySched],
                 expected_cipher[NewKeySched],
                 data_out[OldKeySched],
                 data_out[NewKeySched],
                 "Encryption");
  endtask


  // Helper task to drive ciphertext and key into each decryption instance.
  // Calls a subroutine to perform checks on the outputs (once they are available).
  task automatic check_decryption(
      input bit [1:0][1:0][NumRoundsHalf-1:0][DataWidth-1:0] ciphertext,
      input bit [KeyWidth-1:0]                               key);

    // the expected plaintext after decryption will be provided by the C model.
    bit [1:0][1:0][NumRoundsHalf-1:0][DataWidth-1:0] expected_plaintext;
    // Drive input into decryption instances.
    key_in = key;
    dec_in = 1;
    valid_in = 1;
    for (int unsigned i = 0; i < 2; i++) begin
      for (int unsigned j = 0; j < 2; j++) begin
        for (int unsigned k = 0; k < NumRoundsHalf; k++) begin
          data_in[i][j][k] = ciphertext[i][j][k];
        end
      end
    end
    // Wait for the DUTs to finish calculations.
    clk_if.wait_clks(2);
    wait(&valid_out == 1);
    valid_in = 0;
    // query DPI model for expected decrypted output.
    for (int unsigned i = 0; i < 2; i++) begin
      for (int unsigned j = 0; j < 2; j++) begin
        crypto_dpi_prince_pkg::sv_dpi_prince_decrypt(ciphertext[i][j], key, i,
                                                     expected_plaintext[i][j]);
      end
    end
    check_output(expected_plaintext[OldKeySched],
                 expected_plaintext[NewKeySched],
                 data_out[OldKeySched],
                 data_out[NewKeySched],
                 "Decryption");
  endtask


  // Helper subroutine to compare key and data output values from
  // the C-reference model and the DUTs.
  //
  // For each instance of PRINCE (whether using old or new key schedule),
  // we need to check that the output data matches the output of the reference model.
  //
  // If any comparison error is seen, this task short-circuits immediately,
  // printing out some debug information and the correct failure signature.
  task automatic check_output(
      input bit [1:0][NumRoundsHalf-1:0][DataWidth-1:0] expected_text_old_sched,
      input bit [1:0][NumRoundsHalf-1:0][DataWidth-1:0] expected_text_new_sched,
      input bit [1:0][NumRoundsHalf-1:0][DataWidth-1:0] actual_text_old_sched,
      input bit [1:0][NumRoundsHalf-1:0][DataWidth-1:0] actual_text_new_sched,
      input string                                      msg);

    string reg_msg;
    string err_msg;
    for (int unsigned i = 0; i < 2; i++) begin
      reg_msg = i ? "registered" : "unregistered";
      for (int unsigned j = 0; j < NumRoundsHalf; j++) begin
        // compare outputs generated using old key schedule.
        if (expected_text_old_sched[i][j] != actual_text_old_sched[i][j]) begin
          err_msg = {$sformatf("%s mismatch in %s design with %0d rounds and old key schedule!\n",
                               msg, reg_msg, i+1),
                     $sformatf("Expected[0x%0x] - Actual[0x%0x]\n", expected_text_old_sched[i][j],
                               actual_text_old_sched[i][j])};
          $error(err_msg);
          dv_test_status_pkg::dv_test_status(.passed(1'b0));
        end
        // compare outputs generated using new key schedule.
        if (expected_text_new_sched[i][j] != actual_text_new_sched[i][j]) begin
          err_msg = {$sformatf("%s mismatch in %s design with %0d rounds and old key schedule!\n",
                               msg, reg_msg, i+1),
                     $sformatf("Expected[0x%0x] - Actual[0x%0x]\n", expected_text_new_sched[i][j],
                               actual_text_new_sched[i][j])};
          $error(err_msg);
          dv_test_status_pkg::dv_test_status(.passed(1'b0));
        end
      end
    end
  endtask

//////////////////////////////////////////////////////
// main testbench body
//////////////////////////////////////////////////////

  initial begin : p_stimuli
    int num_trans;
    string msg_id = $sformatf("%m");

    // The key and plaintext/ciphertext to be fed into PRINCE instances.
    bit [KeyWidth/2-1:0] k0, k1;
    bit [DataWidth-1:0] plaintext;

    clk_if.set_period_ps(ClkPeriod);
    clk_if.set_active();
    clk_if.apply_reset();
    $timeformat(-12, 0, " ps", 12);
    clk_if.wait_clks(10);

    /////////////////////////////
    // Test the 5 golden vectors.
    /////////////////////////////

    plaintext = '0;
    k0 = '1;
    k1 = '0;
    test_prince(plaintext, {k1, k0});

    plaintext = '0;
    k0 = '0;
    k1 = '0;
    test_prince(plaintext, {k1, k0});

    plaintext = '1;
    k0 = '0;
    k1 = '0;
    test_prince(plaintext, {k1, k0});

    plaintext = '0;
    k0 = '0;
    k1 = '1;
    test_prince(plaintext, {k1, k0});

    plaintext = 'h0123456789ABCDEF;
    k0 = '0;
    k1 = 'hFEDC_BA98_7654_3210;
    test_prince(plaintext, {k1, k0});

    // Test random vectors
    void'($value$plusargs("smoke_test=%0b", smoke_test));
    num_trans = smoke_test ? 1 : $urandom_range(5000, 25000);
    for (int i = 0; i < num_trans; i++) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(plaintext, "", msg_id)
      `DV_CHECK_STD_RANDOMIZE_FATAL(k0, "", msg_id)
      `DV_CHECK_STD_RANDOMIZE_FATAL(k1, "", msg_id)
      test_prince(plaintext, {k1, k0});
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

endmodule : prim_prince_tb
