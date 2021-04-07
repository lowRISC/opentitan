// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package dv_test_status_pkg;

  // Prints the test status signature & banner.
  //
  // This function takes a boolean arg indicating whether the test passed or failed and prints the
  // signature along with a banner. The signature can be used by external scripts to determine if
  // the test passed or failed.
  function automatic void dv_test_status(bit passed);
    if (passed) begin
      $display("\nTEST PASSED CHECKS");
      $display(" _____         _                                  _ _ ");
      $display("|_   _|__  ___| |_   _ __   __ _ ___ ___  ___  __| | |");
      $display("  | |/ _ \\/ __| __| | '_ \\ / _` / __/ __|/ _ \\/ _` | |");
      $display("  | |  __/\\__ \\ |_  | |_) | (_| \\__ \\__ \\  __/ (_| |_|");
      $display("  |_|\\___||___/\\__| | .__/ \\__,_|___/___/\\___|\\__,_(_)");
      $display("                    |_|                               \n");
    end else begin
      $display("\nTEST FAILED CHECKS");
      $display(" _____         _      __       _ _          _ _ ");
      $display("|_   _|__  ___| |_   / _| __ _(_) | ___  __| | |");
      $display("  | |/ _ \\/ __| __| | |_ / _` | | |/ _ \\/ _` | |");
      $display("  | |  __/\\__ \\ |_  |  _| (_| | | |  __/ (_| |_|");
      $display("  |_|\\___||___/\\__| |_|  \\__,_|_|_|\\___|\\__,_(_)\n");
    end
  endfunction

endpackage
