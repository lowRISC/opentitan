// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface otbn_model_if
  import keymgr_pkg::otbn_key_req_t;
#(
  // Size of the instruction memory, in bytes
  parameter int ImemSizeByte = 4096,

  localparam int ImemAddrWidth = prim_util_pkg::vbits(ImemSizeByte)
) (
  input logic clk_i,
  input logic rst_ni,
  input otbn_key_req_t keymgr_key_i
);

  // Inputs to DUT
  logic                     start;        // Start the operation

  // Outputs from DUT
  bit                       err;          // Something went wrong
  bit [31:0]                stop_pc;      // PC at end of operation
  otbn_pkg::err_bits_t      err_bits;     // Error bits; updated when STATUS switches to idle

  // Mirrored registers
  bit [7:0]                 status;       // STATUS register

  chandle                   handle;       // Handle for DPI calls to C model

  clocking cb @(posedge clk_i);
  endclocking

  // Wait until reset or change of status.
  task automatic wait_status();
    automatic bit [7:0] old_status = status;
    while (rst_ni === 1'b1 && status == old_status) begin
      @(negedge clk_i or negedge rst_ni);
    end
  endtask

  // Start model by setting start for a cycle. Waits until not in reset.
  task automatic start_model();
    wait(rst_ni);
    start = 1'b1;
    @(posedge clk_i or negedge rst_ni);
    start = 1'b0;
  endtask

  // Mark the entirety of IMEM as invalid
  //
  // Call this on a negedge of clk_i to ensure sequencing with the otbn_model_step on the following
  // posedge.
  function automatic void invalidate_imem();
    `uvm_info("otbn_model_if", "Invalidating IMEM", UVM_HIGH)
    `DV_CHECK_FATAL(otbn_model_pkg::otbn_model_invalidate_imem(handle) == 0,
                    "Failed to invalidate IMEM", "otbn_model_if")
  endfunction

  // Mark the entirety of DMEM as invalid
  //
  // Call this on a negedge of clk_i to ensure sequencing with the otbn_model_step on the following
  // posedge.
  function automatic void invalidate_dmem();
    `uvm_info("otbn_model_if", "Invalidating DMEM", UVM_HIGH)
    `DV_CHECK_FATAL(otbn_model_pkg::otbn_model_invalidate_dmem(handle) == 0,
                    "Failed to invalidate DMEM", "otbn_model_if")
  endfunction

  // Ask the Python model to compute a CRC step for a memory write
  //
  // This doesn't actually update any model state (we pass in the old state and delta, and the
  // function returns the new state). But we still call out to Python because that avoids us having
  // to write our own CRC function and ensures that the RTL matches the standardised CRC-32-IEEE
  // checksum.
  function automatic bit [31:0] step_crc(bit [47:0] item, bit [31:0] crc_state);
    `DV_CHECK_FATAL(otbn_model_pkg::otbn_model_step_crc(handle, item, crc_state) == 0,
                    "Failed to update CRC", "otbn_model_if")
    return crc_state;
  endfunction

  // The err signal is asserted by the model if it fails to find the DUT or if it finds a mismatch
  // in results. It should never go high.
  `ASSERT(NoModelErrs, !err)

endinterface
