// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// If using this, instantiate it somewhere that "u_model" will resolve to the corresponding instance
// of the otbn_core_model module. For example, you might instantiate it in your testbench next to
// your model. In that case, SystemVerilog's symbol resolution rules ("go up until it works") should
// do the right thing.

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
  import uvm_pkg::*;

  // Inputs to DUT
  logic [7:0]               cmd_q;        // CMD register
  logic                     cmd_qe;       // CMD register enable

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

  // Mark the entirety of IMEM as invalid
  //
  // Call this on a negedge of clk_i to ensure sequencing with the otbn_model_step on the following
  // posedge.
  function automatic void invalidate_imem();
    `uvm_info("otbn_model_if", "Invalidating IMEM", UVM_HIGH)
    `DV_CHECK_FATAL(u_model.otbn_model_invalidate_imem(handle) == 0,
                    "Failed to invalidate IMEM", "otbn_model_if")
  endfunction

  // Mark the entirety of DMEM as invalid
  //
  // Call this on a negedge of clk_i to ensure sequencing with the otbn_model_step on the following
  // posedge.
  function automatic void invalidate_dmem();
    `uvm_info("otbn_model_if", "Invalidating DMEM", UVM_HIGH)
    `DV_CHECK_FATAL(u_model.otbn_model_invalidate_dmem(handle) == 0,
                    "Failed to invalidate DMEM", "otbn_model_if")
  endfunction

  // Ask the Python model to compute a CRC step for a memory write
  //
  // This doesn't actually update any model state (we pass in the old state and delta, and the
  // function returns the new state). But we still call out to Python because that avoids us having
  // to write our own CRC function and ensures that the RTL matches the standardised CRC-32-IEEE
  // checksum.
  function automatic bit [31:0] step_crc(bit [47:0] item, bit [31:0] crc_state);
    `DV_CHECK_FATAL(u_model.otbn_model_step_crc(handle, item, crc_state) == 0,
                    "Failed to update CRC", "otbn_model_if")
    return crc_state;
  endfunction

  // Pass loop warp rules to the model
  function automatic void take_loop_warps(chandle memutil);
    u_model.otbn_take_loop_warps(handle, memutil);
  endfunction

  function automatic bit has_loop_warps(chandle memutil);
    return u_model.otbn_has_loop_warps(memutil) != 0;
  endfunction

  task automatic send_err_escalation(bit [31:0] err_val);
    `uvm_info("otbn_model_if", "Escalating errors", UVM_HIGH)
    force u_model.wakeup_iss = 1;
    `DV_CHECK_FATAL(u_model.otbn_model_send_err_escalation(handle, err_val) == 0,
                    "Failed to escalate errors", "otbn_model_if")

    @(posedge clk_i or negedge rst_ni);
    force u_model.wakeup_iss = 0;
    release u_model.wakeup_iss;
  endtask: send_err_escalation

  function automatic void set_software_errs_fatal(bit new_val);
    `uvm_info("otbn_model_if", "writing to software_errs_fatal", UVM_HIGH);
    `DV_CHECK_FATAL(u_model.otbn_model_set_software_errs_fatal(handle, new_val) == 0,
                    "Failed to set software_errs_fatal", "otbn_model_if")
  endfunction

  function automatic void otbn_set_no_sec_wipe_chk();
    `uvm_info("otbn_model_if", "writing to no_sec_wipe_data_chk", UVM_HIGH);
    `DV_CHECK_FATAL(u_model.otbn_set_no_sec_wipe_chk(handle) == 0,
                    "Failed to set no_sec_wipe_data_chk", "otbn_model_if")
  endfunction

  function automatic void otbn_disable_stack_check();
    `uvm_info("otbn_model_if", "Disabling stack integrity checks", UVM_HIGH);
    `DV_CHECK_FATAL(u_model.otbn_disable_stack_check(handle) == 0,
                    "Failed to disable stack integrity checks", "otbn_model_if")
  endfunction

  // The err signal is asserted by the model if it fails to find the DUT or if it finds a mismatch
  // in results. It should never go high.
  `ASSERT(NoModelErrs, !err)



endinterface
