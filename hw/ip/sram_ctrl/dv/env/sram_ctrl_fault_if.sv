// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// An interface that can be bound into sram_ctrl in order to inject (and cleanly detect) faults.
//
// To avoid needing to parameterise the interface, this uses a "max footprint" approach, with
// sram_addr and sram_wdata using 64 bits each, rather than AddrWidth and DataWidth.

interface sram_ctrl_fault_if (
  input wire        clk_i,
  input wire        rst_ni,

  input wire        sram_req,
  input wire        sram_we,
  input wire [63:0] sram_addr,
  input wire [63:0] sram_wdata
);
  import uvm_pkg::*;

  // Inject a fault by flipping fault_bits on the signal at rel_path until we have seen the clock
  // low, high and then low again (meaning that we straddle a posedge). The path in rel_path is
  // interpreted relative to the module instance into which this interface is bound.
  //
  // Exits early on reset.
  task automatic fault_signal(string rel_path, uvm_hdl_data_t fault_bits);
    uvm_hdl_data_t good_value;
    string full_path;

    full_path = $sformatf("%0s.%0s",
                         dv_utils_pkg::get_parent_hier($sformatf("%m"), 2),
                         rel_path);

    if (!uvm_hdl_read(full_path, good_value)) begin
      `uvm_fatal($sformatf("%m"), {"Failed to read ", full_path})
    end

    if (!uvm_hdl_force(full_path, good_value ^ fault_bits)) begin
      `uvm_fatal($sformatf("%m"), {"Failed to force ", full_path})
    end

    // Wait for the clock to become high and then low again, exiting early on reset
    fork : isolation_fork begin
      fork
        @(negedge clk_i);
        wait(!rst_ni);
      join_any
      disable fork;
    end join

    // Release the forced signal
    if (!uvm_hdl_release(full_path)) begin
      `uvm_fatal($sformatf("%m"), {"Failed to release ", full_path})
    end

    // Use uvm_hdl_deposit to put back the original good_value (in case the target at full_path
    // isn't driven by a continuous assignment)
    if (!uvm_hdl_deposit(full_path, good_value)) begin
      `uvm_fatal($sformatf("%m"), {"Failed to restore ", full_path})
    end
  endtask

  // Wait until the negedge of the clock on a cycle where an SRAM read or write (depending on the
  // write flag) is in progress.
  //
  // Exits early on reset
  task automatic wait_one_operation(bit write);
    fork : isolation_fork begin
      fork
        wait(!rst_ni);
        @(negedge clk_i iff (write ? sram_we : sram_req));
      join_any
      disable fork;
    end join
  endtask

`define WAIT_FOR_FORCED_SIGNAL(signal, qualifier)                                               \
    fork : isolation_fork begin                                                                 \
      fork                                                                                      \
        wait(!rst_ni);                                                                          \
        forever begin                                                                           \
          // Wait to see a change to signal when qualifier is true. Next, wait a tiny time (to  \
          // avoid races at the posedge) and then check whether clk_i is high. If not, we saw a \
          // change to sram_we that was not on a posedge of the clock.                          \
          @((signal) iff (qualifier));                                                          \
          #1ps;                                                                                 \
          if (!clk_i) break;                                                                    \
        end                                                                                     \
      join_any                                                                                  \
      disable fork;                                                                             \
    end join

  // Wait for a change to sram_we when sram_req is true that happens at a time other than a positive
  // edge of the clock (and therefore must have been caused by forcing a signal).
  //
  // Exits early on reset
  task automatic wait_for_sram_we_corruption();
    `WAIT_FOR_FORCED_SIGNAL(sram_we, sram_req)
  endtask

  // Wait for a change to sram_wdata when sram_req and sram_wdata are true that happens at a time
  // other than a positive edge of the clock (and therefore must have been caused by forcing a
  // signal).
  //
  // Exits early on reset
  task automatic wait_for_sram_wdata_corruption();
    `WAIT_FOR_FORCED_SIGNAL(sram_wdata, sram_req && sram_we)
  endtask

  // Wait for a change to sram_addr when sram_req is true that happens at a time other than a
  // positive edge of the clock (and therefore must have been caused by forcing a signal).
  //
  // Exits early on reset
  task automatic wait_for_sram_addr_corruption();
    `WAIT_FOR_FORCED_SIGNAL(sram_addr, sram_req)
  endtask

`undef WAIT_FOR_FORCED_SIGNAL

endinterface
