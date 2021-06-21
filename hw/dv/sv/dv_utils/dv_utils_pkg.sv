// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

package dv_utils_pkg;
  // dep packages
  import uvm_pkg::*;
  import bus_params_pkg::*;

  // macro includes
  `include "dv_macros.svh"
`ifdef UVM
  `include "uvm_macros.svh"
`endif

  // common parameters used across all benches
  parameter int NUM_MAX_INTERRUPTS = 32;
  typedef logic [NUM_MAX_INTERRUPTS-1:0] interrupt_t;

  parameter int NUM_MAX_ALERTS = 32;
  typedef logic [NUM_MAX_ALERTS-1:0] alert_t;

  // types & variables
  typedef bit [31:0] uint;
  typedef bit [7:0]  uint8;
  typedef bit [15:0] uint16;
  typedef bit [31:0] uint32;
  typedef bit [63:0] uint64;

  // TODO: The above typedefs violate the name rule, which is fixed below. Cleanup the codebase to
  // use the typedefs below and remove the ones above.
  typedef bit [7:0]  uint8_t;
  typedef bit [15:0] uint16_t;
  typedef bit [31:0] uint32_t;
  typedef bit [63:0] uint64_t;

  // typedef parameterized pins_if for ease of implementation for interrupts and alerts
  typedef virtual pins_if #(NUM_MAX_INTERRUPTS) intr_vif;
  typedef virtual pins_if #(1)                  devmode_vif;

  // interface direction / mode - Host or Device
  typedef enum bit {
    Host,
    Device
  } if_mode_e;

  // speed for the clock
  typedef enum int {
    ClkFreq24Mhz  = 24,
    ClkFreq25Mhz  = 25,
    ClkFreq48Mhz  = 48,
    ClkFreq50Mhz  = 50,
    ClkFreq100Mhz = 100
  } clk_freq_mhz_e;

  // compare operator types
  typedef enum {
    CompareOpEq,
    CompareOpCaseEq,
    CompareOpNe,
    CompareOpCaseNe,
    CompareOpGt,
    CompareOpGe,
    CompareOpLt,
    CompareOpLe
  } compare_op_e;

  // mem address struct
  typedef struct {
    uvm_reg_addr_t start_addr;
    uvm_reg_addr_t end_addr;
  } addr_range_t;

  // Enum representing a bus operation type - read or write.
  typedef enum bit {
    BusOpWrite = 1'b0,
    BusOpRead  = 1'b1
  } bus_op_e;

  // Enum representing a type of host requests - read only, write only or random read & write
  typedef enum int {
    HostReqNone      = 0,
    HostReqReadOnly  = 1,
    HostReqWriteOnly = 2,
    HostReqReadWrite = 3
  } host_req_type_e;

  string msg_id = "dv_utils_pkg";

  // return the smaller value of 2 inputs
  function automatic int min2(int a, int b);
      return (a < b) ? a : b;
  endfunction

  // return the bigger value of 2 inputs
  function automatic int max2(int a, int b);
    return (a > b) ? a : b;
  endfunction

  // return the biggest value within the given queue of integers.
  function automatic int max(const ref int int_q[$]);
    `DV_CHECK_GT_FATAL(int_q.size(), 0, "max function cannot accept an empty queue of integers!",
                       msg_id)
    // Assign the first value from the queue in case of negative integers.
    max = int_q[0];
    foreach (int_q[i]) max = max2(max, int_q[i]);
    return max;
  endfunction

  // get absolute value of the input. Usage: absolute(val) or absolute(a - b)
  function automatic uint absolute(int val);
    return val >= 0 ? val : -val;
  endfunction

  // endian swaps a 32-bit data word
  function automatic logic [31:0] endian_swap(logic [31:0] data);
    return {<<8{data}};
  endfunction

  // endian swaps bytes at a word granularity, while preserving overall word ordering.
  //
  // e.g. if `arr[] = '{'h0, 'h1, 'h2, 'h3, 'h4, 'h5, 'h6, 'h7}`, this function will produce:
  //      `'{'h3, 'h2, 'h1, 'h0, 'h7, 'h6, 'h5, 'h4}`
  function automatic void endian_swap_byte_arr(ref bit [7:0] arr[]);
    arr = {<< byte {arr}};
    arr = {<< 32 {arr}};
  endfunction

`ifdef UVM
  // Simple function to set max errors before quitting sim
  function automatic void set_max_quit_count(int n);
    uvm_report_server report_server = uvm_report_server::get_server();
    report_server.set_max_quit_count(n);
  endfunction

  // return if uvm_fatal occurred
  function automatic bit has_uvm_fatal_occurred();
    uvm_report_server report_server = uvm_report_server::get_server();
    return report_server.get_severity_count(UVM_FATAL) > 0;
  endfunction

  // task that waits for the specfied timeout
  task automatic wait_timeout(input uint    timeout_ns,
                              input string  error_msg_id  = msg_id,
                              input string  error_msg     = "timeout occurred!",
                              input bit     report_fatal  = 1);
    #(timeout_ns * 1ns);
    if (report_fatal) `uvm_fatal(error_msg_id, error_msg)
    else              `uvm_error(error_msg_id, error_msg)
  endtask : wait_timeout

  // get masked data based on provided byte mask; if csr reg handle is provided (optional) then
  // masked bytes from csr's mirrored value are returned, else masked bytes are 0's
  function automatic bit [bus_params_pkg::BUS_DW-1:0]
      get_masked_data(bit [bus_params_pkg::BUS_DW-1:0] data,
                      bit [bus_params_pkg::BUS_DBW-1:0] mask,
                      uvm_reg csr = null);
    bit [bus_params_pkg::BUS_DW-1:0] csr_data;
    csr_data = (csr != null) ? csr.get_mirrored_value() : '0;
    get_masked_data = data;
    foreach (mask[i]) begin
      if (~mask[i]) get_masked_data[i * 8 +: 8] = csr_data[i * 8 +: 8];
    end
  endfunction

  // create a sequence by name and return the handle of uvm_sequence
  function automatic uvm_sequence create_seq_by_name(string seq_name);
    uvm_object      obj;
    uvm_factory     factory;
    uvm_sequence    seq;

    factory = uvm_factory::get();
    obj = factory.create_object_by_name(seq_name, "", seq_name);
    if (obj == null) begin
      // print factory overrides to help debug
      factory.print(1);
      `uvm_fatal(msg_id, $sformatf("could not create %0s seq", seq_name))
    end
    if (!$cast(seq, obj)) begin
      `uvm_fatal(msg_id, $sformatf("cast failed - %0s is not a uvm_sequence", seq_name))
    end
    return seq;
  endfunction
`endif

  // Returns the hierarchical path to the interface / module N levels up.
  //
  // Meant to be invoked inside a module or interface.
  // hier:        String input of the interface / module, typically $sformatf("%m").
  // n_levels_up: Integer number of levels up the hierarchy to omit.
  //              Example: if (hier = tb.dut.foo.bar, n_levels_up = 2), then return tb.dut
  function automatic string get_parent_hier(string hier, int n_levels_up = 1);
    int idx;
    int level;
    if (n_levels_up <= 0) return hier;
    for (idx = hier.len() - 1; idx >= 0; idx--) begin
      if (hier[idx] == ".") level++;
      if (level == n_levels_up) break;
    end
    return (hier.substr(0, idx - 1));
  endfunction

  // Periodically check for the existence of a magic file (dv.stop). Exit if it exists. This
  // provides a mechanism to gracefully kill a simulation without direct access to the process.
  task automatic poll_for_stop(uint interval_ns = 10_000, string filename = "dv.stop");
    fork
      while (1) begin
        #(interval_ns * 1ns);
        if (!$system($sformatf("test -f %0s", filename))) begin
          $system($sformatf("rm %0s", filename));
          `dv_fatal($sformatf("Found %0s file. Exiting!", filename), "poll_for_stop")
        end
      end
    join_none
  endtask : poll_for_stop

  // sources
`ifdef UVM
  `include "dv_report_server.sv"
  `include "dv_vif_wrap.sv"
`endif

endpackage
