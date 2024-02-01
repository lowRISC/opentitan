// Copyright lowRISC contributors (OpenTitan project).
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

  // interface direction / mode - Host or Device
  typedef enum bit {
    Host,
    Device
  } if_mode_e;

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

 // Enum representing a probe operation on an internal signal.
  typedef enum {
    SignalProbeSample,  // Sample the signal.
    SignalProbeForce,   // Force the signal with some value.
    SignalProbeRelease  // Release the previous force.
  } signal_probe_e;

  // Enum representing a type of host requests - read only, write only or random read & write
  typedef enum int {
    HostReqNone      = 0,
    HostReqReadOnly  = 1,
    HostReqWriteOnly = 2,
    HostReqReadWrite = 3
  } host_req_type_e;

  // Enum representing clock frequency difference on 2 clocks
  typedef enum bit [1:0] {
    ClkFreqDiffNone,
    ClkFreqDiffSmall,
    ClkFreqDiffBig,
    ClkFreqDiffAny
  } clk_freq_diff_e;

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

  // Extracts the address and size of a const symbol in a SW test (supplied as an ELF file).
  //
  // Used by a testbench to modify the given symbol in an executable (elf) generated for an embedded
  // CPU within the DUT. This function only returns the extracted address and size of the symbol
  // using the readelf utility. Readelf comes with binutils, a package typically available on linux
  // machines. If not available, the assumption is, it can be relatively easily installed.
  // The actual job of writing the new value into the symbol is handled externally (often via a
  // backdoor mechanism to write the memory).
  // Return 1 on success and 0 on failure.
  function automatic bit sw_symbol_get_addr_size(input string elf_file,
                                                 input string symbol,
                                                 input bit does_not_exist_ok,
                                                 output longint unsigned addr,
                                                 output longint unsigned size);

    string msg_id = "sw_symbol_get_addr_size";
    string escaped_symbol = "";
    string symbol_for_filename = "";

    `DV_CHECK_STRNE_FATAL(elf_file, "", "Input arg \"elf_file\" cannot be an empty string", msg_id)
    `DV_CHECK_STRNE_FATAL(symbol,   "", "Input arg \"symbol\" cannot be an empty string", msg_id)

    // If the symbol has special characters, such as '$', escape it for the cmd below, but when
    // creating the file, omit the special characters entirely.
    foreach (symbol[i]) begin
      if (symbol[i] == "$") begin
        escaped_symbol = {escaped_symbol, "\\", symbol[i]};
      end else begin
        escaped_symbol = {escaped_symbol, symbol[i]};
        symbol_for_filename = {symbol_for_filename, symbol[i]};
      end
    end

    begin
      int ret;
      string line;
      int out_file_d = 0;
      string out_file = $sformatf("%0s.dat", symbol_for_filename);
      string cmd = $sformatf(
          // use `--wide` to avoid truncating the output, in case of long symbol name
          // `\s%0s$` ensures we are looking for an exact match, with no pre- or postfixes.
          "/usr/bin/readelf -s --wide %0s | grep \"\\s%0s$\" | awk \'{print $2\" \"$3}\' > %0s",
          elf_file, escaped_symbol, out_file);

      // TODO #3838: shell pipes are bad 'mkay?
      ret = $system(cmd);
      `DV_CHECK_EQ_FATAL(ret, 0, $sformatf("Command \"%0s\" failed with exit code %0d", cmd, ret),
                         msg_id)

      out_file_d = $fopen(out_file, "r");
      `DV_CHECK_FATAL(out_file_d, $sformatf("Failed to open \"%0s\"", out_file), msg_id)

      ret = $fgets(line, out_file_d);

      // If the symbol did not exist in the elf (empty file), and we are ok with that, then return.
      if (!ret && does_not_exist_ok) return 0;

      `DV_CHECK_FATAL(ret, $sformatf("Failed to read line from \"%0s\"", out_file), msg_id)

      // The first line should have the addr in hex followed by its size as integer.
      ret = $sscanf(line, "%h %d", addr, size);
      `DV_CHECK_EQ_FATAL(ret, 2, $sformatf("Failed to extract {addr size} from line \"%0s\"", line),
                         msg_id)

      // Attempt to read the next line should be met with EOF.
      void'($fgets(line, out_file_d));
      ret = $feof(out_file_d);
      `DV_CHECK_FATAL(ret, $sformatf("EOF expected to be reached for \"%0s\"", out_file), msg_id)
      $fclose(out_file_d);

      ret = $system($sformatf("rm -rf %0s", out_file));
      `DV_CHECK_EQ_FATAL(ret, 0, $sformatf("Failed to delete \"%0s\"", out_file), msg_id)
      return 1;
    end
  endfunction

  // Reads VMEM file contents into a queue of data.
  //
  // TODO: Add support for non-contiguous memory.
  // TODO: Add support for ECC bits.
  // TODO: Add support for non-BUS_DW sized VMEM data.
  // vmem_file: Path to VMEM image, compatible with $readmemh mathod.
  // vmem_data: A queue of BUS_DW sized data returned to the caller.
  function automatic void read_vmem(input string vmem_file,
                                    output logic [bus_params_pkg::BUS_DW-1:0] vmem_data[$]);
    int fd;
    uvm_reg_addr_t last_addr;
    string text, msg = "\n", lines[$];

    fd = $fopen(vmem_file, "r");
    `DV_CHECK_FATAL(fd, $sformatf("Failed to open \"%0s\"", vmem_file), msg_id)
    while (!$feof(fd)) begin
      string line;
      void'($fgets(line, fd));
      line = str_utils_pkg::str_strip(line);
      if (line == "") continue;
      text = {text, line, "\n"};
    end
    $fclose(fd);
    `DV_CHECK_STRNE_FATAL(text, "", , msg_id)

    // Remove all block and single comments.
    text = str_utils_pkg::str_remove_sections(.s(text), .start_delim("/*"), .end_delim("*/"));
    text = str_utils_pkg::str_remove_sections(.s(text), .start_delim("//"), .end_delim("\n"),
                                              .remove_end_delim(0));

    vmem_data.delete();
    str_utils_pkg::str_split(text, lines, "\n");
    foreach (lines[i]) begin
      string tokens[$];
      uvm_reg_addr_t addr;

      // Split the line by space. The first item must be the address that starts with '@'.
      str_utils_pkg::str_split(lines[i], tokens, " ");
      `DV_CHECK_FATAL(tokens.size() >= 2,
                      $sformatf("Line \"%s\" in VMEM file %s appears to be malformed",
                                lines[i], vmem_file), msg_id)
      if (!str_utils_pkg::str_starts_with(tokens[0], "@")) begin
        `uvm_fatal(msg_id, $sformatf({"The first word \"%s\" on line \"%s\" in the VMEM file %s ",
                                      " does not appear to be a valid address"},
                                    tokens[0], lines[i], vmem_file))
      end
      tokens[0] = tokens[0].substr(1, tokens[0].len() - 1);
      `DV_CHECK_FATAL(tokens[0].len() <= bus_params_pkg::BUS_AW / 8 * 2,
                      $sformatf("Address width > %0d bytes is not supported: 0x%0s",
                                bus_params_pkg::BUS_AW / 8, tokens[0]), msg_id)
      addr = tokens[0].atohex();
      tokens = tokens[1:$];
      if (i > 0) begin
        `DV_CHECK_FATAL(addr == last_addr,
                        $sformatf("Non-contiguous data unsupported - last_addr: 0x%0h, addr: 0x%0h",
                                  last_addr, addr), msg_id)
      end
      foreach (tokens[i]) begin
        logic [bus_params_pkg::BUS_DW-1:0] data;
        `DV_CHECK_FATAL(tokens[i].len() <= bus_params_pkg::BUS_DW / 8 * 2,
                        $sformatf("Data width > %0d bytes is not supported: 0x%0s",
                                  bus_params_pkg::BUS_DW / 8, tokens[i]), msg_id)
        data = tokens[i].atohex();
        msg = {msg, $sformatf("[0x%0h] = 0x%0h\n", addr + i, data)};
        vmem_data.push_back(data);
      end
      last_addr = addr + tokens.size();
    end
    `uvm_info(msg_id, $sformatf("Contents of VMEM file %s:%s", vmem_file, msg), UVM_HIGH)
  endfunction

  // sources
`ifdef UVM
  `include "dv_report_catcher.sv"
  `include "dv_report_server.sv"
  `include "dv_vif_wrap.sv"
`endif

endpackage
