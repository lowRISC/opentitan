// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// shortcuts for use in switching # of args to insert in formatted string
`define _USE_STR_ARG(n) (sw_log.str_arg.exists(``n``) ? sw_log.str_arg[``n``] : sw_log.arg[``n``])
`define _1_ARGS         `_USE_STR_ARG(0)
`define _2_ARGS         `_1_ARGS, `_USE_STR_ARG(1)
`define _3_ARGS         `_2_ARGS, `_USE_STR_ARG(2)
`define _4_ARGS         `_3_ARGS, `_USE_STR_ARG(3)
`define _5_ARGS         `_4_ARGS, `_USE_STR_ARG(4)
`define _6_ARGS         `_5_ARGS, `_USE_STR_ARG(5)
`define _7_ARGS         `_6_ARGS, `_USE_STR_ARG(6)
`define _8_ARGS         `_7_ARGS, `_USE_STR_ARG(7)
`define _9_ARGS         `_8_ARGS, `_USE_STR_ARG(8)
`define _10_ARGS        `_9_ARGS, `_USE_STR_ARG(9)
`define _11_ARGS        `_10_ARGS, `_USE_STR_ARG(10)
`define _12_ARGS        `_11_ARGS, `_USE_STR_ARG(11)
`define _13_ARGS        `_12_ARGS, `_USE_STR_ARG(12)
`define _14_ARGS        `_13_ARGS, `_USE_STR_ARG(13)
`define _15_ARGS        `_14_ARGS, `_USE_STR_ARG(14)
`define _16_ARGS        `_15_ARGS, `_USE_STR_ARG(15)
`define _17_ARGS        `_16_ARGS, `_USE_STR_ARG(16)
`define _18_ARGS        `_17_ARGS, `_USE_STR_ARG(17)
`define _19_ARGS        `_18_ARGS, `_USE_STR_ARG(18)
`define _20_ARGS        `_19_ARGS, `_USE_STR_ARG(19)
`define _21_ARGS        `_20_ARGS, `_USE_STR_ARG(20)
`define _22_ARGS        `_21_ARGS, `_USE_STR_ARG(21)
`define _23_ARGS        `_22_ARGS, `_USE_STR_ARG(22)
`define _24_ARGS        `_23_ARGS, `_USE_STR_ARG(23)
`define _25_ARGS        `_24_ARGS, `_USE_STR_ARG(24)
`define _26_ARGS        `_25_ARGS, `_USE_STR_ARG(25)
`define _27_ARGS        `_26_ARGS, `_USE_STR_ARG(26)
`define _28_ARGS        `_27_ARGS, `_USE_STR_ARG(27)
`define _29_ARGS        `_28_ARGS, `_USE_STR_ARG(28)
`define _30_ARGS        `_29_ARGS, `_USE_STR_ARG(29)
`define _31_ARGS        `_30_ARGS, `_USE_STR_ARG(30)
`define _32_ARGS        `_31_ARGS, `_USE_STR_ARG(31)
`define _ADD_ARGS(n)    `_``n``_ARGS

interface sw_logger_if #(
  // width of the data bus
  parameter int unsigned AddrDataWidth = 32
) (
  input logic clk_i,
  input logic rst_ni,
  input logic wr_valid,                 // Qualified write access.
  input logic [AddrDataWidth-1:0] addr, // Incoming addr.
  input logic [AddrDataWidth-1:0] data  // Incoming data.
);

`ifdef UVM
  import uvm_pkg::*;
`endif
  import str_utils_pkg::*;

  // macro includes
  `include "dv_macros.svh"

  // Address to which the SW logs are written to. This is set by the testbench.
  logic [AddrDataWidth-1:0] sw_log_addr;

  // Validate the incoming write address.
  logic data_valid;
  assign data_valid = wr_valid && (addr == sw_log_addr);

  // Enable signal to turn on/off logging at runtime.
  bit enable = 1'b1;

  // types
  // log & rodata database files for parsing, associated with the sw_name
  string sw_log_db_files[string];
  string sw_rodata_db_files[string];

  // typedef addr / data values
  typedef bit [AddrDataWidth-1:0] addr_data_t;

  typedef enum {
    LogSeverityInfo,
    LogSeverityWarning,
    LogSeverityError,
    LogSeverityFatal
  } log_severity_e;

  typedef enum {
    LogVerbosityNone,
    LogVerbosityLow,
    LogVerbosityMedium,
    LogVerbosityHigh,
    LogVerbosityFull,
    LogVerbosityDebug
  } log_verbosity_e;

  // struct to hold the complete log data
  typedef struct {
    string          name;         // Name of the SW image.
    log_severity_e  severity;
    log_verbosity_e verbosity;
    string          file;         // Name of the C file invoking the log.
    int             line;         // Line no in the C file from where the log originated.
    int             nargs;        // Number of args provided to the format string.
    addr_data_t     arg[];        // actual arg values
    string          str_arg[int]; // some args are strings - this AA holds it
    string          format;       // formatted string
  } sw_log_t;

  // bit to enable writing the logs to a separate file (disabled by default)
  bit write_sw_logs_to_file = 1'b0;
  string sw_logs_output_file;
  int sw_logs_output_fd = 0;

  // signal indicating all initializations are done (this is set by calling ready() function)
  bit _ready;

  // hash of log with sw_name and addr keys
  sw_log_t sw_logs[string][addr_data_t];

  // hash of rodata with sw_name and addr keys
  string sw_rodata[string][addr_data_t];

  // q of values obtained from the bus
  addr_data_t addr_data_q[$];

  // Indicate when the log was printed and what was the final string.
  event  printed_log_event;
  string printed_log;

  // Sets the sw_name with the provided path.
  //
  // The sw_name is assumed to be the full path to the SW image (example: /path/to/sometest.elf).
  // The logger expects two files to be available in the same directory as the image -
  // <sw_name>.logs.txt: contains logs split as fields of `sw_log_t`
  // <sw_name>.rodata.txt: contains constants from the read-only sections.
  // These are generated by `util/device_sw_utils/extract_sw_logs.py`. The meson build system
  // already generates it for the 'sim_dv' build device.
  function automatic void add_sw_log_db(string sw_image);
    string sw_dir;
    string sw_basename;
    if (_ready) `dv_fatal("This function cannot be called after calling ready()")
    sw_dir = str_utils_pkg::str_path_dirname(sw_image);
    sw_basename = str_utils_pkg::str_path_basename(.filename(sw_image), .drop_extn(1'b1));
    sw_log_db_files[sw_basename] = {sw_dir, "/", sw_basename, ".logs.txt"};
    sw_rodata_db_files[sw_basename] = {sw_dir, "/", sw_basename, ".rodata.txt"};
  endfunction

  // signal to indicate that this monitor is good to go - all initializations are done
  function automatic void ready();
    _ready = 1'b1;
  endfunction

  /********************/
  /* Monitoring logic */
  /********************/
  initial begin
    wait(_ready);
    if (parse_sw_log_file()) begin
      if (write_sw_logs_to_file) begin
        sw_logs_output_file = $sformatf("%m.log");
        sw_logs_output_fd = $fopen(sw_logs_output_file, "w");
      end
      fork
        get_addr_data_from_bus();
        construct_log_and_print();
      join_none
    end
  end

  final begin
    if (sw_logs_output_fd) $fclose(sw_logs_output_fd);
  end

  /******************/
  /* helper methods */
  /******************/
  // function that parses the log data file
  // returns 1 if log data is avaiable, else false
  function automatic bit parse_sw_log_file();
    bit result;

    // Iterate over the available sw names.
    foreach (sw_log_db_files[sw]) begin
      int fd;
      fd = $fopen(sw_log_db_files[sw], "r");
      if (!fd) continue;

      while (!$feof(fd)) begin
        string        field;
        addr_data_t   addr;
        sw_log_t      sw_log;
        bit           status;

        sw_log.name = sw;
        status = get_sw_log_field(fd, "addr", field);
        // We proceed to retrieving other fields only if we get the addr.
        if (!status) break;
        addr = field.atohex();
        void'(get_sw_log_field(fd, "severity", field));
        sw_log.severity = log_severity_e'(field.atoi());
        void'(get_sw_log_field(fd, "file", field));
        sw_log.file = field;
        void'(get_sw_log_field(fd, "line", field));
        sw_log.line = field.atoi();
        void'(get_sw_log_field(fd, "nargs", field));
        sw_log.nargs = field.atoi();
        sw_log.arg = new[sw_log.nargs];
        void'(get_sw_log_field(fd, "format", field));
        // Replace CRs in the middle of the string with NLs.
        sw_log.format = replace_cr_with_nl(field);
        void'(get_sw_log_field(fd, "str_arg_idx", field));

        begin
          int indices[$];
          get_str_arg_indices(field, indices);
          foreach (indices[i]) begin
            sw_log.str_arg[indices[i]] = "";
          end
        end

        if (sw_logs.exists(sw) && sw_logs[sw].exists(addr)) begin
          `dv_warning($sformatf("Log entry for addr %0x already exists:\nOld: %p\nNew: %p",
                                addr, sw_logs[sw][addr], sw_log))
        end
        sw_logs[sw][addr] = sw_log;
      end
      $fclose(fd);

      if (sw_logs.exists(sw) && sw_logs[sw].size() > 0) begin
        void'(parse_sw_rodata_file(sw));
        result = 1'b1;
      end
    end

    // print parsed logs
    foreach (sw_logs[sw, addr]) begin
      `dv_info($sformatf("sw_logs[%0s][%0h] = %p", sw, addr, sw_logs[sw][addr]), UVM_HIGH)
    end

    return result;
  endfunction

  function automatic bit parse_sw_rodata_file(string sw);
    int fd;
    fd = $fopen(sw_rodata_db_files[sw], "r");
    if (!fd) return 0;

    while (!$feof(fd)) begin
      string        field;
      addr_data_t   addr;
      bit           status;

      status = get_sw_log_field(fd, "addr", field);
      // We proceed to retrieving other fields only if we get the addr.
      if (!status) break;
      addr = field.atohex();
      void'(get_sw_log_field(fd, "string", field));

      if (sw_rodata.exists(sw) && sw_rodata[sw].exists(addr)) begin
        `dv_warning($sformatf("Rodata entry for addr %0x already exists:\nOld: %s\nNew: %s",
                              addr, sw_rodata[sw][addr], field))
      end
      // Replace CRs in the middle of the string with NLs.
      sw_rodata[sw][addr] = replace_cr_with_nl(field);
    end
    $fclose(fd);

    // print parsed rodata
    foreach (sw_rodata[sw, addr]) begin
      `dv_info($sformatf("sw_rodata[%0s][%0h] = %p", sw, addr, sw_rodata[sw][addr]), UVM_HIGH)
    end

    return (sw_rodata[sw].size() > 0);
  endfunction

  // Get the sw log fields by parsing line-by-line.
  // The ref arg value is used to return the retrived field.
  // Function returns the successfulness of the operation.
  function automatic bit get_sw_log_field(int fd, string field, ref string value);
    byte   lf    = 8'ha;
    byte   cr    = 8'hd;
    string match = {field, ": *"};

    value = "";
    while (!$feof(fd)) begin
      string line;
      void'($fgets(line, fd));
      // Chomp the trailing newlines.
      while (byte'(line.getc(line.len() - 1)) inside {lf, cr}) begin
        line = line.substr(0, line.len() - 2);
      end
      if (line == "") continue;
      // Check if field exists
      if (!uvm_re_match(match, line)) begin
        value = line.substr(match.len() - 1, line.len() - 1);
        return 1'b1;
      end
      else begin
        return 1'b0;
      end
    end
    return 1'b0;
  endfunction

  // Parse list if indices that have string args (in string format as space separated values
  // and return a queue of corresponding integers.
  function automatic void get_str_arg_indices(string list, ref int indices[$]);
    int i;
    int start = 0;
    indices.delete();
    if (list == "") return;
    for (i = 0; i < list.len(); i++) begin
      if (list.getc(i) == " " && i == start) begin
        start++;
        continue;
      end
      else if (list.getc(i) == " ") begin
        string index = list.substr(start, i - 1);
        indices.push_back(index.atoi());
        start = i + 1;
      end
    end
    if (start < i) begin
      string index = list.substr(start, i - 1);
      indices.push_back(index.atoi());
    end
  endfunction

  // replace carriage return in the middle of the string with newline.
  function automatic string replace_cr_with_nl(string text);
    byte cr = 8'hd;
    byte lf = 8'ha;
    if (text.len() >= 2) begin
      for (int i = 0; i < text.len() - 1; i++) begin
        if (byte'(text.getc(i)) == cr) begin
          text.putc(i, lf);
        end
      end
    end
    return text;
  endfunction

  // Retrieve the string at the specified addr.
  function automatic string get_str_at_addr(string sw, addr_data_t addr);
    if (sw_rodata[sw].exists(addr)) return sw_rodata[sw][addr];
    // The string could start midway from an existing addr entry.
    foreach (sw_rodata[sw][str_addr]) begin
      addr_data_t limit = sw_rodata[sw][str_addr].len() - 1;
      if (addr inside {[str_addr : str_addr + limit]}) begin
        return sw_rodata[sw][str_addr].substr(addr - str_addr, limit);
      end
    end
    // If no string was found at the provided addr, then return the addr converted to string.
    begin
      string result;
      result.hextoa(addr);
      return result;
    end
  endfunction

  // retrieve addr or data from the bus
  task automatic get_addr_data_from_bus();
    forever begin
      @(posedge clk_i or negedge rst_ni);
      if (!rst_ni) begin
        addr_data_q.delete();
        wait(rst_ni);
      end else begin
        if (enable && data_valid) begin
          addr_data_q.push_back(data);
        end
      end
    end
  endtask

  //construct log and print when complete data is available
  task automatic construct_log_and_print();
    forever begin
      addr_data_t addr;
      // get addr
      wait(addr_data_q.size() > 0);
      addr = addr_data_q.pop_front();

      // lookup addr in sw_logs
      foreach (sw_logs[sw]) begin
        if (sw_logs[sw].exists(addr)) begin
          bit rst_occurred;
          fork
            begin
              fork
                // get args
                for (int i = 0; i < sw_logs[sw][addr].nargs; i++) begin
                  wait(addr_data_q.size() > 0);
                  sw_logs[sw][addr].arg[i] = addr_data_q.pop_front();
                  // Check if this is an str arg
                  if (sw_logs[sw][addr].str_arg.exists(i)) begin
                    // The arg[i] received is the addr in rodata where the string resides.
                    sw_logs[sw][addr].str_arg[i] = get_str_at_addr(sw, sw_logs[sw][addr].arg[i]);
                    `dv_info($sformatf("String arg at addr %0h: %0s", sw_logs[sw][addr].arg[i],
                                       sw_logs[sw][addr].str_arg[i]), UVM_DEBUG)
                  end
                end
                begin
                  // check if rst_ni occurred - in that case discard and start over
                  wait(rst_ni === 1'b0);
                  rst_occurred = 1'b1;
                end
              join_any
              disable fork;
            end
          join
          if (rst_occurred) continue;
          print_sw_log(sw_logs[sw][addr]);
        end
      end
    end
  endtask

  // print the log captured from the SW.
  function automatic void print_sw_log(sw_log_t sw_log);
    string log_header = sw_log.name;
    if (sw_log.file != "") begin
      // Append the SW file and line to the header.
      log_header = {log_header, "(", sw_log.file, ":",
                    $sformatf("%0d", sw_log.line), ")"};
    end

    // construct formatted string based on args
    case (sw_log.nargs)
       0: ;
       1: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(1));
       2: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(2));
       3: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(3));
       4: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(4));
       5: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(5));
       6: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(6));
       7: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(7));
       8: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(8));
       9: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(9));
      10: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(10));
      11: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(11));
      12: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(12));
      13: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(13));
      14: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(14));
      15: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(15));
      16: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(16));
      17: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(17));
      18: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(18));
      19: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(19));
      20: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(20));
      21: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(21));
      22: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(22));
      23: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(23));
      24: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(24));
      25: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(25));
      26: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(26));
      27: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(27));
      28: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(28));
      29: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(29));
      30: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(30));
      31: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(31));
      32: sw_log.format = $sformatf(sw_log.format, `_ADD_ARGS(32));
      default: `dv_fatal($sformatf("UNSUPPORTED: nargs = %0d (only 0:32 allowed)", sw_log.nargs))
    endcase

    begin
`ifdef UVM
      uvm_verbosity level;
      case (sw_log.verbosity)
        LogVerbosityNone:   level = UVM_NONE;
        LogVerbosityLow:    level = UVM_LOW;
        LogVerbosityMedium: level = UVM_MEDIUM;
        LogVerbosityHigh:   level = UVM_HIGH;
        LogVerbosityFull:   level = UVM_FULL;
        LogVerbosityDebug:  level = UVM_DEBUG;
        default:            level = UVM_LOW;
      endcase
`endif
      case (sw_log.severity)
        LogSeverityInfo:    `dv_info(sw_log.format, level, log_header)
        LogSeverityWarning: `dv_warning(sw_log.format, log_header)
        LogSeverityError:   `dv_error(sw_log.format, log_header)
        LogSeverityFatal:   `dv_fatal(sw_log.format, log_header)
        default:            `dv_info(sw_log.format, level, log_header)
      endcase
    end

    // write sw log to file if enabled
    if (sw_logs_output_fd) begin
      $fwrite(sw_logs_output_fd, "[%15t]: [%0s] %0s\n", $time, log_header, sw_log.format);
    end

    printed_log = sw_log.format;
    ->printed_log_event;
  endfunction

endinterface

// undefine previously defined macros
`undef _USE_STR_ARG
`undef _1_ARGS
`undef _2_ARGS
`undef _3_ARGS
`undef _4_ARGS
`undef _5_ARGS
`undef _6_ARGS
`undef _7_ARGS
`undef _8_ARGS
`undef _9_ARGS
`undef _10_ARGS
`undef _11_ARGS
`undef _12_ARGS
`undef _13_ARGS
`undef _14_ARGS
`undef _15_ARGS
`undef _16_ARGS
`undef _17_ARGS
`undef _18_ARGS
`undef _19_ARGS
`undef _20_ARGS
`undef _21_ARGS
`undef _22_ARGS
`undef _23_ARGS
`undef _24_ARGS
`undef _25_ARGS
`undef _26_ARGS
`undef _27_ARGS
`undef _28_ARGS
`undef _29_ARGS
`undef _30_ARGS
`undef _31_ARGS
`undef _32_ARGS
`undef _ADD_ARGS
