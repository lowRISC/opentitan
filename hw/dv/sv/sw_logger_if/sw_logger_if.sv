// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// shortcuts for use in switching # of args to insert in formatted string
`define _USE_STR_ARG(a, n)          (a.str_arg.exists(``n``) ? a.str_arg[``n``] : a.arg[``n``])
`define _0_ARGS(a)
`define _1_ARGS(a)                  , `_USE_STR_ARG(a, 0)
`define _2_ARGS(a)                  `_1_ARGS(a), `_USE_STR_ARG(a, 1)
`define _3_ARGS(a)                  `_2_ARGS(a), `_USE_STR_ARG(a, 2)
`define _4_ARGS(a)                  `_3_ARGS(a), `_USE_STR_ARG(a, 3)
`define _5_ARGS(a)                  `_4_ARGS(a), `_USE_STR_ARG(a, 4)
`define _6_ARGS(a)                  `_5_ARGS(a), `_USE_STR_ARG(a, 5)
`define _7_ARGS(a)                  `_6_ARGS(a), `_USE_STR_ARG(a, 6)
`define _8_ARGS(a)                  `_7_ARGS(a), `_USE_STR_ARG(a, 7)
`define _9_ARGS(a)                  `_8_ARGS(a), `_USE_STR_ARG(a, 8)
`define _10_ARGS(a)                 `_9_ARGS(a), `_USE_STR_ARG(a, 9)
`define _11_ARGS(a)                 `_10_ARGS(a), `_USE_STR_ARG(a, 10)
`define _12_ARGS(a)                 `_11_ARGS(a), `_USE_STR_ARG(a, 11)
`define _13_ARGS(a)                 `_12_ARGS(a), `_USE_STR_ARG(a, 12)
`define _14_ARGS(a)                 `_13_ARGS(a), `_USE_STR_ARG(a, 13)
`define _15_ARGS(a)                 `_14_ARGS(a), `_USE_STR_ARG(a, 14)
`define _16_ARGS(a)                 `_15_ARGS(a), `_USE_STR_ARG(a, 15)
`define _17_ARGS(a)                 `_16_ARGS(a), `_USE_STR_ARG(a, 16)
`define _18_ARGS(a)                 `_17_ARGS(a), `_USE_STR_ARG(a, 17)
`define _19_ARGS(a)                 `_18_ARGS(a), `_USE_STR_ARG(a, 18)
`define _20_ARGS(a)                 `_19_ARGS(a), `_USE_STR_ARG(a, 19)
`define _21_ARGS(a)                 `_20_ARGS(a), `_USE_STR_ARG(a, 20)
`define _22_ARGS(a)                 `_21_ARGS(a), `_USE_STR_ARG(a, 21)
`define _23_ARGS(a)                 `_22_ARGS(a), `_USE_STR_ARG(a, 22)
`define _24_ARGS(a)                 `_23_ARGS(a), `_USE_STR_ARG(a, 23)
`define _25_ARGS(a)                 `_24_ARGS(a), `_USE_STR_ARG(a, 24)
`define _26_ARGS(a)                 `_25_ARGS(a), `_USE_STR_ARG(a, 25)
`define _27_ARGS(a)                 `_26_ARGS(a), `_USE_STR_ARG(a, 26)
`define _28_ARGS(a)                 `_27_ARGS(a), `_USE_STR_ARG(a, 27)
`define _29_ARGS(a)                 `_28_ARGS(a), `_USE_STR_ARG(a, 28)
`define _30_ARGS(a)                 `_29_ARGS(a), `_USE_STR_ARG(a, 29)
`define _31_ARGS(a)                 `_30_ARGS(a), `_USE_STR_ARG(a, 30)
`define _32_ARGS(a)                 `_31_ARGS(a), `_USE_STR_ARG(a, 31)
`define _ADD_ARGS(a, n)             `_``n``_ARGS(a)
`define FORMATTED_LOG_WITH_NARGS(n) $sformatf(log `_ADD_ARGS(sw_log, n))

interface sw_logger_if #(
  // width of the data bus
  parameter int unsigned DATA_WIDTH = 32
) (
  input logic                   clk,        // clock
  input logic                   rst_n,      // active low reset
  input logic                   valid,      // qualification for addr_data
  input logic [DATA_WIDTH-1:0]  addr_data,  // addr/data written to sw_log_addr
  output logic [DATA_WIDTH-1:0] sw_log_addr // used by external logic to qualify valid
);

`ifdef UVM
  import uvm_pkg::*;
  `include "uvm_macros.svh"
`endif

  // Enable signal to turn on/off logging at runtime.
  bit enable = 1'b1;

  // types
  // log & rodata database files for parsing, associated with the sw_name
  string sw_log_db_files[string];
  string sw_rodata_db_files[string];

  // typedef addr / data values
  typedef bit [DATA_WIDTH-1:0] addr_data_t;

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
    string          name;       // Name of the SW image.
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

  // Set the sw_name, The logger assumes that there are two files placed in the rundir -
  // <sw_name>_logs.txt: contains logs split as fields of `sw_log_t`
  // <sw_name>_rodata.txt: contains constants from the read-only sections.
  function automatic void set_sw_name(string sw_name);
    if (_ready) log_fatal(.log("this function cannot be called after calling ready()"));
    sw_log_db_files[sw_name] = {sw_name, "_logs.txt"};
    sw_rodata_db_files[sw_name] = {sw_name, "_rodata.txt"};
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
          log_warning($sformatf("Log entry for addr %0x already exists:\nOld: %p\nNew: %p",
                                addr, sw_logs[sw][addr], sw_log));
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
      log_info(.verbosity(LogVerbosityHigh),
               .log($sformatf("sw_logs[%0s][%0h] = %p", sw, addr, sw_logs[sw][addr])));
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
        log_warning($sformatf("Rodata entry for addr %0x already exists:\nOld: %s\nNew: %s",
                              addr, sw_rodata[sw][addr], field));
      end
      // Replace CRs in the middle of the string with NLs.
      sw_rodata[sw][addr] = replace_cr_with_nl(field);
    end
    $fclose(fd);

    // print parsed rodata
    foreach (sw_rodata[sw, addr]) begin
      log_info(.verbosity(LogVerbosityHigh),
               .log($sformatf("sw_rodata[%0s][%0h] = %p", sw, addr, sw_rodata[sw][addr])));
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
      @(posedge clk);
      if (enable && valid === 1'b1 && rst_n !== 0) begin
        addr_data_q.push_back(addr_data);
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
                    log_info(.verbosity(LogVerbosityDebug),
                             .log($sformatf("String arg at addr %0h: %0s",
                                            sw_logs[sw][addr].arg[i],
                                            sw_logs[sw][addr].str_arg[i])));
                  end
                end
                begin
                  // check if rst_n occurred - in that case discard and start over
                  wait(rst_n === 1'b0);
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
    string log = sw_log.format;

    // construct formatted string based on args
    case (sw_log.nargs)
       0: log = `FORMATTED_LOG_WITH_NARGS(0);
       1: log = `FORMATTED_LOG_WITH_NARGS(1);
       2: log = `FORMATTED_LOG_WITH_NARGS(2);
       3: log = `FORMATTED_LOG_WITH_NARGS(3);
       4: log = `FORMATTED_LOG_WITH_NARGS(4);
       5: log = `FORMATTED_LOG_WITH_NARGS(5);
       6: log = `FORMATTED_LOG_WITH_NARGS(6);
       7: log = `FORMATTED_LOG_WITH_NARGS(7);
       8: log = `FORMATTED_LOG_WITH_NARGS(8);
       9: log = `FORMATTED_LOG_WITH_NARGS(9);
      10: log = `FORMATTED_LOG_WITH_NARGS(10);
      11: log = `FORMATTED_LOG_WITH_NARGS(11);
      12: log = `FORMATTED_LOG_WITH_NARGS(12);
      13: log = `FORMATTED_LOG_WITH_NARGS(13);
      14: log = `FORMATTED_LOG_WITH_NARGS(14);
      15: log = `FORMATTED_LOG_WITH_NARGS(15);
      16: log = `FORMATTED_LOG_WITH_NARGS(16);
      17: log = `FORMATTED_LOG_WITH_NARGS(17);
      18: log = `FORMATTED_LOG_WITH_NARGS(18);
      19: log = `FORMATTED_LOG_WITH_NARGS(19);
      20: log = `FORMATTED_LOG_WITH_NARGS(20);
      21: log = `FORMATTED_LOG_WITH_NARGS(21);
      22: log = `FORMATTED_LOG_WITH_NARGS(22);
      23: log = `FORMATTED_LOG_WITH_NARGS(23);
      24: log = `FORMATTED_LOG_WITH_NARGS(24);
      25: log = `FORMATTED_LOG_WITH_NARGS(25);
      26: log = `FORMATTED_LOG_WITH_NARGS(26);
      27: log = `FORMATTED_LOG_WITH_NARGS(27);
      28: log = `FORMATTED_LOG_WITH_NARGS(28);
      29: log = `FORMATTED_LOG_WITH_NARGS(29);
      30: log = `FORMATTED_LOG_WITH_NARGS(30);
      31: log = `FORMATTED_LOG_WITH_NARGS(31);
      32: log = `FORMATTED_LOG_WITH_NARGS(32);
    default: log_fatal($sformatf("UNSUPPORTED: nargs = %0d (only 0:32 allowed)", sw_log.nargs));
    endcase
    sw_log.format = log;
    print_log(.sw_log(sw_log), .is_sw_log(1'b1));
    printed_log = log;
    ->printed_log_event;
  endfunction

  // print logs from this file.
  function automatic void print_self_log(log_severity_e severity,
                                         log_verbosity_e verbosity = LogVerbosityLow,
                                         string log);
    sw_log_t self_log;
    self_log.name = "sw_logger_if";
    self_log.severity = severity;
    self_log.verbosity = verbosity;
    self_log.file = "";
    self_log.format = log;
    print_log(.sw_log(self_log));
  endfunction

  // print an info message from this file
  function automatic void log_info(log_verbosity_e verbosity = LogVerbosityLow, string log);
    print_self_log(.severity(LogSeverityInfo), .verbosity(verbosity), .log(log));
  endfunction

  // print a warning message from this file
  function automatic void log_warning(string log);
    print_self_log(.severity(LogSeverityWarning), .log(log));
  endfunction

  // print an error message from this file
  function automatic void log_error(string log);
    print_self_log(.severity(LogSeverityError), .log(log));
  endfunction

  // print a fatal message from this file
  function automatic void log_fatal(string log);
    print_self_log(.severity(LogSeverityFatal), .log(log));
  endfunction

  // UVM-agnostic print_log api that switches between system call and UVM call
  function automatic void print_log(sw_log_t sw_log, bit is_sw_log = 1'b0);
    string log_header = sw_log.name;
    if (sw_log.file != "") begin
      log_header = {log_header, "(", sw_log.file, ":",
                    $sformatf("%0d", sw_log.line), ")"};
    end
`ifdef UVM
    begin
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

      case (sw_log.severity)
        LogSeverityInfo:    `uvm_info(log_header, sw_log.format, level)
        LogSeverityWarning: `uvm_error(log_header, sw_log.format)
        LogSeverityError:   `uvm_error(log_header, sw_log.format)
        LogSeverityFatal:   `uvm_fatal(log_header, sw_log.format)
        default:            `uvm_info(log_header, sw_log.format, level)
      endcase
    end
`else
    case (sw_log.severity)
      LogSeverityInfo:    $info("[%15t]: [%0s] %0s", $time, log_header, sw_log.format);
      LogSeverityWarning: $warning("[%15t]: [%0s] %0s", $time, log_header, sw_log.format);
      LogSeverityError:   $error("[%15t]: [%0s] %0s", $time, log_header, sw_log.format);
      LogSeverityFatal:   $fatal("[%15t]: [%0s] %0s", $time, log_header, sw_log.format);
      default:            $info("[%15t]: [%0s] %0s", $time, log_header, sw_log.format);
    endcase
`endif
    // write sw log to file if enabled
    if (is_sw_log && sw_logs_output_fd) begin
      $fwrite(sw_logs_output_fd, "[%15t]: [%0s] %0s\n", $time, log_header, sw_log.format);
    end
  endfunction

endinterface

// undefine previously defined macros
`undef _USE_STR_ARG
`undef _0_ARGS
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
`undef FORMATTED_LOG_WITH_NARGS
