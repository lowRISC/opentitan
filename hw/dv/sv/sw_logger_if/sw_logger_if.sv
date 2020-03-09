// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// shortcuts for use in switching # of args to insert in formatted string
`define _0_ARGS(a)
`define _1_ARGS(a)                  , a[0]
`define _2_ARGS(a)                  `_1_ARGS(a), a[1]
`define _3_ARGS(a)                  `_2_ARGS(a), a[2]
`define _4_ARGS(a)                  `_3_ARGS(a), a[3]
`define _5_ARGS(a)                  `_4_ARGS(a), a[4]
`define _6_ARGS(a)                  `_5_ARGS(a), a[5]
`define _7_ARGS(a)                  `_6_ARGS(a), a[6]
`define _8_ARGS(a)                  `_7_ARGS(a), a[7]
`define _9_ARGS(a)                  `_8_ARGS(a), a[8]
`define _10_ARGS(a)                 `_9_ARGS(a), a[9]
`define _11_ARGS(a)                 `_10_ARGS(a), a[10]
`define _12_ARGS(a)                 `_11_ARGS(a), a[11]
`define _13_ARGS(a)                 `_12_ARGS(a), a[12]
`define _14_ARGS(a)                 `_13_ARGS(a), a[13]
`define _15_ARGS(a)                 `_14_ARGS(a), a[14]
`define _16_ARGS(a)                 `_15_ARGS(a), a[15]
`define _17_ARGS(a)                 `_16_ARGS(a), a[16]
`define _18_ARGS(a)                 `_17_ARGS(a), a[17]
`define _19_ARGS(a)                 `_18_ARGS(a), a[18]
`define _20_ARGS(a)                 `_19_ARGS(a), a[19]
`define _21_ARGS(a)                 `_20_ARGS(a), a[20]
`define _22_ARGS(a)                 `_21_ARGS(a), a[21]
`define _23_ARGS(a)                 `_22_ARGS(a), a[22]
`define _24_ARGS(a)                 `_23_ARGS(a), a[23]
`define _25_ARGS(a)                 `_24_ARGS(a), a[24]
`define _26_ARGS(a)                 `_25_ARGS(a), a[25]
`define _27_ARGS(a)                 `_26_ARGS(a), a[26]
`define _28_ARGS(a)                 `_27_ARGS(a), a[27]
`define _29_ARGS(a)                 `_28_ARGS(a), a[28]
`define _30_ARGS(a)                 `_29_ARGS(a), a[29]
`define _31_ARGS(a)                 `_30_ARGS(a), a[30]
`define _32_ARGS(a)                 `_31_ARGS(a), a[31]
`define _ADD_ARGS(a, n)             `_``n``_ARGS(a)
`define FORMATTED_LOG_WITH_NARGS(n) $sformatf(log `_ADD_ARGS(sw_log.arg, n))

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
  // image name and log file for parsing
  string sw_name;
  string sw_log_file;

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
    string          file;       // Name of the C file invoking the log.
    int             line;       // Line no in the C file from where the log originated.
    int             nargs;      // Number of args provided to the format string.
    addr_data_t     arg[];      // actual arg values
    string          format;     // formatted string
  } sw_log_t;

  // signal indicating all initializations are done (this is set by calling ready() function)
  bit _ready;

  // hash of log with addr key
  sw_log_t sw_logs[addr_data_t];

  // q of values obtained from the bus
  addr_data_t addr_data_q[$];

  // function to add the log dat files
  function automatic void set_sw_log_file(string _sw_name, string _sw_log_file);
    if (_ready) log_fatal(.log("this function cannot be called after calling ready()"));
    sw_name = _sw_name;
    sw_log_file = _sw_log_file;
  endfunction

  // signal to indicate all monitor is good to go - all initializations are done
  function automatic void ready();
    _ready = 1'b1;
  endfunction

  /********************/
  /* Monitoring logic */
  /********************/
  initial begin
    wait(_ready);
    if (parse_sw_log_file()) begin
      fork
        get_addr_data_from_bus();
        construct_log_and_print();
      join_none
    end
  end

  /******************/
  /* helper methods */
  /******************/
  // function that parses the log data file
  // returns 1 if log data is avaiable, else false
  function automatic bit parse_sw_log_file();
    int fd;
    fd = $fopen(sw_log_file, "r");
    if (!fd) return 0;

    while (!$feof(fd)) begin
      string        field;
      addr_data_t   addr;
      sw_log_t      sw_log;
      bit           status;

      sw_log.name = sw_name;
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
      sw_log.format = field;

      if (sw_logs.exists(addr)) begin
        log_warning($sformatf("Log entry for addr %0x already exists:\nOld: %p\nNew: %p",
                              addr, sw_logs[addr], sw_log));
      end
      sw_logs[addr] = sw_log;
    end
    $fclose(fd);

    // cleanup the format of all logs
    cleanup_format();

    // print parsed logs
    foreach (sw_logs[addr]) begin
      log_info(.verbosity(LogVerbosityHigh),
               .log($sformatf("sw_logs[%0h] = %p", addr, sw_logs[addr])));
    end

    return (sw_logs.size() > 0);
  endfunction

  // Get the sw log fields by parsing line-by-line.
  // The ref arg value is used to return the retrived field.
  // Function returns the successfulness of the operation.
  function automatic bit get_sw_log_field(int fd, string field, ref string value);
    byte   lf    = 8'ha;
    byte   cr    = 8'hd;
    string match = {field, ": *"};

    while (!$feof(fd)) begin
      string line;
      void'($fgets(line, fd));
      // Chomp the trailing newlines.
      while (byte'(line.getc(line.len() - 1)) inside {lf, cr}) begin
        line = line.substr(0, line.len() - 2);
      end
      if (line == "") continue;
      // check if field exists
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

  // function to cleanup the string formatting
  function automatic void cleanup_format();
    byte cr = 8'hd;
    byte lf = 8'ha;
    foreach (sw_logs[addr]) begin
      string str = sw_logs[addr].format;
      if (str.len() >= 2) begin
        for (int i = 0; i < str.len() - 1; i++) begin
          // replace carriage return in the middle of the string with newline.
          if (byte'(str.getc(i)) == cr) begin
            str.putc(i, lf);
          end
        end
      end
      sw_logs[addr].format = str;
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
      if (sw_logs.exists(addr)) begin
        bit rst_occurred;
        fork
          begin
            fork
              // get args
              for (int i = 0; i < sw_logs[addr].nargs; i++) begin
                wait(addr_data_q.size() > 0);
                sw_logs[addr].arg[i] = addr_data_q.pop_front();
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
        print_sw_log(sw_logs[addr]);
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
    print_log(sw_log);
  endfunction

  // print logs from this file.
  function automatic void print_self_log(log_severity_e severity,
                                         log_verbosity_e verbosity = LogVerbosityLow,
                                         string log);
    sw_log_t self_log;
    self_log.name = $sformatf("sw_logger_if[%0s]", sw_name);
    self_log.severity = severity;
    self_log.verbosity = verbosity;
    self_log.file = "";
    self_log.format = log;
    print_log(self_log);
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
  function automatic void print_log(sw_log_t sw_log);
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
      LogSeverityInfo:    $info("%0t: [%0s] %0s", $time, log_header, sw_log.format);
      LogSeverityWarning: $warning("%0t: [%0s] %0s", $time, log_header, sw_log.format);
      LogSeverityError:   $error("%0t: [%0s] %0s", $time, log_header, sw_log.format);
      LogSeverityFatal:   $fatal("%0t: [%0s] %0s", $time, log_header, sw_log.format);
      default:            $info("%0t: [%0s] %0s", $time, log_header, sw_log.format);
    endcase
`endif
  endfunction

endinterface

// undefine previously defined macros
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
