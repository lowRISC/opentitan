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
`define FORMATTED_MSG_WITH_NARGS(n) $sformatf(msg `_ADD_ARGS(sw_msg.arg, n))

interface sw_msg_monitor_if #(
  // width of the data bus
  parameter int unsigned DATA_WIDTH = 32
) (
  input logic                   clk,        // clock
  input logic                   rst_n,      // active low reset
  input logic                   valid,      // qualification for addr_data
  input logic [DATA_WIDTH-1:0]  addr_data,  // addr/data written to sw_msg_addr
  output logic [DATA_WIDTH-1:0] sw_msg_addr // used by external logic to qualify valid
);

  // types
  // struct to hold sw msg data file and name
  typedef struct {
    string name;
    string file;
  } sw_msg_data_file_t;

  // typedef addr / data values
  typedef bit [DATA_WIDTH-1:0] addr_data_t;

  // struct to hold the complete msg data
  typedef struct {
    string      msg_type;   // info, warning, error or fatal
    string      verbosity;  // none, low, medium, high, full, debug
    string      name;       // sw name
    string      file;       // name of C file
    int         line;       // line no
    string      header;     // custom header (else its [name](file:line))
    int         nargs;      // no of args
    addr_data_t arg[];      // actual arg values
    string      format;     // formatted string
  } sw_msg_t;

  // index of elements parsed from each line of msg data file
  typedef enum {
    AddrIndex,
    MsgTypeIndex,
    VerbosityIndex,
    FileIndex,
    LineIndex,
    NArgsIndex,
    FormatIndex,
    ArgsIndex
  } sw_msg_fields_index_e;

  // msg scheme
  typedef enum {
    MsgSchemeNone,        // addr\msg (msg might contain additional metadata)
    MsgSchmeCustomHeader, // addr\header\nargs\format
    MsgSchemeDv           // addr\msg_type\verbosity\file\line\nargs\format
  } msg_scheme_e;

  // signal indicating all initializations are done (this is set by calling ready() function)
  bit _ready;

  // single char string delimiter used to segregate the msg data fields
  // by default, this is set to '\' which is 5c in hex
  byte delimiter = 8'h5c;
  string delimiter_str = "";

  // q of input file sources
  sw_msg_data_file_t sw_msg_data_files[$];

  // hash of msg with addr key
  sw_msg_t sw_msgs[addr_data_t];

  // q of values obtained from the bus
  addr_data_t addr_data_q[$];

  /****************************/
  /* Initialization functions */
  /****************************/
  // function to set the delimiter value
  function automatic void set_delimiter(byte value);
    if (_ready) msg_fatal(.msg("this function cannot be called after calling ready()"));
    delimiter = value;
    // update the string version
    // if delimiter is '\' (8'h5c) then the string version
    // needs to be empty since SV treats '\' as null
    delimiter_str.putc(0, delimiter);
    delimiter_str = (delimiter == 8'h5c) ? "" : delimiter_str;
  endfunction

  // function to add the msg dat files
  function automatic void add_sw_msg_data_files(string img_name, string img_file);
    sw_msg_data_file_t sw_msg_data_file;
    if (_ready) msg_fatal(.msg("this function cannot be called after calling ready()"));
    sw_msg_data_file.name = img_name;
    sw_msg_data_file.file = img_file;
    sw_msg_data_files.push_back(sw_msg_data_file);
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
    if (parse_sw_msg_data_files()) begin
      fork
        get_addr_data_from_bus();
        construct_msg_and_print();
      join_none
    end
  end

  /******************/
  /* helper methods */
  /******************/
  // function that parses the msg data file
  // returns 1 if msg data is avaiable, else false
  function automatic bit parse_sw_msg_data_files();
    foreach (sw_msg_data_files[i]) begin
      int fd;
      fd = $fopen(sw_msg_data_files[i].file, "r");
      if (!fd) continue;
      else begin
        addr_data_t addr;

        while (!$feof(fd)) begin
          string       line;
          string       fields[$];
          int          merge_fields_idx_start = 0;
          int          merge_fields_idx_end = 0;
          msg_scheme_e scheme;

          // read line and split into fields based on delimiter
          void'($fgets(line, fd));
          if (line inside {"", "\n", "\r"}) continue;
          split_msg_data_line_to_fields(line, fields);

          // print fields for debug
          foreach (fields[i]) begin
            msg_info(.verbosity("d"), .msg($sformatf("fields[%0d] = %0s", i, fields[i])));
          end

          // get addr (first field)
          addr = fields[AddrIndex].atohex();
          if (sw_msgs.exists(addr)) begin
            msg_warning(.msg($sformatf("msg entry for addr %0x already exists:\n%p",
                                       addr, sw_msgs[addr])));
          end

          // detect msg scheme based on fields size and values
          // if > 7 fields AND fields[MsgTypeIndex] is either "i", "w", "e" or "f"
          // then its DV scheme, otherwise it is something else
          if (fields.size() >= 7) scheme = MsgSchemeDv;
          // Note: If user adds null termination in the msg that is not supported
          if (fields[MsgTypeIndex].tolower() inside {"i", "info"}) begin
            sw_msgs[addr].msg_type = "i";
          end else if (fields[MsgTypeIndex].tolower() inside {"w", "warn", "warning"}) begin
            sw_msgs[addr].msg_type = "w";
          end else if (fields[MsgTypeIndex].tolower() inside {"e", "err", "error"}) begin
            sw_msgs[addr].msg_type = "e";
          end else if (fields[MsgTypeIndex].tolower() inside {"f", "fatal"}) begin
            sw_msgs[addr].msg_type = "f";
          end else begin
            // if fields size >= 4, its a msg with custom header
            // if fields size < 4, there no scheme detected
            if (fields.size() >= 4) scheme = MsgSchmeCustomHeader;
            else                    scheme = MsgSchemeNone;
          end

          case (scheme)
            MsgSchemeNone: begin
              sw_msgs[addr].msg_type = "i";
              sw_msgs[addr].verbosity = "n";
              sw_msgs[addr].file = "";
              sw_msgs[addr].line = 0;
              sw_msgs[addr].nargs = 0;
              sw_msgs[addr].format =  fields[1];
              sw_msgs[addr].name = sw_msg_data_files[i].name;
              merge_fields_idx_start = 2;
            end
            MsgSchmeCustomHeader: begin
              sw_msgs[addr].verbosity = "n";
              sw_msgs[addr].file = "";
              sw_msgs[addr].line = 0;
              sw_msgs[addr].header = fields[1];
              sw_msgs[addr].nargs = fields[2].atoi();
              sw_msgs[addr].arg = new[sw_msgs[addr].nargs];
              sw_msgs[addr].format =  fields[3];
              sw_msgs[addr].name = sw_msg_data_files[i].name;
              merge_fields_idx_start = 4;
            end
            MsgSchemeDv: begin
              // 7 entries: addr, type, verbosity, file, line, nargs, format
              sw_msgs[addr].verbosity = fields[VerbosityIndex];
              sw_msgs[addr].file = fields[FileIndex];
              sw_msgs[addr].line = fields[LineIndex].atoi();
              sw_msgs[addr].nargs = fields[NArgsIndex].atoi();
              sw_msgs[addr].arg = new[sw_msgs[addr].nargs];
              sw_msgs[addr].format = fields[FormatIndex];
              sw_msgs[addr].name = sw_msg_data_files[i].name;
              merge_fields_idx_start = 7;
            end
          endcase
          // its possible that user might have added the delimiter in the msg itself
          // in that case append the remaining ones back into formatted string
          for (int i = merge_fields_idx_start; i < fields.size(); i++) begin
            sw_msgs[addr].format = {sw_msgs[addr].format, delimiter_str, fields[i]};
          end
        end

        // cleanup the format of all msgs
        cleanup_format();

        // print parsed msgs
        foreach (sw_msgs[addr]) begin
          msg_info(.verbosity("h"), .msg($sformatf("sw_msgs[%0h] = %p", addr, sw_msgs[addr])));
        end
      end
      $fclose(fd);
    end
    return (sw_msgs.size() > 0);
  endfunction

    // split string using single character delimiter (as byte)
  function automatic void split_msg_data_line_to_fields(input string  str,
                                                        output string split[$]);
    int start = 0;
    for (int i = 0; i < str.len(); i++) begin
      if (str.getc(i) == delimiter) begin
        split.push_back(str.substr(start, i - 1));
        start = i + 1;
      end
    end
    // last one
    split.push_back(str.substr(start, str.len() - 1));
  endfunction

  // function to cleanup the string formatting
  function automatic void cleanup_format();
    foreach (sw_msgs[addr]) begin
      string str = sw_msgs[addr].format;
      if (str.len() >= 2) begin
        // replace ^M with \n and ^J also with \n (CR is not supported in SV)
        for (int i = 0; i < str.len() - 1; i++) begin
          if (str.getc(i) == "^" && str.getc(i + 1) inside {"M", "J"}) begin
            str = {str.substr(0, i - 1), "\n", str.substr(i + 2, str.len() - 1)};
            i++;
          end
          // replace %x, %d, %h with %0x, %0d and %0h
          if (str.getc(i) == "%" && str.getc(i + 1) inside {"x", "h", "d"}) begin
            str = {str.substr(0, i), "0", str.substr(i + 1, str.len() - 1)};
            i += 2;
          end
        end
      end
      // remove the last \n added by $fgets
      if (str.getc(str.len() - 1) == "\n") begin
        str = str.substr(0, str.len() - 2);
      end
      // remove the last \n added in the print msg
      if (str.getc(str.len() - 1) == "\n") begin
        str = str.substr(0, str.len() - 2);
      end
      sw_msgs[addr].format = str;
    end
  endfunction

    // retrieve addr or data from the bus
  task automatic get_addr_data_from_bus();
    forever begin
      @(posedge clk);
      if (valid === 1'b1 && rst_n !== 0) begin
        addr_data_q.push_back(addr_data);
      end
    end
  endtask

  //construct msg and print when complete data is available
  task automatic construct_msg_and_print();
    forever begin
      addr_data_t addr;
      // get addr
      wait(addr_data_q.size() > 0);
      addr = addr_data_q.pop_front();

      // lookup addr in sw_msgs
      if (sw_msgs.exists(addr)) begin
        bit rst_occurred;
        fork
          begin
            fork
              // get args
              for (int i = 0; i < sw_msgs[addr].nargs; i++) begin
                wait(addr_data_q.size() > 0);
                sw_msgs[addr].arg[i] = addr_data_q.pop_front();
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
        sw_msg_print(sw_msgs[addr]);
      end
    end
  endtask

  // print the msg
  function automatic void sw_msg_print(sw_msg_t sw_msg);
    string msg_header = sw_msg.header;
    string msg = sw_msg.format;

    // if header not available, then construct from other fields: name(file:line)
    if (msg_header == "") begin
      msg_header = sw_msg.name;
      if (sw_msg.file != "") begin
        msg_header = {msg_header, "(", sw_msg.file, ":", $sformatf("%0d", sw_msg.line), ")"};
      end
    end

    // construct formatted string based on args
    case (sw_msg.nargs)
       0: msg = `FORMATTED_MSG_WITH_NARGS(0);
       1: msg = `FORMATTED_MSG_WITH_NARGS(1);
       2: msg = `FORMATTED_MSG_WITH_NARGS(2);
       3: msg = `FORMATTED_MSG_WITH_NARGS(3);
       4: msg = `FORMATTED_MSG_WITH_NARGS(4);
       5: msg = `FORMATTED_MSG_WITH_NARGS(5);
       6: msg = `FORMATTED_MSG_WITH_NARGS(6);
       7: msg = `FORMATTED_MSG_WITH_NARGS(7);
       8: msg = `FORMATTED_MSG_WITH_NARGS(8);
       9: msg = `FORMATTED_MSG_WITH_NARGS(9);
      10: msg = `FORMATTED_MSG_WITH_NARGS(10);
      11: msg = `FORMATTED_MSG_WITH_NARGS(11);
      12: msg = `FORMATTED_MSG_WITH_NARGS(12);
      13: msg = `FORMATTED_MSG_WITH_NARGS(13);
      14: msg = `FORMATTED_MSG_WITH_NARGS(14);
      15: msg = `FORMATTED_MSG_WITH_NARGS(15);
      16: msg = `FORMATTED_MSG_WITH_NARGS(16);
      17: msg = `FORMATTED_MSG_WITH_NARGS(17);
      18: msg = `FORMATTED_MSG_WITH_NARGS(18);
      19: msg = `FORMATTED_MSG_WITH_NARGS(19);
      20: msg = `FORMATTED_MSG_WITH_NARGS(20);
      21: msg = `FORMATTED_MSG_WITH_NARGS(21);
      22: msg = `FORMATTED_MSG_WITH_NARGS(22);
      23: msg = `FORMATTED_MSG_WITH_NARGS(23);
      24: msg = `FORMATTED_MSG_WITH_NARGS(24);
      25: msg = `FORMATTED_MSG_WITH_NARGS(25);
      26: msg = `FORMATTED_MSG_WITH_NARGS(26);
      27: msg = `FORMATTED_MSG_WITH_NARGS(27);
      28: msg = `FORMATTED_MSG_WITH_NARGS(28);
      29: msg = `FORMATTED_MSG_WITH_NARGS(29);
      30: msg = `FORMATTED_MSG_WITH_NARGS(30);
      31: msg = `FORMATTED_MSG_WITH_NARGS(31);
      32: msg = `FORMATTED_MSG_WITH_NARGS(32);
      default: msg_fatal("UNSUPPORTED", $sformatf("nargs = %0d (only 0:32 allowed)", sw_msg.nargs));
    endcase

    // print the msg
    msg_print(sw_msg.msg_type, sw_msg.verbosity, msg_header, msg);
  endfunction

  // methods
  // msg_print api that switches between system call and UVM call
  function automatic void msg_print(string msg_type = "i",
                                    string verbosity = "n",
                                    string msg_header = "",
                                    string msg);
`ifdef UVM
    import uvm_pkg::*;
    `include "uvm_macros.svh"

    uvm_verbosity level;
    case (verbosity)
      "n", "none":          level = UVM_NONE;
      "l", "lo", "low":     level = UVM_LOW;
      "m", "med", "medium": level = UVM_MEDIUM;
      "h", "hi", "high":    level = UVM_HIGH;
      "f", "full":          level = UVM_FULL;
      "d", "dbg", "debug":  level = UVM_DEBUG;
      default:              level = UVM_NONE;
    endcase

    // additional cleanup: if msg_header is already enclosed in [],
    // then remove it, since uvm macros also add them
    if (msg_header.len() >= 2) begin
      if (msg_header[0] == "[" && msg_header[msg_header.len() - 1] == "]") begin
        msg_header = msg_header.substr(1, msg_header.len() - 2);
      end
    end

    case (msg_type.tolower())
      "i", "info":            `uvm_info(msg_header, msg, level)
      "w", "warn", "warning": `uvm_error(msg_header, msg)
      "e", "err", "error":    `uvm_error(msg_header, msg)
      "f", "fatal":           `uvm_fatal(msg_header, msg)
      default:                `uvm_info(msg_header, msg, level)
    endcase
`else
    case (msg_type.tolower())
      "i", "info":            $info("%0t: %0s %0s", $time, msg_header, msg);
      "w", "warn", "warning": $warning("%0t: %0s %0s", $time, msg_header, msg);
      "e", "err", "error":    $error("%0t: %0s %0s", $time, msg_header, msg);
      "f", "fatal":           $fatal("%0t: %0s %0s", $time, msg_header, msg);
      default:                $info("%0t: %0s %0s", $time, msg_header, msg);
    endcase
`endif
  endfunction

  // print info msg
  function automatic void msg_info(string verbosity = "l", string msg_header = "", string msg);
    msg_print(.verbosity(verbosity), .msg_header(msg_header), .msg(msg));
  endfunction

  // print warning msg
  function automatic void msg_warning(string msg_header = "", string msg);
    msg_print(.msg_type("w"), .msg_header(msg_header), .msg(msg));
  endfunction

  // print error msg
  function automatic void msg_error(string msg_header = "", string msg);
    msg_print(.msg_type("e"), .msg_header(msg_header), .msg(msg));
  endfunction

  // print fatal msg
  function automatic void msg_fatal(string msg_header = "", string msg);
    msg_print(.msg_type("f"), .msg_header(msg_header), .msg(msg));
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
`undef FORMATTED_MSG_WITH_NARGS
