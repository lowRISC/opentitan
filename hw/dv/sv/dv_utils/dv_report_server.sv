// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Standardize look & feel of report phase and uvm logging messages.
class dv_report_server extends uvm_default_report_server;

  bit show_file_line = 1'b1;
  // if enabled, show the relative path of the file. By default only show file name
  bit show_file_path = 1'b0;
  bit use_default_uvm_report_message_format = 1'b0;

  function new (string name = "");
    super.new(name);
    // provide ability to override these knobs over cli
    void'($value$plusargs("show_file_line=%0b", show_file_line));
    void'($value$plusargs("show_file_path=%0b", show_file_path));
    void'($value$plusargs("use_default_uvm_report_message_format=%0b",
                           use_default_uvm_report_message_format));
  endfunction

  function void report_summarize(UVM_FILE file = 0);
    int num_uvm_warning;
    int num_uvm_error;
    int num_uvm_fatal;

    num_uvm_warning = get_severity_count(UVM_WARNING);
    num_uvm_error   = get_severity_count(UVM_ERROR);
    num_uvm_fatal   = get_severity_count(UVM_FATAL);

    // Print default summary report
    super.report_summarize(file);

    // Print final test pass-fail - external tool can use this signature for test status
    // Treat UVM_WARNINGs as a sign of test failure since it could silently result in false pass
    dv_test_status_pkg::dv_test_status((num_uvm_warning + num_uvm_error + num_uvm_fatal) == 0);
  endfunction

  // Override default messaging format to standard "pretty" format for all testbenches
  virtual function string compose_report_message(uvm_report_message report_message,
                                                 string report_object_name = "");

    if (use_default_uvm_report_message_format) begin
      return (super.compose_report_message(report_message, report_object_name));
    end else begin
      uvm_severity  severity  = report_message.get_severity();
      string        filename  = report_message.get_filename();
      int           line      = report_message.get_line();
      string        obj_name  = report_message.get_report_object().get_full_name();
      string        id        = report_message.get_id();
      string        message   = report_message.get_message();
      string        file_line;

      if (show_file_line && filename != "") begin
        if (!show_file_path) filename = str_utils_pkg::str_path_basename(filename);
        file_line = $sformatf("(%0s:%0d) ", filename, line);
      end
      obj_name = {obj_name, ((obj_name != "") ? " " : "")};
      compose_report_message = $sformatf({"%0s @ %t: ", file_line, obj_name, "[%0s] %0s"},
                                          severity.name(), $realtime, id, message);
      return compose_report_message;
    end
  endfunction

endclass
