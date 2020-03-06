// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class core_ibex_report_server extends uvm_default_report_server;

  function new(string name = "");
    super.new(name);
  endfunction

  function void report_summarize(UVM_FILE file = 0);
    int error_count;
    error_count = get_severity_count(UVM_WARNING);
    error_count = get_severity_count(UVM_ERROR) + error_count;
    error_count = get_severity_count(UVM_FATAL) + error_count;

    if (error_count == 0) begin
      $display("\n--- RISC-V UVM TEST PASSED ---\n");
    end else begin
      $display("\n--- RISC-V UVM TEST FAILED ---\n");
    end
    super.report_summarize(file);
  endfunction

endclass
