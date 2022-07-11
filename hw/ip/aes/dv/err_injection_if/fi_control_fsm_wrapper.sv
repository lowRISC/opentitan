// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


//wrapper module to avoid having to know/write out the path from tb to bind


module fi_control_fsm_wrapper
  import uvm_pkg::*;
  #( parameter string IfName = "vif"
  )
  ( input clk,
    input rst_ni
    );

  // declare interface
  fi_control_if  fi_if (.clk_i  (clk), .rst_ni (rst_ni));
  initial begin
    uvm_config_db#(virtual fi_control_if)::set(null, "*", pick_if_name(), fi_if);
  end

  // Pick a name for this interface, under which it will be registered with the UVM DB. This is
  // based on IfName but also appends the index under the deepest generate block if necessary. For
  // example, if IfName is "foo" and we're bound into a module that is instantiated with indices 0,
  // 1 and 2 and then this should return "foo_0", "foo_1" and "foo_2", respectively.
  function automatic string pick_if_name();
    // find the interface index
    string str = $sformatf("%m");
    string suffix = "";
    int    closing_bracket = -1;
    int    opening_bracket  = -1;

    // Walk from the back, searching for something of the form "[123]".
    for (int i = str.len() - 1; i >= 0; i--) begin
      if (str[i] == "]") begin
        closing_bracket = i;
        break;
      end
    end
    for (int i = str.len() - 1; i >= 0; i--) begin
      if (str[i] == "[") begin
        opening_bracket = i;
        break;
      end
    end
    if (str[opening_bracket] == "[") begin
      // we do not expect to see "[]"
      if (!(closing_bracket > opening_bracket + 1)) begin
        // we cannot use macro as module is not a part of hierarchy
        // will fail the get_full_name() lookup
        `uvm_fatal($sformatf("%m"), $sformatf("Found unexpected empty bracket"))
      end
      // Put the stuff in the brackets in suffix
      suffix = str.substr(opening_bracket + 1, closing_bracket - 1);
    end

    return $sformatf("%s_%s", IfName, suffix);
  endfunction
endmodule
