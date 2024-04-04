// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


//wrapper module to avoid having to know/write out the path from tb to bind


module fi_control_fsm_wrapper
  import uvm_pkg::*;
  import aes_env_pkg::*;
  import aes_pkg::*;
  #( parameter string IfName = "vif"
  ) (
    input logic      clk_i,
    input logic      rst_ni,
    input aes_ctrl_e aes_ctrl_cs
  );

  // declare interface
  fi_control_if  fi_if (.*);
  initial begin
    uvm_config_db#(virtual fi_control_if)::set(null, "*",
      pick_if_name(IfName, $sformatf("%m")), fi_if);
  end
endmodule
