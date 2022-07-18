// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0


//wrapper module to avoid having to know/write out the path from tb to bind


module fi_cipher_fsm_wrapper
  import uvm_pkg::*;
  import aes_env_pkg::*;
  #( parameter string IfName = "vif"
  )
  ( input clk,
    input rst_ni
    );

  // declare interface
  fi_cipher_if  fi_if (.clk_i  (clk), .rst_ni (rst_ni));
  initial begin
    uvm_config_db#(virtual fi_cipher_if)::set(null, "*",
      pick_if_name(IfName, $sformatf("%m")), fi_if);
  end

endmodule
