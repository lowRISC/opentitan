// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Fix external implemented registers path location for CSR/RAL
function automatic void update_external_reg_hdl_path();
  // Empty for now!

  // uvm_hdl_path_concat paths[$];
  // string reg_name = get_name();
  // bit reg_updated = 0;
  //
  // if ( reg_name == "alert_test" ) begin
  //   clear_hdl_path( "BkdrRegPathRtl" );
  //   // this register does not exist...
  //   reg_updated = 1;
  // end
  //
  // if ( reg_name == "xxxx" ) begin
  //   clear_hdl_path( "BkdrRegPathRtl" );
  //   // update hdl path of all fields in this register
  //   add_hdl_path_slice("u_reg_ext.xxxx", 0, 32, 0, "BkdrRegPathRtl");
  //   reg_updated = 1;
  // end
  //
  // . . . more registers.
  //
  // if ( reg_updated == 0 ) begin
  //   `uvm_error(`gtn, $sformatf( "Error when updated %s backdoor paths\n", reg_name ));
  // end

endfunction
