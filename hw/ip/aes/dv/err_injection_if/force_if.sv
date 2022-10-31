// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Interface used for fault inject verification
interface force_if
  import uvm_pkg::*;
  #(parameter string Signal = "",
    parameter int SignalWidth = 1 )
  (
   input logic clk_i,
   input logic rst_ni
   );

  string       par_hier = dv_utils_pkg::get_parent_hier($sformatf("%m"),2);
  string       path     = $sformatf("%s.%s", par_hier, Signal);

  function static void force_state(bit [SignalWidth-1:0] state);
    $assertoff(0, "tb.dut");
    $asserton(0, "tb.dut.u_aes_core.AesSecCmDataRegLocalEscDataOut");
    $asserton(0, "tb.dut.u_aes_core.AesSecCmDataRegLocalEscIv");
    if (!uvm_hdl_check_path(path)) begin
      `uvm_fatal("Force_if", $sformatf("PATH NOT EXISTING %m"))
    end
    if (!uvm_hdl_force(path,state)) begin
      `uvm_error("Force_if", $sformatf("Was not able to force %s", state))
    end
  endfunction

  function static void release_state();
    uvm_hdl_release(path);
    $asserton(0,"tb.dut");
  endfunction
endinterface
