// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%
import re
%>\
module top_${top["name"]} #(
  parameter bit IbexPipeLine = 0
) (
);
% for m in top["module"]:
  // ${m["name"]}
%     for p_in in m["available_input_list"] + m["available_inout_list"]:
          ## assume it passed validate and have available input list always
%         if "width" in p_in and int(p_in["width"]) != 1:
  logic [${int(p_in["width"])-1}:0] ${m["name"]}_${p_in["name"]}_p2d;
%         else:
  logic ${m["name"]}_${p_in["name"]}_p2d;
%         endif
%     endfor
%     for p_out in m["available_output_list"] + m["available_inout_list"]:
          ## assume it passed validate and have available output list always
%         if "width" in p_out and int(p_out["width"]) != 1:
  logic [${int(p_out["width"])-1}:0] ${m["name"]}_${p_out["name"]}_d2p;
  logic [${int(p_out["width"])-1}:0] ${m["name"]}_${p_out["name"]}_en_d2p;
%         else:
  logic ${m["name"]}_${p_out["name"]}_d2p;
  logic ${m["name"]}_${p_out["name"]}_en_d2p;
%         endif
%     endfor
% endfor

  input               scanmode_i  // 1 for Scan

  // Top instantiation
  top_${top["name"]}_core #(
    .IbexPipeLine (IbexPipeLine)
  ) u_core (
    .clk_i          (           ),
    .rst_ni         (           ),

    // JTAG
    .jtag_tck_i     (           ),
    .jtag_tms_i     (           ),
    .jtag_trst_ni   (           ),
    .jtag_td_i      (           ),
    .jtag_td_o      (           ),

    // Module CIO
% for m in top["module"]:
    // ${m["name"]}
    % for p_in in m["available_input_list"] + m["available_inout_list"]:
          ## assume it passed validate and have available input list always
    .cio_${m["name"]}_${p_in["name"]}_p2d_i (${m["name"]}_${p_in["name"]}_p2d),
    % endfor
    % for p_out in m["available_output_list"] + m["available_inout_list"]:
          ## assume it passed validate and have available output list always
    .cio_${m["name"]}_${p_out["name"]}_d2p_o    (${m["name"]}_${p_out["name"]}_d2p),
    .cio_${m["name"]}_${p_out["name"]}_en_d2p_o (${m["name"]}_${p_out["name"]}_en_d2p),
    % endfor
% endfor

    .scanmode_i()
  );

endmodule

