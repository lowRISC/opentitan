// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for ${dut.name}.
// Intended to be used with a formal tool.

% if len(dut.pkgs) > 0:
module ${dut.name}_fpv
% for pkg in dut.pkgs:
  import ${pkg};
% endfor
% if dut.params:
#(
% else:
(
% endif
% else:
% if dut.params:
module ${dut.name}_fpv #(
% else:
module ${dut.name}_fpv (
% endif
% endif
% if dut.params:
% for k, param in enumerate(dut.params):
<% comma = "" if (k == len(dut.params)-1) else "," %>  ${param.style} ${param.datatype} ${param.name} =${param.value}${comma}
% endfor
) (
% endif
% for k, port in enumerate(dut.ports):
<% comma = "" if (k == len(dut.ports)-1) else "," %>  ${port.direction} ${port.datatype} ${port.name}${comma}
% endfor
);

<% params = dut.get_param_style("parameter") %>
% if params:
  ${dut.name} #(
% for k, param in enumerate(params):
  <% comma = "" if (k == len(params)-1) else "," %>  .${param.name}(${param.name})${comma}
% endfor
  ) dut (
% else:
  ${dut.name} dut (
%endif
  % for k, port in enumerate(dut.ports):
<% comma = "" if (k == len(dut.ports)-1) else "," %>    .${port.name}${comma}
  % endfor
  );


endmodule : ${dut.name}_fpv
