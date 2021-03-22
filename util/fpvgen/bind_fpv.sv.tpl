// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module ${dut.name}_bind_fpv;

<% params = dut.get_param_style("parameter") %>
% if params:
  bind ${dut.name} ${dut.name}_assert_fpv #(
% for k, param in enumerate(params):
  <% comma = "" if (k == len(params)-1) else "," %>  .${param.name}(${param.name})${comma}
% endfor
  ) i_${dut.name}_assert_fpv (
% else:
  bind ${dut.name} ${dut.name}_assert_fpv i_${dut.name}_assert_fpv (
%endif
  % for k, port in enumerate(dut.ports):
<% comma = "" if (k == len(dut.ports)-1) else "," %>    .${port.name}${comma}
  % endfor
  );

% if dut.is_cip:

  bind ${dut.name} tlul_assert #(
    .EndpointType("Device")
  ) i_tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o),
    .*
  );

  bind ${dut.name} ${dut.name}_csr_assert_fpv i_${dut.name}_csr_assert_fpv (
    .clk_i,
    .rst_ni,
    .h2d    (tl_i),
    .d2h    (tl_o)
  );
% endif

endmodule : ${dut.name}_bind_fpv
