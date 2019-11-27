// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//

module ${dut.name}_bind_fpv;

  bind ${dut.name} ${dut.name}_assert_fpv ${dut.name}_assert_fpv (
    .*
  );
% if dut.is_cip:

  bind ${dut.name} tlul_assert #(
    .EndpointType("Device")
  ) tlul_assert_device (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );

  bind ${dut.name} ${dut.name}_csr_assert_fpv (
  	.*
  );
% endif

endmodule : ${dut.name}_bind_fpv
