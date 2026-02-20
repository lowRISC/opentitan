// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module ${module_instance_name}_fpv_bind;

  bind ${module_instance_name} u_csr_assert_fpv u_csr_assert_fpv (
    .clk_i,
    .rst_ni,
    .h2d  (tl_i),
    .d2h  (tl_o)
  );

endmodule : ${module_instance_name}_bind_fpv
