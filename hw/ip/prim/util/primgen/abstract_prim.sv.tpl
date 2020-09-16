// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

% if num_techlibs > 1:
`ifndef PRIM_DEFAULT_IMPL
  `define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif
% endif

module prim_${prim_name}
${module_header_imports}
#(
${module_header_params}
) (
  ${module_header_ports}
);
% if num_techlibs > 1:
  parameter prim_pkg::impl_e Impl = `PRIM_DEFAULT_IMPL;
% endif

${instances}

endmodule
