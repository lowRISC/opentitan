// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This file is auto-generated.

% if num_techlibs > 1:
`ifndef PRIM_DEFAULT_IMPL
  `define PRIM_DEFAULT_IMPL prim_pkg::ImplGeneric
`endif
% endif

// This is to prevent AscentLint warnings in the generated
// abstract prim wrapper. These warnings occur due to the .*
// use. TODO: we may want to move these inline waivers
// into a separate, generated waiver file for consistency.
//ri lint_check_off OUTPUT_NOT_DRIVEN INPUT_NOT_READ
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
//ri lint_check_on OUTPUT_NOT_DRIVEN INPUT_NOT_READ
