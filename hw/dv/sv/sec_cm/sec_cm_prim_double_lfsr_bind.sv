// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module sec_cm_prim_double_lfsr_bind ();
  bind prim_double_lfsr prim_double_lfsr_if #(.Width(LfsrDw)) u_prim_double_lfsr_if (.*);
endmodule
