// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module sec_cm_prim_count_bind ();
  bind prim_count prim_count_if #(.Width(Width)) u_prim_count_if (.*);
endmodule
