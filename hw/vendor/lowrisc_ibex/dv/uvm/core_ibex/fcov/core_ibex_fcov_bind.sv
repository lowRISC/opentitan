// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module core_ibex_fcov_bind;
  bind ibex_core core_ibex_fcov_if u_fcov_bind (
    .*
  );

  bind ibex_core core_ibex_pmp_fcov_if
  #(.PMPGranularity(PMPGranularity),
    .PMPNumRegions(PMPNumRegions))
  u_pmp_fcov_bind (
    .*
  );
endmodule
