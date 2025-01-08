// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Binds ${(module_instance_name).upper()} functional coverage interafaces to the top level ${(module_instance_name).upper()} module.

module ${module_instance_name}_cov_bind;
  import ${module_instance_name}_pkg::*;

  bind ${module_instance_name} cip_mubi_cov_wrapper#(.NumMubis(NLpg)) u_lpg_cg_en_cov_if (
    .rst_ni (rst_ni),
    .mubis  (lpg_cg_en_i)
  );

  bind ${module_instance_name} cip_mubi_cov_wrapper#(.NumMubis(NLpg)) u_lpg_rst_en_cov_if (
    .rst_ni (rst_ni),
    .mubis  (lpg_rst_en_i)
  );
endmodule : ${module_instance_name}_cov_bind
