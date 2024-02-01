// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface cip_lc_tx_cov_if(input [3:0] val, input rst_ni);
  import uvm_pkg::*;
  import dv_base_reg_pkg::*;

  typedef mubi_cov #(.Width(4),
                     .ValueTrue(lc_ctrl_pkg::On),
                     .ValueFalse(lc_ctrl_pkg::Off)) lc_tx_cov;
  lc_tx_cov cov;
  initial begin
    cov = lc_tx_cov::type_id::create($sformatf("%m"));
    forever begin
      @(val or rst_ni);
      if (rst_ni === 1) cov.sample(val);
    end
  end
endinterface
