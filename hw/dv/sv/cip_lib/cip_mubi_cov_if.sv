// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

interface cip_mubi_cov_if #(parameter int Width = 4) (input [Width-1:0] mubi, input rst_ni);
  import uvm_pkg::*;
  import dv_base_reg_pkg::*;

  dv_base_mubi_cov mubi_cov;
  initial begin
    mubi_cov = dv_base_mubi_cov::type_id::create($sformatf("%m"));
    mubi_cov.create_cov(Width);
    forever begin
      @(mubi or rst_ni);
      if (rst_ni === 1) mubi_cov.sample(mubi);
    end
  end
endinterface
