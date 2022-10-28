// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module ibex_simple_system_cosim_checker_bind;
  bind ibex_simple_system ibex_simple_system_cosim_checker#(
      .SecureIbex,
      .ICache,
      .PMPEnable,
      .PMPGranularity,
      .PMPNumRegions,
      .MHPMCounterNum
    ) u_ibex_simple_system_cosim_checker_bind (
      .clk_i            (IO_CLK),
      .rst_ni           (IO_RST_N),

      .host_dmem_req    (host_req[CoreD]),
      .host_dmem_gnt    (host_gnt[CoreD]),
      .host_dmem_we     (host_we[CoreD]),
      .host_dmem_addr   (host_addr[CoreD]),
      .host_dmem_be     (host_be[CoreD]),
      .host_dmem_wdata  (host_wdata[CoreD]),

      .host_dmem_rvalid (host_rvalid[CoreD]),
      .host_dmem_rdata  (host_rdata[CoreD]),
      .host_dmem_err    (host_err[CoreD])
    );
endmodule
