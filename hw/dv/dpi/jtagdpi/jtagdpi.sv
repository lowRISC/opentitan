// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module jtagdpi #(
  parameter string Name = "jtag0", // name of the JTAG interface (display only)
  parameter int ListenPort = 44853 // TCP port to listen on
)(
  input  clk_i,
  input  rst_ni,

  output jtag_tck,
  output jtag_tms,
  output jtag_tdi,
  input  jtag_tdo,
  output jtag_trst_n,
  output jtag_srst_n
);

  import "DPI-C"
  function chandle jtagdpi_create(input string name, input int listen_port);

  import "DPI-C"
  function void jtagdpi_tick(input chandle ctx, output bit tck, output bit tms,
                             output bit tdi, output bit trst_n,
                             output bit srst_n, input bit tdo);

  import "DPI-C"
  function void jtagdpi_close(input chandle ctx);

  chandle ctx;

  initial begin
    ctx = jtagdpi_create(Name, ListenPort);
  end

  final begin
    jtagdpi_close(ctx);
    ctx = 0;
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    jtagdpi_tick(ctx, jtag_tck, jtag_tms, jtag_tdi, jtag_trst_n, jtag_srst_n,
                 jtag_tdo);
  end

endmodule
