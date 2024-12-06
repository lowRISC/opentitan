// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module jtagdpi #(
  parameter string Name = "jtag0", // name of the JTAG interface (display only)
  parameter int ListenPort = 44853 // TCP port to listen on
)(
  input  logic clk_i,
  input  logic rst_ni,
  input  bit   active,

  output logic jtag_tck,
  output logic jtag_tms,
  output logic jtag_tdi,
  input  logic jtag_tdo,
  output logic jtag_trst_n,
  output logic jtag_srst_n
);

  import "DPI-C"
  function chandle jtagdpi_create(input string name, input int listen_port,
                                  input int assert_srst);

  import "DPI-C"
  function void jtagdpi_tick(input chandle ctx, output bit tck, output bit tms,
                             output bit tdi, output bit trst_n,
                             output bit srst_n, input bit tdo);

  import "DPI-C"
  function void jtagdpi_close(input chandle ctx);

  chandle ctx;

  function automatic void initialize();
    int port, assert_srst;

    assert (ctx == null);

    // The listening socket port can be customized at runtime
    port = ListenPort;
    void'($value$plusargs("jtagdpi_port=%0d", port));

    // The functional reset can optionally start out asserted
    assert_srst = 0;
    void'($value$plusargs("jtagdpi_assert_srst=%0d", assert_srst));

    ctx = jtagdpi_create(Name, port, assert_srst);
  endfunction

  initial begin
    if (active) initialize();
  end

  always @(posedge active) begin
    if (ctx == null) initialize();
  end

  final begin
    jtagdpi_close(ctx);
    ctx = null;
  end

  always_ff @(posedge clk_i, negedge rst_ni) begin
    if (active) jtagdpi_tick(ctx, jtag_tck, jtag_tms, jtag_tdi, jtag_trst_n,
                             jtag_srst_n, jtag_tdo);
  end

endmodule
