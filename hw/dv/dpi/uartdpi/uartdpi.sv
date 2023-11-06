// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module uartdpi #(
  parameter integer BAUD = 'x,
  parameter integer FREQ = 'x,
  parameter string NAME = "uart0"
)(
  input  logic clk_i,
  input  logic rst_ni,
  input  bit   active,

  output logic tx_o,
  input  logic rx_i
);
  // Path to a log file. Used if none is specified through the `UARTDPI_LOG_<name>` plusarg.
  localparam string DEFAULT_LOG_FILE = {NAME, ".log"};

  // Min cycles is 2 for fast test mode
  localparam int CYCLES_PER_SYMBOL = FREQ / BAUD;

  import "DPI-C" function
    chandle uartdpi_create(input string name, input string log_file_path);

  import "DPI-C" function
    void uartdpi_close(input chandle ctx);

  import "DPI-C" function
    byte uartdpi_read(input chandle ctx);

  import "DPI-C" function
    int uartdpi_can_read(input chandle ctx);

  import "DPI-C" function
    void uartdpi_write(input chandle ctx, int data);

  chandle ctx;
  string log_file_path = DEFAULT_LOG_FILE;

  function automatic void initialize();
    $value$plusargs({"UARTDPI_LOG_", NAME, "=%s"}, log_file_path);
    ctx = uartdpi_create(NAME, log_file_path);
  endfunction

  initial begin
    if (active) initialize();
  end

  always @(posedge active) begin
    if (ctx == null) initialize();
  end

  final begin
    uartdpi_close(ctx);
    ctx = null;
  end

  // TX
  reg txactive;
  int  txcount;
  int  txcyccount;
  reg [9:0] txsymbol;
  bit seen_reset;

  logic eff_clk;
  assign eff_clk = clk_i & active;

  always_ff @(negedge eff_clk or negedge rst_ni) begin
    if (!rst_ni) begin
      tx_o <= 1;
      txactive <= 0;
    end else begin
      if (!txactive) begin
        tx_o <= 1;
        if (uartdpi_can_read(ctx)) begin
          automatic int c = uartdpi_read(ctx);
          txsymbol <= {1'b1, c[7:0], 1'b0};
          txactive <= 1;
          txcount <= 0;
          txcyccount <= 0;
        end
      end else begin
        txcyccount <= txcyccount + 1;
        tx_o <= txsymbol[txcount];
        if (txcyccount == CYCLES_PER_SYMBOL - 1) begin
          txcyccount <= 0;
          if (txcount == 9)
            txactive <= 0;
          else
            txcount <= txcount + 1;
        end
      end
    end
  end

  // RX
  reg rxactive;
  int rxcount;
  int rxcyccount;
  reg [7:0] rxsymbol;

  always_ff @(negedge eff_clk or negedge rst_ni) begin
    rxcyccount <= rxcyccount + 1;

    if (!rst_ni) begin
      rxactive <= 0;
      seen_reset <= 1;
    end else begin
      if (!rxactive) begin
        if (!rx_i && seen_reset) begin
          rxactive <= 1;
          rxcount <= 0;
          rxcyccount <= 0;
        end
      end else begin
        if (rxcount == 0) begin
          if (rxcyccount == CYCLES_PER_SYMBOL/2 - 1) begin
            if (rx_i) begin
              rxactive <= 0;
            end else begin
              rxcount <= rxcount + 1;
              rxcyccount <= 0;
            end
          end
        end else if (rxcount <= 8) begin
          if (rxcyccount == CYCLES_PER_SYMBOL - 1) begin
            rxsymbol[rxcount-1] <= rx_i;
            rxcount <= rxcount + 1;
            rxcyccount <= 0;
          end
        end else begin
          if (rxcyccount == CYCLES_PER_SYMBOL - 1) begin
            rxactive <= 0;
            if (rx_i) begin
              uartdpi_write(ctx, rxsymbol);
            end
          end
        end
      end
    end
  end

endmodule
