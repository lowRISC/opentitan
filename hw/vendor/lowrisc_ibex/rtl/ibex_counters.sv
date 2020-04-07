module ibex_counters #(
  parameter int MaxNumCounters = 29,
  parameter int NumCounters = 0,
  parameter int CounterWidth = 32
) (
  input                             clk_i,
  input                             rst_ni,

  input  logic [MaxNumCounters-1:0] counter_inc_i,
  input  logic [MaxNumCounters-1:0] counterh_we_i,
  input  logic [MaxNumCounters-1:0] counter_we_i,
  input  logic [31:0]               counter_val_i,
  output logic [63:0]               counter_val_o [MaxNumCounters]
);
  logic [63:0] counter [MaxNumCounters];

  assign counter_val_o = counter;

  for (genvar i = 0; i < MaxNumCounters; i++) begin : g_counter
    // Only elaborate flops that are needed from the given CounterWidth and NumCounters.
    if (i < NumCounters) begin : g_counter_exists

      logic [63:0] counter_upd;
      logic [63:0] counter_load;
      logic we;
      logic [CounterWidth-1:0] counter_d;

      // Update
      always_comb begin

        // Write
        we = counter_we_i[i] | counterh_we_i[i];
        counter_load[63:32] = counter[i][63:32];
        counter_load[31:0]  = counter_val_i;
        if (counterh_we_i[i]) begin
          counter_load[63:32] = counter_val_i;
          counter_load[31:0]  = counter[i][31:0];
        end

        // Increment
        counter_upd = counter[i] + 64'h1;

        // Next value logic
        if (we) begin
          counter_d = counter_load[CounterWidth-1:0];
        end else if (counter_inc_i[i])begin
          counter_d = counter_upd[CounterWidth-1:0];
        end else begin
          counter_d = counter[i][CounterWidth-1:0];
        end
      end

`ifdef FPGA_XILINX
      // Set DSP pragma for supported xilinx FPGAs
      localparam dsp_pragma = CounterWidth < 49  ? "yes" : "no";
      (* use_dsp = dsp_pragma *) logic [CounterWidth-1:0] counter_q;

      // DSP output register requires synchronous reset.
      `define COUNTER_FLOP_RST posedge clk_i
`else
      logic [CounterWidth-1:0] counter_q;

      `define COUNTER_FLOP_RST posedge clk_i or negedge rst_ni
`endif

      // Counter flop
      always @(`COUNTER_FLOP_RST) begin
        if (!rst_ni) begin
          counter_q <= '0;
        end else begin
          counter_q <= counter_d;
        end
      end

      if (CounterWidth < 64) begin : g_counter_narrow
        assign counter[i][CounterWidth-1:0] = counter_q;
        assign counter[i][63:CounterWidth]  = '0;
      end else begin : g_counter_full
        assign counter[i] = counter_q;
      end
    end else begin : g_no_counter
      assign counter[i] = '0;
    end
  end

endmodule

// Keep helper defines file-local.
`undef COUNTER_FLOP_RST
