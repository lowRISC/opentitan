// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: UART core module
//

module perfcounters_t_event (
  input                  clk_i,
  input                  rst_ni,

  input  perfcounters_t_reg_pkg::perfcounters_t_reg2hw_t reg2hw,
  output perfcounters_t_reg_pkg::perfcounters_t_hw2reg_t hw2reg

);
  import perfcounters_t_reg_pkg::*;


logic [7: 0] events;
logic [11:0] events_counters_mux;
logic [3:0] event_counters_rst;
logic [3:0] event_clk_counters_rst;

logic [31:0] event_counter3_reg; 
logic [31:0] event_counter2_reg; 
logic [31:0] event_counter1_reg; 
logic [31:0] event_counter0_reg; 

logic [31:0] event_clk_counter3_reg; 
logic [31:0] event_clk_counter2_reg; 
logic [31:0] event_clk_counter1_reg; 
logic [31:0] event_clk_counter0_reg; 

logic	     event_counter0_en;
logic	     event_counter1_en;
logic	     event_counter2_en;
logic	     event_counter3_en;
logic	     event_clk_counter0_en;
logic	     event_clk_counter1_en;
logic	     event_clk_counter2_en;
logic	     event_clk_counter3_en;




  assign events[0]		= reg2hw.event_reg.event_0.q;
  assign events[1]		= reg2hw.event_reg.event_1.q;
  assign events[2]		= reg2hw.event_reg.event_2.q;
  assign events[3]		= reg2hw.event_reg.event_3.q;
  assign events[4]		= reg2hw.event_reg.event_4.q;
  assign events[5]		= reg2hw.event_reg.event_5.q;
  assign events[6]		= reg2hw.event_reg.event_6.q;
  assign events[7]		= reg2hw.event_reg.event_7.q;

  assign event_counters_rst[0]	        = reg2hw.event_counters_rst_reg.event_counter0_rst.q;
  assign event_clk_counters_rst[0]	= reg2hw.event_counters_rst_reg.event_clk_counter0_rst.q;

  assign event_counters_rst[1]	        = reg2hw.event_counters_rst_reg.event_counter1_rst.q;
  assign event_clk_counters_rst[1]	= reg2hw.event_counters_rst_reg.event_clk_counter1_rst.q;

  assign event_counters_rst[2]	        = reg2hw.event_counters_rst_reg.event_counter2_rst.q;
  assign event_clk_counters_rst[2]	= reg2hw.event_counters_rst_reg.event_clk_counter2_rst.q;


  assign event_counters_rst[3]	        = reg2hw.event_counters_rst_reg.event_counter3_rst.q;
  assign event_clk_counters_rst[3]	= reg2hw.event_counters_rst_reg.event_clk_counter3_rst.q;


  assign events_counters_mux	= reg2hw.events_counters_mux_reg;

// READBACK COUNTERS VALUE
  assign hw2reg.event_counter3_reg.d = event_counter3_reg;
  assign hw2reg.event_counter2_reg.d = event_counter2_reg;
  assign hw2reg.event_counter1_reg.d = event_counter1_reg;
  assign hw2reg.event_counter0_reg.d = event_counter0_reg;

  assign hw2reg.event_counter3_reg.de = 1'b1;
  assign hw2reg.event_counter2_reg.de = 1'b1;
  assign hw2reg.event_counter1_reg.de = 1'b1;
  assign hw2reg.event_counter0_reg.de = 1'b1;


  assign hw2reg.event_clk_counter3_reg.d = event_clk_counter3_reg;
  assign hw2reg.event_clk_counter2_reg.d = event_clk_counter2_reg;
  assign hw2reg.event_clk_counter1_reg.d = event_clk_counter1_reg;
  assign hw2reg.event_clk_counter0_reg.d = event_clk_counter0_reg;

  assign hw2reg.event_clk_counter3_reg.de = 1'b1;
  assign hw2reg.event_clk_counter2_reg.de = 1'b1;
  assign hw2reg.event_clk_counter1_reg.de = 1'b1;
  assign hw2reg.event_clk_counter0_reg.de = 1'b1;

  // Derive 1 clk pulse on events
  assign hw2reg.event_reg.event_0.d = 1'b0;
  assign hw2reg.event_reg.event_1.d = 1'b0;
  assign hw2reg.event_reg.event_2.d = 1'b0;
  assign hw2reg.event_reg.event_3.d = 1'b0;
  assign hw2reg.event_reg.event_4.d = 1'b0;
  assign hw2reg.event_reg.event_5.d = 1'b0;
  assign hw2reg.event_reg.event_6.d = 1'b0;
  assign hw2reg.event_reg.event_7.d = 1'b0;

  assign hw2reg.event_reg.event_0.de = reg2hw.event_reg.event_0.q;
  assign hw2reg.event_reg.event_1.de = reg2hw.event_reg.event_1.q;
  assign hw2reg.event_reg.event_2.de = reg2hw.event_reg.event_2.q;
  assign hw2reg.event_reg.event_3.de = reg2hw.event_reg.event_3.q;
  assign hw2reg.event_reg.event_4.de = reg2hw.event_reg.event_4.q;
  assign hw2reg.event_reg.event_5.de = reg2hw.event_reg.event_5.q;
  assign hw2reg.event_reg.event_6.de = reg2hw.event_reg.event_6.q;
  assign hw2reg.event_reg.event_7.de = reg2hw.event_reg.event_7.q;


  // Derive 1 clk pulse on RST
  assign hw2reg.event_counters_rst_reg.event_counter0_rst.d = 1'b0;
  assign hw2reg.event_counters_rst_reg.event_counter1_rst.d = 1'b0;
  assign hw2reg.event_counters_rst_reg.event_counter2_rst.d = 1'b0;
  assign hw2reg.event_counters_rst_reg.event_counter3_rst.d = 1'b0;
  assign hw2reg.event_counters_rst_reg.event_clk_counter0_rst.d = 1'b0;
  assign hw2reg.event_counters_rst_reg.event_clk_counter1_rst.d = 1'b0;
  assign hw2reg.event_counters_rst_reg.event_clk_counter2_rst.d = 1'b0;
  assign hw2reg.event_counters_rst_reg.event_clk_counter3_rst.d = 1'b0;

  assign hw2reg.event_counters_rst_reg.event_counter0_rst.de = reg2hw.event_counters_rst_reg.event_counter0_rst.q;
  assign hw2reg.event_counters_rst_reg.event_counter1_rst.de = reg2hw.event_counters_rst_reg.event_counter1_rst.q;
  assign hw2reg.event_counters_rst_reg.event_counter2_rst.de = reg2hw.event_counters_rst_reg.event_counter2_rst.q;
  assign hw2reg.event_counters_rst_reg.event_counter3_rst.de = reg2hw.event_counters_rst_reg.event_counter3_rst.q;

  assign hw2reg.event_counters_rst_reg.event_clk_counter0_rst.de = reg2hw.event_counters_rst_reg.event_clk_counter0_rst.q;
  assign hw2reg.event_counters_rst_reg.event_clk_counter1_rst.de = reg2hw.event_counters_rst_reg.event_clk_counter1_rst.q;
  assign hw2reg.event_counters_rst_reg.event_clk_counter2_rst.de = reg2hw.event_counters_rst_reg.event_clk_counter2_rst.q;
  assign hw2reg.event_counters_rst_reg.event_clk_counter3_rst.de = reg2hw.event_counters_rst_reg.event_clk_counter3_rst.q;




  
  always_comb begin
  case ( reg2hw.events_counters_mux_reg.events_counter0_mux.q )
  3'b000: event_counter0_en =  events[0];
  3'b001: event_counter0_en =  events[1];
  3'b010: event_counter0_en =  events[2];
  3'b011: event_counter0_en =  events[3];
  3'b100: event_counter0_en =  events[4];
  3'b101: event_counter0_en =  events[5];
  3'b110: event_counter0_en =  events[6];
  3'b111: event_counter0_en =  events[7];
  endcase

  end
  always_comb begin
  case ( reg2hw.events_counters_mux_reg.events_counter1_mux.q )
  3'b000: event_counter1_en =  events[0];
  3'b001: event_counter1_en =  events[1];
  3'b010: event_counter1_en =  events[2];
  3'b011: event_counter1_en =  events[3];
  3'b100: event_counter1_en =  events[4];
  3'b101: event_counter1_en =  events[5];
  3'b110: event_counter1_en =  events[6];
  3'b111: event_counter1_en =  events[7];
  default:
	  event_counter1_en =  events[0];
  endcase

  end
  always_comb begin
  case ( reg2hw.events_counters_mux_reg.events_counter2_mux.q )
  3'b000: event_counter2_en =  events[0];
  3'b001: event_counter2_en =  events[1];
  3'b010: event_counter2_en =  events[2];
  3'b011: event_counter2_en =  events[3];
  3'b100: event_counter2_en =  events[4];
  3'b101: event_counter2_en =  events[5];
  3'b110: event_counter2_en =  events[6];
  3'b111: event_counter2_en =  events[7];
  default:
	  event_counter2_en =  events[0];
  endcase

  end
  always_comb begin
  case ( reg2hw.events_counters_mux_reg.events_counter3_mux.q )
  3'b000: event_counter3_en =  events[0];
  3'b001: event_counter3_en =  events[1];
  3'b010: event_counter3_en =  events[2];
  3'b011: event_counter3_en =  events[3];
  3'b100: event_counter3_en =  events[4];
  3'b101: event_counter3_en =  events[5];
  3'b110: event_counter3_en =  events[6];
  3'b111: event_counter3_en =  events[7];
  default:
	  event_counter3_en =  events[0];
  endcase

  end

  // EVENT COUNTERS
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
  	 event_counter0_reg <= 32'b0;
    end else if (event_counters_rst[0] ) begin
  	 event_counter0_reg <= 32'b0;
    end else if (event_counter0_en ) begin
	 event_counter0_reg <= event_counter0_reg + 1'b1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
  	 event_counter1_reg <= 32'b0;
    end else if (event_counters_rst[1] ) begin
  	 event_counter1_reg <= 32'b0;
    end else if (event_counter1_en ) begin
	 event_counter1_reg <= event_counter1_reg + 1'b1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
  	 event_counter2_reg <= 32'b0;
    end else if (event_counters_rst[2] ) begin
  	 event_counter2_reg <= 32'b0;
    end else if (event_counter2_en ) begin
	 event_counter2_reg <= event_counter2_reg + 1'b1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
  	 event_counter3_reg <= 32'b0;
    end else if (event_counters_rst[3] ) begin
  	 event_counter3_reg <= 32'b0;
    end else if (event_counter3_en ) begin
	 event_counter3_reg <= event_counter3_reg + 1'b1;
    end
  end

  // EVENT CLK COUNTERS

  assign event_clk_counter0_en = 1'b1;
  assign event_clk_counter1_en = 1'b1;
  assign event_clk_counter2_en = 1'b1;
  assign event_clk_counter3_en = 1'b1;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
  	 event_clk_counter0_reg <= 32'b0;
    end else if (event_clk_counters_rst[0] ) begin
  	 event_clk_counter0_reg <= 32'b0;
    end else if (event_clk_counter0_en ) begin
	 event_clk_counter0_reg <= event_clk_counter0_reg + 1'b1;
    end
  end


  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
  	 event_clk_counter1_reg <= 32'b0;
    end else if (event_clk_counters_rst[1] ) begin
  	 event_clk_counter1_reg <= 32'b0;
    end else if (event_clk_counter1_en ) begin
	 event_clk_counter1_reg <= event_clk_counter1_reg + 1'b1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
  	 event_clk_counter2_reg <= 32'b0;
    end else if (event_clk_counters_rst[2] ) begin
  	 event_clk_counter2_reg <= 32'b0;
    end else if (event_clk_counter2_en ) begin
	 event_clk_counter2_reg <= event_clk_counter2_reg + 1'b1;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
  	 event_clk_counter3_reg <= 32'b0;
    end else if (event_clk_counters_rst[3] ) begin
  	 event_clk_counter3_reg <= 32'b0;
    end else if (event_clk_counter0_en ) begin
	 event_clk_counter3_reg <= event_clk_counter3_reg + 1'b1;
    end
  end

endmodule
