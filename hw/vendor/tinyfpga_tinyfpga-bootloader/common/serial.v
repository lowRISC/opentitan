module width_adapter #(
  parameter [31:0] INPUT_WIDTH = 8,
  parameter [31:0] OUTPUT_WIDTH = 1
) (
  input clk,
  input reset,

  input data_in_put,
  output data_in_free,
  input [INPUT_WIDTH-1:0] data_in,

  output data_out_put,
  input data_out_free,
  output [OUTPUT_WIDTH-1:0] data_out
);

  generate
    if (INPUT_WIDTH > OUTPUT_WIDTH) begin
      // wide to narrow conversion
      reg [INPUT_WIDTH:0] data_in_q;
      reg has_data;

      always @(posedge clk) begin
        if (!has_data && data_in_put) begin
          data_in_q <= {1'b1, data_in};
          has_data <= 1;
        end

        if (has_data && data_out_free) begin
          data_in_q <= data_in_q >> OUTPUT_WIDTH;
        end

        if (data_in_q == 1'b1) begin
          has_data <= 0;
        end
      end

      assign data_out = data_in_q[OUTPUT_WIDTH:1];
      assign data_out_put = has_data;


    end else if (INPUT_WIDTH < OUTPUT_WIDTH) begin
      // narrow to wide conversion


    end else begin
      assign data_in_free = data_out_free;
      assign data_out_put = data_in_put;
      assign data_out = data_in;
    end
  endgenerate

endmodule
