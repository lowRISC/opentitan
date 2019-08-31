module usb_fs_out_arb #(
  parameter NUM_OUT_EPS = 1
) (
  ////////////////////
  // endpoint interface 
  ////////////////////
  input [NUM_OUT_EPS-1:0] out_ep_req,
  output reg [NUM_OUT_EPS-1:0] out_ep_grant
);
  integer i;
  reg grant;

  always @* begin
    grant = 0;

    for (i = 0; i < NUM_OUT_EPS; i = i + 1) begin
      out_ep_grant[i] <= 0;

      if (out_ep_req[i] && !grant) begin
        out_ep_grant[i] <= 1;
        grant = 1;
      end
    end
  end
endmodule
