module usb_fs_in_arb #(
  parameter NUM_IN_EPS = 1
) (
  ////////////////////
  // endpoint interface 
  ////////////////////
  input [NUM_IN_EPS-1:0] in_ep_req,
  output reg [NUM_IN_EPS-1:0] in_ep_grant,
  input [(NUM_IN_EPS*8)-1:0] in_ep_data,


  ////////////////////
  // protocol engine interface 
  ////////////////////
  output reg [7:0] arb_in_ep_data
);
  integer i;
  reg grant;
 
  always @* begin
    grant = 0;

    arb_in_ep_data <= 0;

    for (i = 0; i < NUM_IN_EPS; i = i + 1) begin
      in_ep_grant[i] <= 0;

      if (in_ep_req[i] && !grant) begin
        in_ep_grant[i] <= 1;
        arb_in_ep_data <= in_ep_data[i * 8 +: 8];
        grant = 1;
      end
    end
  end
endmodule
