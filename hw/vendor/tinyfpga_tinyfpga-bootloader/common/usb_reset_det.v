// detects USB port reset signal from host
module usb_reset_det (
  input clk,
  output reset,

  input usb_p_rx,
  input usb_n_rx
);
  // reset detection
  reg [16:0] reset_timer = 0;
  reg reset_i = 0;


  wire timer_expired = reset_timer > 16'd30000;
  always @(posedge clk) reset_i <= timer_expired;
  assign reset = reset_i;
 
  
  always @(posedge clk) begin
    if (usb_p_rx || usb_n_rx) begin
      reset_timer <= 0;
    end else begin
      // SE0 detected from host
      if (!timer_expired) begin
        // timer not expired yet, keep counting
        reset_timer <= reset_timer + 1;
      end
    end
  end
  
endmodule
