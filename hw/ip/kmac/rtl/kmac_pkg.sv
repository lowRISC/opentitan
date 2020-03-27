package kmac_pkg;

  // Alerts
  localparam int                   NumAlerts = 2;
  localparam logic [NumAlerts-1:0] AlertAsyncOn = {NumAlerts{1'b1}};

endpackage

