package sensor_ctrl_pkg;

  parameter int NumAlerts   = top_pkg::NUM_AST_ALERTS;
  parameter int NumIoRails  = top_pkg::NUM_IO_RAILS;

  typedef struct packed {
    logic [NumIoRails-1:0] io_pok;
  } ast_status_t;

  parameter ast_status_t AST_STATUS_DEFAULT = '{
    io_pok: {NumIoRails{1'b1}}
  };

  // Ack mode enumerations
  typedef enum logic {
    ImmAck = 0,
    SwAck  = 1
  } ast_ack_mode_e;


endpackage // sensor_ctrl_pkg
