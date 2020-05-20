package sensor_ctrl_pkg;

  parameter int NumAlerts   = top_pkg::NUM_AST_ALERTS;
  parameter int NumIoRails  = top_pkg::NUM_IO_RAILS;

  // auxillary information to ast
  // these are synchronization clocks needed by AST
  typedef struct packed {
    logic clk_ast_sys;
    logic clk_ast_usb;
    logic clk_ast_io;
    logic clk_ast_aon;
    logic rst_ast_sys_n;
    logic rst_ast_usb_n;
    logic rst_ast_io_n;
    logic rst_ast_aon_n;
  } ast_aux_t;

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
