package sensor_ctrl_pkg;

  parameter int NumAlerts   = top_pkg::NUM_AST_ALERTS;
  parameter int NumIoRails  = top_pkg::NUM_IO_RAILS;
  parameter int AstAddrBits = top_pkg::AST_ADDRW;
  parameter int AstDataBits = top_pkg::AST_DATAW;

  typedef struct packed {
    logic req_valid;
    logic we;
    logic [AstAddrBits-1:0] addr;
    logic [AstDataBits-1:0] wdata;
  } ast_bus_req_t;

  typedef struct packed {
    logic rsp_valid;
    logic [AstDataBits-1:0] rdata;
  } ast_bus_rsp_t;

  // these are synchronization clocks needed by AST
  typedef struct packed {
    logic clk_ast_main;
    logic clk_ast_usb;
    logic clk_ast_io;
    logic clk_ast_muxed;
    logic rst_ast_main_n;
    logic rst_ast_usb_n;
    logic rst_ast_io_n;
  } ast_intf_t;

  parameter ast_bus_rsp_t AST_BUS_RSP_DEFAULT = '{
    rsp_valid: 1'b0,
    rdata:     '0
  };

  // Following should be moved to ast_wrapper
  typedef struct packed {
    logic [NumAlerts-1:0] alerts_p;
    logic [NumAlerts-1:0] alerts_n;
  } ast_alert_req_t;

  typedef struct packed {
    logic [NumAlerts-1:0] alerts_ack;
  } ast_alert_rsp_t;

  typedef struct packed {
    logic [NumIoRails-1:0] io_pok;
  } ast_status_t;

  parameter ast_alert_req_t AST_ALERT_REQ_DEFAULT = '{
    alerts_p: '0,
    alerts_n: {NumAlerts{1'b1}}
  };

  parameter ast_status_t AST_STATUS_DEFAULT = '{
    io_pok: {NumIoRails{1'b1}}
  };

  // Ack mode enumerations
  typedef enum logic {
    ImmAck = 0,
    SwAck  = 1
  } ast_ack_mode_e;


endpackage // sensor_ctrl_pkg
