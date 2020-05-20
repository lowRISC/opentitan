package sensor_ctrl_pkg;

  parameter int NumAlerts   = sensor_ctrl_reg_pkg::NumAlerts;
  parameter int NumIoRails  = sensor_ctrl_reg_pkg::NumIoRails;
  parameter int AstAddrBits = 12;
  parameter int AstDataBits = 32;

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
