package ast_wrapper_pkg;

  parameter int NumAlerts      = top_pkg::NUM_AST_ALERTS;
  parameter int NumIoRails     = top_pkg::NUM_IO_RAILS;
  parameter int EntropyStreams = top_pkg::ENTROPY_STREAM;
  parameter int AdcChannels    = top_pkg::ADC_CHANNELS;
  parameter int AdcDataWidth   = top_pkg::ADC_DATAW;
  parameter int AstAddrBits    = top_pkg::AST_ADDRW;
  parameter int AstDataBits    = top_pkg::AST_DATAW;

  // The following structs should eventually be relocted to other modules
  typedef struct packed {
    logic [AdcChannels-1:0] channel_sel;
    logic pd;
  } adc_ast_req_t;

  typedef struct packed {
    logic [AdcDataWidth-1:0] data;
    logic data_valid;
  } adc_ast_rsp_t;


  typedef struct packed {
    logic rng_en;
  } es_ast_req_t;

  typedef struct packed {
    logic rng_ok;
    logic [EntropyStreams-1:0] rng_b;
  } es_ast_rsp_t;


  typedef struct packed {
    logic vcc_pok;
    logic aon_pok;
  } ast_rst_t;

  typedef struct packed {
    logic clk_main;
    logic clk_io;
    logic clk_usb;
    logic clk_aon;
  } ast_clks_t;

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

  // Ack mode enumerations
  typedef enum logic {
    ImmAck = 0,
    SwAck  = 1
  } ast_ack_mode_e;


endpackage // rstmgr_pkg
