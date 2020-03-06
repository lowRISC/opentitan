package rstmgr_pkg;

  // global constants
  parameter int ALWAYS_ON_SEL = 0;

  // params that reference pwrmgr, should be replaced once pwrmgr is merged
  //localparam int AlwaysOnSel = pwrmgr_pkg::AlwaysOnDomain;
  //localparam int ExtResetReasons = pwrmgr_pkg::HwRstReqs;
  localparam int PowerDomains = 2;
  localparam int OffDomains = PowerDomains-1;
  localparam int ExtResetReasons = 2;

  // low power exit + external reasons + ndm_reset_req
  localparam int ResetReasons = 1 + ExtResetReasons + 1;

  // reasons for pwrmgr reset reset
  typedef enum logic [1:0] {
    None = 0,
    LowPwrEntry = 1,
    HwReq = 2,
    Undefined = 3
  } reset_cause_e;

  // pwrmgr interface (these are declared in pwrmgr_pkg), should remove once present
  typedef struct packed {
    logic [PowerDomains-1:0] rst_lc_req;
    logic [PowerDomains-1:0] rst_sys_req;
    reset_cause_e reset_cause;
  } pwr_rst_req_t;

  // rstmgr to pwrmgr
  typedef struct packed {
    logic [PowerDomains-1:0] rst_lc_src_n;
    logic [PowerDomains-1:0] rst_sys_src_n;
  } pwr_rst_rsp_t;

  // ast interface
  typedef struct packed {
    logic vcc_pok;
    logic alw_pok;
  } rstmgr_ast_t;

  // default value for rstmgr_ast_rsp_t (for dangling ports)
  parameter rstmgr_ast_t RSTMGR_AST_DEFAULT = '{
    vcc_pok: 1'b1,
    alw_pok: 1'b1
  };

  // resets generated and broadcast
  // This should be templatized and generated
  typedef struct packed {
    logic rst_por_n;
    logic rst_lc_n;
    logic rst_sys_fixed_n;
    logic rst_sys_n;
    logic rst_spi_device_n;
    logic rst_usb_n;
  } rstmgr_out_t;

  // peripherals reset requests
  typedef struct packed {
    logic rst_cpu_n;
    logic ndmreset_req;
  } rstmgr_cpu_t;

  // default value for rstmgr_ast_rsp_t (for dangling ports)
  parameter rstmgr_cpu_t RSTMGR_CPU_DEFAULT = '{
    rst_cpu_n: 1'b1,
    ndmreset_req: '0
  };

  // peripherals reset requests
  typedef struct packed {
    logic [ExtResetReasons-1:0] rst_reqs;
  } rstmgr_peri_t;

  // default value for rstmgr_ast_rsp_t (for dangling ports)
  parameter rstmgr_peri_t RSTMGR_PERI_DEFAULT = '{
    rst_reqs: '0
  };


endpackage // rstmgr_pkg
