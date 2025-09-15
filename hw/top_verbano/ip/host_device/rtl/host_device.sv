
module host_device import tlul_pkg::*; (

  input clk_i,
  input rst_ni,

  // Host interfaces
  input  tlul_pkg::tl_h2d_t host_ctrl_tl_req_i,
  output tlul_pkg::tl_d2h_t host_ctrl_tl_rsp_o,

  output tlul_pkg::tl_h2d_t host_mailbox_tl_req_o,
  input  tlul_pkg::tl_d2h_t host_mailbox_tl_rsp_i

);


  import tl_peri_pkg::*;
  import mailbox_reg_pkg::*;

  localparam int AW = 32;
  localparam int DW = 32;
  localparam int DBW = DW/8;                    // Byte Width
  // The address and data to write (example)
  localparam WRITE_ADDR  = tl_peri_pkg::ADDR_SPACE_MAILBOX + mailbox_reg_pkg::MAILBOX_MESSAGE_PAYLOAD_1_OFFSET;
  localparam WRITE_DATA  = 32'hDEADBEEF;

  // FSM states
  typedef enum reg [2:0] {
      IDLE,
      WAIT_CNT,
      SEND_PUT,
      WAIT_RESP,
      DONE
  } state_t;

  // register signals
  logic           reg_we;
  logic           reg_re;
  logic [AW-1:0]  reg_addr;
  logic [DW-1:0]  reg_wdata;
  logic [DBW-1:0] reg_be;
  logic [DW-1:0]  reg_rdata;
  logic           reg_error;
  // State machine signals
  state_t state, next_state;
  logic [4:0] cnt_q, cnt_d;

  // Host device request and response signals
  logic        host_device_req_valid;
  logic [31:0] host_device_req_addr;
  logic        host_device_req_we;
  logic [31:0] host_device_req_wdata;
  logic [3:0]  host_device_req_be;
  logic        host_device_gnt;
  logic        host_device_rsp_valid;
  logic [31:0] host_device_rsp_data;
  logic        host_device_rsp_err;
  logic        host_device_rsp_intg_err;

  // outgoing integrity generation
  tlul_pkg::tl_d2h_t tl_o_pre;

  // tlul_fifo_async #(
  //   .ReqDepth        (1),
  //   .RspDepth        (1)
  // ) u_asf_35 (
  //   .clk_h_i      (clk_main_i),
  //   .rst_h_ni     (rst_main_ni),
  //   .clk_d_i      (clk_fixed_i),
  //   .rst_d_ni     (rst_fixed_ni),
  //   .tl_h_i       (tl_asf_35_us_h2d),
  //   .tl_h_o       (tl_asf_35_us_d2h),
  //   .tl_d_o       (tl_asf_35_ds_h2d),
  //   .tl_d_i       (tl_asf_35_ds_d2h)
  // );
  tlul_adapter_reg #(
    .RegAw(AW),
    .RegDw(DW),
    .EnableDataIntgGen(0)
  ) u_reg_if (
    .clk_i,
    .rst_ni,

    .tl_i (host_ctrl_tl_req_i),
    .tl_o (tl_o_pre),

    .en_ifetch_i(prim_mubi_pkg::MuBi4False),
    .intg_error_o(),

    .we_o    (reg_we),
    .re_o    (reg_re),
    .addr_o  (reg_addr),
    .wdata_o (reg_wdata),
    .be_o    (reg_be),
    .busy_i  (1'b0),
    .rdata_i (reg_rdata),
    .error_i (reg_error)
  );


  tlul_rsp_intg_gen #(
    .EnableRspIntgGen(1),
    .EnableDataIntgGen(1)
  ) u_rsp_intg_gen (
    .tl_i(tl_o_pre),
    .tl_o(host_ctrl_tl_rsp_o)
  );

  integer fp;

  initial begin
    fp = $fopen("host_device.log", "w");
    if (fp == 0) begin
      $fatal("Failed to open fp");
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      reg_rdata <= '0;
      reg_error <= 1'b0;
    end else begin
      if (reg_re) begin
        // Read operation
        $fwrite(fp, "Device Read: addr=0x%08x\n", reg_addr);
      end else if (reg_we) begin
        $fwrite(fp, "Device Write: addr=0x%08x, wdata=0x%08x\n", reg_addr, reg_wdata);
      end
      $fflush(fp); // Flush to ensure data is written
    end
  end

  final begin
    $fclose(fp);
  end

  // FSM state progression
  always @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
          state <= IDLE;
          cnt_q <= '0;
      end else begin
          state <= next_state;
          cnt_q <= cnt_d;
      end
  end

  tlul_adapter_host #(
    .MAX_REQS(1),
    .EnableDataIntgGen(1),
    .EnableRspDataIntgCheck(1)
  ) u_host_device_tlul_host (
    .clk_i,
    .rst_ni,
    // do not make a request unless there is room for the response
    .req_i          ( host_device_req_valid          ),
    .gnt_o          ( host_device_gnt                ),
    .addr_i         ( host_device_req_addr           ),
    .we_i           ( host_device_req_we             ),
    .wdata_i        ( host_device_req_wdata          ),
    .wdata_intg_i   ( tlul_pkg::TL_A_USER_DEFAULT.data_intg    ),
    .be_i           ( host_device_req_be             ),
    .instr_type_i   ( prim_mubi_pkg::MuBi4False      ),
    .user_rsvd_i    ( '0                             ),
    .valid_o        ( host_device_rsp_valid          ),
    .rdata_o        ( host_device_rsp_data           ),
    .rdata_intg_o   (                                ),
    .err_o          ( host_device_rsp_err            ),
    .intg_err_o     ( host_device_rsp_intg_err       ),
    .tl_o           ( host_mailbox_tl_req_o          ),
    .tl_i           ( host_mailbox_tl_rsp_i          )
  );

  // FSM and outputs
  always_comb begin
      // Defaults
      host_device_req_valid  = 1'b0;
      host_device_req_be    = 4'b1111;
      host_device_req_addr           = WRITE_ADDR;
      host_device_req_wdata          = WRITE_DATA;
      host_device_req_we             = 1'b1;
      next_state   = state;

      cnt_d        = cnt_q;
      case (state)
          IDLE: begin
              // Start transaction immediately
              next_state = reg_we && reg_addr == 32'h600000E8 ? WAIT_CNT : IDLE;
          end
          WAIT_CNT: begin
            cnt_d = cnt_q + 1;
            if (cnt_q == 5'd20) begin
              next_state = SEND_PUT;
              cnt_d      = '0;
            end
          end
          SEND_PUT: begin
              host_device_req_valid = 1'b1;
              if (host_device_gnt)
                  next_state = WAIT_RESP;
          end
          WAIT_RESP: begin
              if (host_device_rsp_valid)
                  next_state = DONE;
          end
          DONE: begin
              // Write complete: stay here or go to IDLE for repeat
              next_state = DONE;
          end
      endcase
  end


endmodule
