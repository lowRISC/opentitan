module oled_driver
  import prim_pkg::*;
  import oled_driver_reg_pkg::*;
(
  input clk_i,
  input rst_ni,

  input  tlul_pkg::tl_h2d_t tl_i,
  output tlul_pkg::tl_d2h_t tl_o,

  output cio_oled_sdin_o,
  output cio_oled_sdin_en_o,
  output cio_oled_sclk_o,
  output cio_oled_sclk_en_o,
  output cio_oled_dc_o,
  output cio_oled_dc_en_o,
  output cio_oled_res_o,
  output cio_oled_res_en_o,
  output cio_oled_vbat_o,
  output cio_oled_vbat_en_o,
  output cio_oled_vdd_o,
  output cio_oled_vdd_en_o
);

  oled_driver_reg2hw_t reg2hw;
  oled_driver_hw2reg_t hw2reg;

  tlul_pkg::tl_h2d_t  tl_win_h2d[1];
  tlul_pkg::tl_d2h_t  tl_win_d2h[1];

  oled_driver_reg_top u_reg(
    .clk_i,
    .rst_ni,

    .tl_i,
    .tl_o,

    .tl_win_o   (tl_win_h2d),
    .tl_win_i   (tl_win_d2h),

    .reg2hw,
    .hw2reg,

    .devmode_i  (1'b1)
  );

  logic update_start;
  logic update_ready;

  logic disp_on_start;
  logic disp_on_ready;

  logic disp_off_start;
  logic disp_off_ready;

  assign update_start        = reg2hw.cmd.disp_write.q & reg2hw.cmd.disp_write.qe;
  assign disp_on_start       = reg2hw.cmd.disp_on.q & reg2hw.cmd.disp_on.qe;
  assign disp_off_start      = reg2hw.cmd.disp_off.q & reg2hw.cmd.disp_off.qe;

  assign hw2reg.status.disp_ready.d = update_ready;
  assign hw2reg.status.on_ready.d   = disp_on_ready;
  assign hw2reg.status.off_ready.d  = disp_off_ready;

  logic        pbuf_req;
  logic        pbuf_gnt;
  logic        pbuf_we;
  logic [6:0]  pbuf_addr;
  logic [31:0] pbuf_wdata;
  logic [31:0] pbuf_wmask;
  logic [31:0] pbuf_rdata;
  logic        pbuf_rvalid;
  logic        pbuf_rerror;

  assign pbuf_rdata = '1;
  assign pbuf_rvalid = pbuf_req & ~pbuf_we;

  logic        pbuf_writing_q;
  logic        pbuf_writing_d;
  logic [1:0]  pbuf_byte_q;
  logic [1:0]  pbuf_byte_d;
  logic [6:0]  pbuf_held_addr;
  logic [31:0] pbuf_held_wdata;
  logic [31:0] pbuf_held_wmask;
  logic        pbuf_write_start;

  assign pbuf_gnt = pbuf_write_start;

  assign pbuf_write_start = ~pbuf_writing_q & pbuf_req & pbuf_we;
  assign pbuf_write_finish = pbuf_writing_q & (pbuf_byte_q == 2'b11);
  assign pbuf_writing_d = pbuf_write_start | (pbuf_writing_q & ~pbuf_write_finish);

  assign pbuf_byte_d = pbuf_write_start ? 2'b0 :
                                          pbuf_byte_q + 1'b1;

  always @(posedge clk_i or negedge rst_ni) begin
    if(~rst_ni) begin
      pbuf_writing_q <= 1'b0;
    end else begin
      pbuf_writing_q <= pbuf_writing_d;
    end
  end

  always @(posedge clk_i) begin
    pbuf_byte_q <= pbuf_byte_d;
    if(pbuf_write_start) begin
      pbuf_held_wdata <= pbuf_wdata;
      pbuf_held_wmask <= pbuf_wmask;
      pbuf_held_addr  <= pbuf_addr;
    end
  end

  logic       pbuf_write_byte_en;
  logic       pbuf_write_en;
  logic [8:0] pbuf_write_addr;
  logic [7:0] pbuf_write_data;

  assign pbuf_write_byte_en = (pbuf_byte_q == 2'b00) ? |pbuf_held_wmask[7:0]   :
                              (pbuf_byte_q == 2'b01) ? |pbuf_held_wmask[15:8]  :
                              (pbuf_byte_q == 2'b10) ? |pbuf_held_wmask[23:16] :
                                                       |pbuf_held_wmask[31:24];

  assign pbuf_write_en = pbuf_writing_q & pbuf_write_byte_en;
  assign pbuf_write_addr = {pbuf_held_addr, pbuf_byte_q};

  assign pbuf_write_data = (pbuf_byte_q == 2'b00) ? pbuf_held_wdata[7:0]   :
                           (pbuf_byte_q == 2'b01) ? pbuf_held_wdata[15:8]  :
                           (pbuf_byte_q == 2'b10) ? pbuf_held_wdata[23:16] :
                                                    pbuf_held_wdata[31:24];

  // TL ADAPTER SRAM
  tlul_adapter_sram #(
    .SramAw (7),
    .SramDw (32),
    .Outstanding (1),
    .ByteAccess  (1),
    .ErrOnRead   (1)
  ) u_tlul_adapter (
    .clk_i,
    .rst_ni,
    .tl_i   (tl_win_h2d[0]),
    .tl_o   (tl_win_d2h[0]),

    .req_o    (pbuf_req   ),
    .gnt_i    (pbuf_gnt   ),
    .we_o     (pbuf_we    ),
    .addr_o   (pbuf_addr  ), // Doesn't care the address other than sub-word
    .wdata_o  (pbuf_wdata ),
    .wmask_o  (pbuf_wmask ),
    .rdata_i  (pbuf_rdata ),
    .rvalid_i (pbuf_rvalid),
    .rerror_i (pbuf_rerror)
  );

  OLEDCtrl u_OLEDCtrl (
    .clk(clk_i),

    .update_start,
    .update_clear(1'b0),
    .update_ready,

    .disp_on_start,
    .disp_on_ready,

    .disp_off_start,
    .disp_off_ready,

    .toggle_disp_start(1'b0),
    .toggle_disp_ready(),

    .pbuf_write_en_i  (pbuf_write_en),
    .pbuf_write_data_i(pbuf_write_data),
    .pbuf_write_addr_i(pbuf_write_addr),

    .SDIN (cio_oled_sdin_o),
    .SCLK (cio_oled_sclk_o),
    .DC   (cio_oled_dc_o  ),
    .RES  (cio_oled_res_o ),
    .VBAT (cio_oled_vbat_o),
    .VDD  (cio_oled_vdd_o )
  );

  assign cio_oled_sdin_en_o = 1'b1;
  assign cio_oled_sclk_en_o = 1'b1;
  assign cio_oled_dc_en_o   = 1'b1;
  assign cio_oled_res_en_o  = 1'b1;
  assign cio_oled_vbat_en_o = 1'b1;
  assign cio_oled_vdd_en_o  = 1'b1;
endmodule

