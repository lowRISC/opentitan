`timescale 1ns/1ps

module tb_without_uvm;

  // ===== 1) Imports for types/enums (no UVM) =====
  import tlul_pkg::*;
  import prim_ram_1p_pkg::*;
  import prim_alert_pkg::*;
  import top_racl_pkg::*;

  // If your i2c.sv defines parameters (like NumAlerts), mirror them here if needed.
  localparam int NumAlerts = 1; // <-- set to match your i2c instance (often 1 for I2C)

  // ===== 2) Clock / Reset =====
  logic clk_i = 0;
  logic rst_ni = 0;
  always #5 clk_i = ~clk_i;   // 100 MHz

  // ===== 3) External open-drain I2C wires =====
  logic scl, sda;
  // weak pull-ups -> idle '1'
  assign (weak0, weak1) scl = 1'b1;
  assign (weak0, weak1) sda = 1'b1;

  // ===== 4) DUT <-> pad wiring =====
  // DUT-side “core IO” signals
  logic cio_scl_o, cio_scl_en_o;
  logic cio_sda_o, cio_sda_en_o;
  // Feed external wires back into DUT inputs
  wire  cio_scl_i = scl;
  wire  cio_sda_i = sda;

  // Model open-drain: drive the external net low only when enable=1 and output=0.
  // Otherwise release (Z) so pull-up can bring it high.
  assign scl = (cio_scl_en_o && (cio_scl_o == 1'b0)) ? 1'b0 : 1'bz;
  assign sda = (cio_sda_en_o && (cio_sda_o == 1'b0)) ? 1'b0 : 1'bz;

  // ===== 5) RAM config (required) =====
  ram_1p_cfg_t     ram_cfg_i     = RAM_1P_CFG_DEFAULT;
  ram_1p_cfg_rsp_t ram_cfg_rsp_o;

  // ===== 6) TileLink-UL (TL-UL) bus =====
  // Keep bus idle by default; you can add tiny read/write tasks later if you need CSR access.
  tl_h2d_t tl_i;
  tl_d2h_t tl_o;

  task tl_idle();
    tl_i.a_valid   = 1'b0;
    tl_i.a_opcode  = '0;
    tl_i.a_param   = '0;
    tl_i.a_size    = 3'd2;  // 4B
    tl_i.a_source  = '0;
    tl_i.a_address = '0;
    tl_i.a_mask    = 4'hF;
    tl_i.a_data    = '0;
    tl_i.a_user    = '0;
    tl_i.d_ready   = 1'b1;
  endtask

  // ===== 7) Alerts (tie RX low; observe TX) =====
  alert_rx_t alert_rx_i [NumAlerts];
  alert_tx_t alert_tx_o [NumAlerts];
  initial begin
    for (int i = 0; i < NumAlerts; i++) begin
      alert_rx_i[i] = '0; // no incoming alerts from the fabric
    end
  end

  // ===== 8) RACL policy (tie-off) =====
  racl_policy_vec_t racl_policies_i = '0;
  racl_error_log_t  racl_error_o;

  // ===== 9) DUT =====
  i2c dut (
    .clk_i,
    .rst_ni,

    .ram_cfg_i     (ram_cfg_i),
    .ram_cfg_rsp_o (ram_cfg_rsp_o),

    .tl_i (tl_i),
    .tl_o (tl_o),

    .alert_rx_i (alert_rx_i),
    .alert_tx_o (alert_tx_o),

    .racl_policies_i (racl_policies_i),
    .racl_error_o    (racl_error_o),

    .cio_scl_i   (cio_scl_i),
    .cio_scl_o   (cio_scl_o),
    .cio_scl_en_o(cio_scl_en_o),
    .cio_sda_i   (cio_sda_i),
    .cio_sda_o   (cio_sda_o),
    .cio_sda_en_o(cio_sda_en_o),

    .lsio_trigger_o()   // unused
  );

  // ===== 10) Reset & basic scenario =====
  initial begin
    tl_idle();
    rst_ni = 0;
    repeat (10) @(posedge clk_i);
    rst_ni = 1;
    repeat (10) @(posedge clk_i);

    // If your glitch filter is controlled by CSRs, uncomment and use tl_write() here.
    // localparam I2C_BASE = 32'h4002_0000; // example; adjust for your IP-level build
    // tl_write(I2C_BASE + 'h04, 32'h0000_0005); // example: set filter threshold N=5

    // Inject a few glitches directly on the external wires
    inject_scl_glitch(3);   // shorter than threshold -> should be rejected
    inject_sda_glitch(2);
    repeat (20) @(posedge clk_i);

    inject_scl_glitch(5);   // exactly threshold -> boundary behavior
    inject_sda_glitch(5);
    repeat (20) @(posedge clk_i);

    inject_scl_glitch(8);   // longer than threshold -> should be accepted
    inject_sda_glitch(7);
    repeat (50) @(posedge clk_i);

    $display("DONE");
    $finish;
  end

  // ===== 11) Glitch inject tasks (no UVM needed) =====
  task automatic inject_scl_glitch(input int cycles);
    force scl = 1'b1;
    repeat (cycles) @(posedge clk_i);
    release scl;
  endtask

  task automatic inject_sda_glitch(input int cycles);
    force sda = 1'b1;
    repeat (cycles) @(posedge clk_i);
    release sda;
  endtask

  // ===== 12) Waves =====
  initial begin
    $dumpfile("i2c_simple.vcd");
    $dumpvars(0, tb);
  end

endmodule

