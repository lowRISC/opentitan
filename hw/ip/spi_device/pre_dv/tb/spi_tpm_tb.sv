// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for spi_tpm
interface tpm_if (input clk);
  //logic sck;
  logic csb;
  logic mosi;
  logic miso;

  modport tb  (output csb, mosi, input  miso);
  modport dut (input  csb, mosi, output miso);

  //clocking tb_cb @ (posedge clk);
  //  // Negative edge drive, latch at 1 step
  //  default input #1step output negedge;
  //  output negedge csb;
  //  output mosi;
  //  input  miso;
  //endclocking : tb_cb

endinterface : tpm_if

module spi_tpm_tb;

  localparam time ClkPeriod = 10000;

  wire clk, rst_n;

  clk_rst_if main_clk (
    .clk,
    .rst_n
  );

  localparam time SckPeriod = 14000;

  wire sck, sck_rst_n;
  clk_rst_if sck_clk (
    .clk   (sck),
    .rst_n (sck_rst_n)
  );

  wire sck_en, gated_sck, gated_sck_inverted;

  assign gated_sck          = (sck_en) ? sck : 1'b 0;
  assign gated_sck_inverted = ~gated_sck;

  assign sck_en = ~tif.csb;

  localparam int unsigned CmdAddrFifoDepth = 2;
  localparam int unsigned WrFifoDepth      = 64;
  localparam int unsigned RdFifoDepth      = 4;
  localparam int unsigned RdFifoWidth      = 8;

  localparam bit EnLocality = 1;

  // Derived
  localparam int unsigned CmdAddrPtrW = $clog2(CmdAddrFifoDepth+1);
  localparam int unsigned WrFifoPtrW  = $clog2(WrFifoDepth+1);
  localparam int unsigned RdFifoPtrW  = $clog2(RdFifoDepth+1);
  localparam int unsigned CmdAddrSize = 32;
  localparam int unsigned FifoRegSize = 12; // fifo addr

  localparam int unsigned NumLocality = (EnLocality) ? 5 : 1 ;

  localparam int unsigned AccessRegSize    = 8 ;
  localparam int unsigned IntEnRegSize     = 32;
  localparam int unsigned IntVectorRegSize = 8 ;
  localparam int unsigned IntStsRegSize    = 32;
  localparam int unsigned IntfCapRegSize   = 32;
  localparam int unsigned StatusRegSize    = 32;
  localparam int unsigned IdRegSize        = 32; // {DID, VID}
  localparam int unsigned RidRegSize       = 8 ;

  tpm_if tif(sck);
  logic miso_en, miso;

  //assign tif.tb.sck   = gated_sck;
  assign tif.miso = (miso_en) ? miso : 1'b z;

  typedef struct packed {
    logic tpm_en;
    logic tpm_mode;
    logic hw_reg_dis;
    logic reg_chk_dis;
    logic invalid_locality;
  } cfg_t;

  cfg_t tpm_cfg;

  // FIFOs
  logic cmdaddr_rvalid, cmdaddr_rready;
  logic [31:0] cmdaddr_rdata;

  logic wrfifo_rvalid, wrfifo_rready;
  logic [7:0] wrfifo_rdata;

  logic rdfifo_wvalid, rdfifo_wready;
  logic [7:0] rdfifo_wdata;

  // status
  logic cmdaddr_notempty;
  logic [WrFifoPtrW-1:0] wrfifo_depth;
  logic [RdFifoPtrW-1:0] rdfifo_depth;

  spi_tpm #(
    .CmdAddrFifoDepth (CmdAddrFifoDepth),
    .WrFifoDepth      (WrFifoDepth     ),
    .RdFifoDepth      (RdFifoDepth     ),
    .RdDataFifoSize   (RdFifoWidth     ),
    .EnLocality       (EnLocality      )
  ) dut (
    .clk_in_i  (gated_sck),
    .clk_out_i (gated_sck_inverted),

    .sys_clk_i  (clk),
    .sys_rst_ni (rst_n),

    .scan_rst_ni ( 1'b 1 ),
    .scanmode_i  (prim_mubi_pkg::MuBi4False),

    .csb_i     (tif.csb     ),
    .mosi_i    (tif.mosi    ),
    .miso_o    (miso        ),
    .miso_en_o (miso_en     ),

    .tpm_cap_o (),

    .cfg_tpm_en_i               (tpm_cfg.tpm_en          ),
    .cfg_tpm_mode_i             (tpm_cfg.tpm_mode        ),
    .cfg_tpm_hw_reg_dis_i       (tpm_cfg.hw_reg_dis      ),
    .cfg_tpm_reg_chk_dis_i      (tpm_cfg.reg_chk_dis     ),
    .cfg_tpm_invalid_locality_i (tpm_cfg.invalid_locality),

    // Hw reg in SYS clk
    .sys_access_reg_i          (40'h 11_02_13_04_15), // Locality 0,2,4 active
    .sys_int_enable_reg_i      (32'h DEAD_BEEF     ),
    .sys_int_vector_reg_i      ( 8'h DE            ),
    .sys_int_status_reg_i      (32'h BEEF_DEAD     ),
    .sys_intf_capability_reg_i (32'h A5A5_5A5A     ),
    .sys_status_reg_i          (32'h ABCD_EF01     ),
    .sys_id_reg_i              (32'h 9876_5432     ),
    .sys_rid_reg_i             ( 8'h 10            ),

    .sys_cmdaddr_rvalid_o (cmdaddr_rvalid),
    .sys_cmdaddr_rdata_o  (cmdaddr_rdata ),
    .sys_cmdaddr_rready_i (cmdaddr_rready),

    .sys_wrfifo_rvalid_o (wrfifo_rvalid),
    .sys_wrfifo_rdata_o  (wrfifo_rdata ),
    .sys_wrfifo_rready_i (wrfifo_rready),

    .sys_rdfifo_wvalid_i (rdfifo_wvalid),
    .sys_rdfifo_wdata_i  (rdfifo_wdata ),
    .sys_rdfifo_wready_o (rdfifo_wready),

    .sys_cmdaddr_notempty_o (cmdaddr_notempty),
    .sys_rdfifo_notempty_o  (),
    .sys_rdfifo_depth_o     (rdfifo_depth),
    .sys_wrfifo_depth_o     (wrfifo_depth)
  );

  initial begin
    sck_clk.set_period_ps(SckPeriod);
    sck_clk.set_active();

    main_clk.set_period_ps(ClkPeriod);
    main_clk.set_active();

    tif.csb = 1'b 1;

    sck_clk.apply_reset();
    main_clk.apply_reset();


    // Fork for sw handling and host tb

    fork
      host();
      sw();
      begin
        #40us
        $display("TEST TIMED OUT!!");
        $finish();
      end
    join_any

    $display("TEST PASSED!");
    $finish();
  end


  ///////////
  // Tasks //
  ///////////

  // BEGIN: Host ==============================================================
  task host();
    automatic logic [7:0] data [$];

    sck_clk.wait_clks(10);

    // Read non return-by-HW regs
    tpm_read(24'h D4_00CE, 2, data); // invalid locality

    for (int i = 0 ; i < 2 ; i++) begin
      $display("Byte %d : $x", i, data.pop_front());
    end

    sck_clk.wait_clks(10);

    // Read return-by-HW regs
    tpm_read(24'h D4_0000, 4, data);

    for (int i = 0 ; i < 4 ; i++) begin
      $display("Byte %d : $x", i, data.pop_front());
    end

    sck_clk.wait_clks(10);

    tpm_read(24'h D4_ABCE, 2, data); // invalid locality

    sck_clk.wait_clks(10);

    data.delete();
    data.push_back(8'h EF);
    data.push_back(8'h BE);
    data.push_back(8'h AD);
    data.push_back(8'h DE);

    tpm_write(24'h D4_0110, 4, data);

    sck_clk.wait_clks(10);

    // Maximum Payload Transfer
    data.delete();
    repeat(64) begin
      data.push_back($urandom_range(255));
    end

    tpm_write(24'h D4_0110, 64, data);

    sck_clk.wait_clks(600);

    $display("Host transactions has ended.");

  endtask : host


  // tpm_header: Send command and address.
  // check the WAIT byte then if WAIT, wait until Start byte is received.
  task tpm_header (
    input bit          cmd_type, // 0: Write, 1: Read
    input logic [23:0] addr,
    input int unsigned xfer_size,
    output logic       wait_n     // 0: wait, 1: start
  );

    // Command
    tpm_sendbyte({cmd_type, 1'b 0, 6'(xfer_size-1)});

    // Send address
    fork
      for (int i = 2 ; i >= 0 ; i--) begin
        tpm_sendbyte(addr[8*i+:8]);
      end
      begin
        repeat (24) @(sck_clk.cb);
        wait_n = tif.miso;
      end
    join
  endtask : tpm_header

  task tpm_read (
    input  logic [23:0] addr,
    input  int unsigned xfer_size,
    output logic [7:0] rdata [$]
  );
    automatic logic [7:0] data;
    automatic logic       wait_n;

    tpm_start();

    tpm_header(1'b 1, addr, xfer_size, wait_n);

    forever begin
      if (wait_n == 1'b 1) begin
        break;
      end
      @(sck_clk.cb);
      tpm_readbyte(data);
      wait_n = data[0];
    end

    @(sck_clk.cbn);

    // Receive amount of xfer_size
    // Change MOSI high-z
    tif.mosi = 1'b z;
    @(sck_clk.cb);
    for (int i = 0 ; i < xfer_size ; i++) begin
      tpm_readbyte(data);
      rdata.push_back(data);
    end

    // tpm_readbyte finished in posedge of SCK
    @(sck_clk.cbn);
    tpm_stop();
  endtask : tpm_read


  task tpm_write (
    input logic [23:0] addr,
    input int unsigned xfer_size,
    input logic [7:0] wdata [$]
  );
    automatic logic [7:0] data;
    automatic logic       wait_n;
    tpm_start();

    tpm_header(1'b 0, addr, xfer_size, wait_n);

    // Check if wait
    forever begin
      if (wait_n == 1'b 1) begin
        break;
      end
      @(sck_clk.cb);
      tpm_readbyte(data);
      wait_n = data[0];
    end

    @(sck_clk.cbn);

    // Send (pop from wdata and send a byte)
    foreach(wdata[i]) begin
      tpm_sendbyte(wdata[i]);
      $display("Byte (%2d): %2xh", i, wdata[i]);
    end

    tpm_stop();
  endtask : tpm_write

  task tpm_sendbyte(
    input logic [7:0] data
  );
    // Assume TPM transaction already began
    // Send each bit at every negedge of the SCK
    // Assume the first is already negedge event.
    for (int i = 7 ; i >= 0 ; i--) begin
      tif.mosi = data[i];
      @(sck_clk.cbn);
    end
  endtask : tpm_sendbyte

  task tpm_readbyte(
    output logic [7:0] data
  );
    for (int i = 7 ; i > 0 ; i--) begin
      data[i] = tif.miso;
      @(sck_clk.cb);
    end
    data[0] = tif.miso;
  endtask : tpm_readbyte

  task tpm_start ();
    @(sck_clk.cbn); // negative clk
    tif.csb = 1'b 0;
  endtask : tpm_start

  task tpm_stop ();
    //@(sck_clk.cbn); // negative clk
    // Assume negedge
    // wait less than half of SCK
    #(SckPeriod/2100) // SckPeriod is in ps
    tif.csb = 1'b 1;
  endtask : tpm_stop

  // END:   Host --------------------------------------------------------------

  // SW ==============================================================
  task sw();
    // Wait event and loop
    logic [31:0] cmd;
    logic [31:0] tpm_reg;
    logic [6:0] xfer_size;
    logic [7:0] data;

    // Initial
    cmdaddr_rready = 1'b 0;

    // Configure
    tpm_cfg = '{
      tpm_en:           1'b 1,
      tpm_mode:         1'b 0, // FIFO
      hw_reg_dis:       1'b 0,
      reg_chk_dis:      1'b 0,
      invalid_locality: 1'b 1
    };

    rdfifo_wvalid = 1'b 0;
    rdfifo_wdata = 8'h 0;

    forever begin
      wait (cmdaddr_notempty == 1'b 1);

      // Read entry from cmd fifo
      cmdaddr_read(cmdaddr_rvalid, cmdaddr_rready, cmdaddr_rdata, cmd);
      xfer_size = cmd[24+:6] + 1; // xfer_size in the header is 0 based

      case (cmd[31])
        1'b 0: begin : write
          $display("TPM Write command process: Xfer Size (%d)", xfer_size);
          // pop from write fifo
          do begin
            wrfifo_read(wrfifo_rvalid, wrfifo_rready, wrfifo_rdata, data);
            xfer_size = xfer_size - 1;
            $display("TPM Write Data: %2x", data);
          end while (xfer_size != '0);
        end

        1'b 1: begin : read
          // Prepare random data up to xfer_size
          $display("TPM Read command process: Xfer Size (%d)", xfer_size);
          do begin
            data = $urandom_range(255);
            rdfifo_write(rdfifo_wvalid, rdfifo_wready, rdfifo_wdata, data);
            xfer_size = xfer_size - 1;
          end while (xfer_size != '0);
        end
      endcase
    end
  endtask : sw

  task cmdaddr_read (
    const ref              rvalid,
    ref       logic        rready, // output
    const ref logic [31:0] rdata,
    output    logic [31:0] data
  );
    @(posedge clk && rvalid);
    data   = rdata;
    rready = 1'b 1;

    @(posedge clk);
    rready = 1'b 0;
  endtask : cmdaddr_read

  task wrfifo_read (
    const ref             rvalid,
    ref       logic       rready, // output
    const ref logic [7:0] rdata,
    output    logic [7:0] data
  );
    @(posedge clk iff rvalid);
    data   = rdata;
    rready = 1'b 1;

    @(posedge clk);
    rready = 1'b 0;
  endtask : wrfifo_read

  task rdfifo_write (
    ref   logic       wvalid, // output
    const ref         wready,
    ref   logic [7:0] wdata,  // output
    input logic [7:0] data
  );
    wvalid = 1'b 1;
    wdata  = data;
    @(posedge clk iff wready);
    wvalid = 1'b 0;
  endtask : rdfifo_write
  // SW --------------------------------------------------------------

endmodule : spi_tpm_tb
