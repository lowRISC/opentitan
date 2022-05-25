// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Testbench module for spid_jedec

module spid_upload_tb;

  import spi_device_pkg::*;

  import spid_common::*;

  localparam time ClkPeriod = 10000; // 10ns
  localparam time SckPeriod = 14000; // 14ns

  wire clk, rst_n;
  clk_rst_if main_clk (
    .clk,
    .rst_n
  );

  wire sck, sck_rst_n;
  clk_rst_if sck_clk (
    .clk   (sck),
    .rst_n (sck_rst_n)
  );

  spi_if sif(sck);

  virtual spi_if.tb  tb_sif  = sif.tb;
  virtual spi_if.dut dut_sif = sif.dut;

  logic [3:0] dut_sd_en, dut_sd;
  logic [3:0] tb_sd_en,  tb_sd;

  for (genvar i = 0 ; i < 4 ; i++) begin : g_dut_sif
    assign sif.sd_out[i] = dut_sd_en[i] ? dut_sd[i] : 1'b Z;
  end

  wire sck_en, gated_sck, gated_sck_inverted;

  assign gated_sck          = (sck_en) ? sck : 1'b 0;
  assign gated_sck_inverted = ~gated_sck;

  assign sck_en = ~sif.csb;

  logic rst_spi_n;
  assign rst_spi_n = sck_rst_n && ~sif.csb;

  sel_datapath_e dut_sel_dp;

  logic [CmdInfoIdxW-1:0] cmd_info_idx;
  cmd_info_t cmd_info;

  // CmdInfo is defined in spid_common.sv
  // ReserveStart:ReserveStart+2 are for upload test

  logic sck_busy_set; // SCK

  spi_mode_e spi_mode;

  logic               s2p_valid;
  logic [7:0]         s2p_data;
  logic [BitCntW-1:0] s2p_bitcnt;

  // Memory interface
  logic              bus_mem_req;
  logic              bus_mem_write;
  logic [SramAw-1:0] bus_mem_addr;
  logic [SramDw-1:0] bus_mem_wdata;
  logic [SramDw-1:0] bus_mem_wmask;
  logic              bus_mem_rvalid;
  logic [SramDw-1:0] bus_mem_rdata;
  logic [1:0]        bus_mem_rerror;

  localparam int unsigned ArbCnt = 3; // CmdAddr, Payload, Sw
  logic [ArbCnt-1:0] arb_req           ;
  logic [ArbCnt-1:0] arb_gnt           ;
  logic [ArbCnt-1:0] arb_write         ;
  logic [SramAw-1:0] arb_addr  [ArbCnt];
  logic [SramDw-1:0] arb_wdata [ArbCnt];
  logic [SramDw-1:0] arb_wmask [ArbCnt];
  logic [ArbCnt-1:0] arb_rvalid        ;
  logic [SramDw-1:0] arb_rdata [ArbCnt];
  logic [1:0]        arb_error [ArbCnt];

  spi_device_pkg::sram_l2m_t arb_l2m [ArbCnt];
  spi_device_pkg::sram_m2l_t arb_m2l [ArbCnt];

  spi_device_pkg::sram_l2m_t sw_l2m;
  spi_device_pkg::sram_m2l_t sw_m2l;
  assign arb_l2m[2] = sw_l2m;
  assign sw_m2l = arb_m2l[2];

  logic              spi_mem_req;
  logic              spi_mem_write;
  logic [SramAw-1:0] spi_mem_addr;
  logic [SramDw-1:0] spi_mem_wdata;
  logic [SramDw-1:0] spi_mem_wmask;
  logic              spi_mem_rvalid;
  logic [SramDw-1:0] spi_mem_rdata;
  logic [1:0]        spi_mem_rerror;

  spi_device_pkg::sram_l2m_t sck_l2m;
  spi_device_pkg::sram_m2l_t sck_m2l;

  // Connection arb
  for (genvar i = 0 ; i < ArbCnt ; i++) begin: g_arb
    assign arb_req  [i] = arb_l2m[i].req;
    assign arb_write[i] = arb_l2m[i].we;
    assign arb_addr [i] = arb_l2m[i].addr;
    assign arb_wdata[i] = arb_l2m[i].wdata;
    assign arb_wmask[i] = spi_device_pkg::sram_strb2mask(arb_l2m[i].wstrb);

    assign arb_m2l[i] = '{
      rvalid: arb_rvalid[i],
      rdata:  arb_rdata[i],
      rerror: arb_error[i]
    };
  end

  // Connection sck <-> spi_mem
  assign spi_mem_req   = sck_l2m.req;
  assign spi_mem_write = sck_l2m.we;
  assign spi_mem_addr  = sck_l2m.addr;
  assign spi_mem_wdata = sck_l2m.wdata;
  assign spi_mem_wmask = spi_device_pkg::sram_strb2mask(sck_l2m.wstrb);

  assign sck_m2l = '{
    rvalid: spi_mem_rvalid,
    rdata:  spi_mem_rdata,
    rerror: spi_mem_rerror
  };

  // FIFO
  logic cmdfifo_rvalid, cmdfifo_rready;
  logic [7:0] cmdfifo_rdata;
  logic addrfifo_rvalid, addrfifo_rready;
  logic [31:0] addrfifo_rdata;
  logic cmdfifo_notempty, addrfifo_notempty;
  logic cmdfifo_set_pulse;
  logic payload_overflow;
  logic [ $clog2(SramCmdFifoDepth+1)-1:0] cmdfifo_depth;
  logic [$clog2(SramAddrFifoDepth+1)-1:0] addrfifo_depth;
  logic [      $clog2(PayloadByte+1)-1:0] payload_depth;
  logic [        $clog2(PayloadByte)-1:0] payload_start_idx;

  // Upload module signals
  logic cfg_addr_4b_en;


  initial begin
    sck_clk.set_period_ps(SckPeriod);
    sck_clk.set_active();

    main_clk.set_period_ps(ClkPeriod);
    main_clk.set_active();

    sif.csb = 1'b 1;

    // Driving default inactive values on the interface
    sw_l2m.req = 1'b 0;
    cmdfifo_rready  = 1'b 0;
    addrfifo_rready = 1'b 0;

    cfg_addr_4b_en = 1'b 0;

    spi_mode = FlashMode;

    sck_clk.apply_reset();
    main_clk.apply_reset();

    fork
      begin
        #300us
        $display("TEST TIMED OUT!!");
        $finish();
      end
      host();
      sw();
    join_any

    $finish();
  end

  static task host();
    //  Prep data
    automatic logic [7:0] payload [$];
    automatic int unsigned payload_bytes;

    // Wait
    #200ns

    // Issue CmdOnly command
    spiflash_chiperase(sif.tb, 8'h C7);

    // Issue Cmd/Addr command
    repeat (10) @(sck_clk.cbn);
    spiflash_blockerase(sif.tb, 8'h 52, 32'h 00DE_ADBE, 1'b 0); // 32kB

    // Issue Cmd/Addr/Payload command
    repeat (30) @(sck_clk.cbn);
    spiflash_program(
      sif.tb,
      8'h 02,         // opcode
      32'h 00AD_BEEF, // addr
      1'b 0,          // addr_4b_en

      // payload
      '{
        8'h A5,
        8'h 5A,
        8'h AB,
        8'h CD,
        8'h EF,
        8'h DE,
        8'h AD,
        8'h BE,
        8'h EF
      }
    );

    // Cmd & Payload : Write Status

    // Cmd & Addr & Payload : less than 256B
    repeat (100) @(sck_clk.cbn);
    for (int i = 0 ; i < 255 ; i++) begin
      payload[i] = i;
    end
    spiflash_program(
      sif.tb,
      8'h 02,         // opcode
      32'h 00AB_CDEF, // addr
      1'b 0,          // addr_4b_en
      payload
    );
    payload = {};

    repeat(256) @(sck_clk.cbn); // Wait payload size (4clk per word read?)

    // Cmd & Addr & Payload : equal to 256B
    for (int i = 0 ; i < 256 ; i++) begin
      payload[i] = i;
    end
    spiflash_program(
      sif.tb,
      8'h 02,         // opcode
      32'h 00_0000, // addr
      1'b 0,          // addr_4b_en
      payload
    );
    payload = {};

    repeat(256) @(sck_clk.cbn); // Wait payload size (4clk per word read?)

    // Cmd & Addr & Payload : 256B < x <= 512B
    payload_bytes = $urandom_range(512, 257);
    for (int i = 0 ; i < payload_bytes; i++ ) begin
      payload[i] = i % PayloadByte;
    end
    spiflash_program(
      sif.tb,
      8'h 02,         // opcode
      32'h 00_0000, // addr
      1'b 0,          // addr_4b_en
      payload
    );
    payload = {};

    repeat(payload_bytes) @(sck_clk.cbn); // Wait payload size (4clk per word read?)

    // Cmd & Addr & Payload : greater than 512B
    payload_bytes = $urandom_range(1024, 513);
    for (int i = 0 ; i < payload_bytes; i++ ) begin
      payload[i] = i % PayloadByte ^ 8'(i/PayloadByte) ;
    end
    spiflash_program(
      sif.tb,
      8'h 02,         // opcode
      32'h 00_0000, // addr
      1'b 0,          // addr_4b_en
      payload
    );
    payload = {};

    repeat(payload_bytes) @(sck_clk.cbn); // Wait payload size (4clk per word read?)


    #10us // Wait enough for SW to pop
    @(sck_clk.cbn);
  endtask : host

  static task sw();
    automatic logic [ 7:0] cmd;
    automatic logic [31:0] addr;
    automatic logic [ 7:0] payload [$];

    forever begin
      // Check if fifo has entries inside
      // cmdfifo_notempty asserted when FIFO write happens.
      // it takes one more cycle to have valid read data
      // due to the latency that FIFO reads from DPSRAM.
      // Check cmdfifo_rvalid rather than cmdfifo_notempty
      @(posedge clk iff (cmdfifo_set_pulse == 1'b 1));
      cmd = cmdfifo_rdata;
      $display("Cmd %x is uploaded", cmd);
      cmdfifo_rready = 1'b 1;
      @(posedge clk);
      cmdfifo_rready = 1'b 0;

      // Decode command to check if addr/payload fields
      case (cmd) inside
        8'h C7, 8'h 06: begin
          // Do nothing to HW
          // Maybe checking busy set?
        end

        8'h 52, 8'h D8: begin
          // Wait until Addr not empty
          @(posedge clk iff (addrfifo_notempty == 1'b 1));
          addr = addrfifo_rdata;
          $display("Addr %x is received", addr);
          addrfifo_rready = 1'b 1;
          @(posedge clk);
          addrfifo_rready = 1'b 0;
        end

        8'h 01, 8'h 11: begin
          // Wait until CSb deasserted
          @(posedge clk iff (sif.csb == 1'b 1));

          // Due to CDC, payload depth updated later
          repeat (5) @(posedge clk);

          // fetch payload buffer
          read_sram(sw_l2m, sw_m2l,
            SramPayloadIdx, payload_depth, payload);
        end

        8'h 02, 8'h 42: begin
          // Wait until Addr not empty
          @(posedge clk iff (addrfifo_notempty == 1'b 1));
          addr = addrfifo_rdata;
          $display("Addr %x is received", addr);
          addrfifo_rready = 1'b 1;
          @(posedge clk);
          addrfifo_rready = 1'b 0;

          // Payload
          // Wait until CSb deasserted
          @(posedge clk iff (sif.csb == 1'b 1));

          // Due to CDC, payload depth updated later
          repeat (5) @(posedge clk);

          // fetch payload buffer
          if (payload_overflow) begin
            $display("Payload Overflow: Read from offset and max depth(%d)", payload_depth);
            $display("  Start Addr: 'h %8X",
                     SramPayloadIdx + (payload_start_idx >> OffsetW));
            read_sram_wrap(sw_l2m, sw_m2l,
              SramPayloadIdx,
              PayloadByte,
              SramPayloadIdx + (payload_start_idx >> OffsetW),
              payload_start_idx[0+:OffsetW],
              payload_depth,
              payload);
          end else begin
            assert(payload_start_idx == '0);
            read_sram(sw_l2m, sw_m2l,
              SramPayloadIdx, payload_depth, payload);
          end
        end

      endcase
    end

  endtask : sw

  // CSb pulse
  logic csb_sckin_sync_d, csb_sckin_sync_q, csb_asserted_pulse_sckin;
  prim_flop_2sync #(
    .Width      (1),
    .ResetValue (1'b 1)
  ) u_csb_sckin_sync (
    .clk_i (gated_sck),
    .rst_ni(rst_spi_n), //Use CSb as a reset
    .d_i (1'b 0),
    .q_o (csb_sckin_sync_d)
  );
  always_ff @(posedge gated_sck or negedge rst_spi_n) begin
    if (!rst_spi_n) csb_sckin_sync_q <= 1'b 1;
    else            csb_sckin_sync_q <= csb_sckin_sync_d;
  end

  assign csb_asserted_pulse_sckin = csb_sckin_sync_q && !csb_sckin_sync_d;

  // CSb deassertion pulse generator
  logic csb_sync, csb_sync_q, csb_deasserted_busclk;
  prim_flop_2sync #(
    .Width      (1),
    .ResetValue (1'b 1)
  ) u_csb_sync (
    .clk_i   (clk),
    .rst_ni  (rst_n),
    .d_i     (sif.csb),
    .q_o     (csb_sync)
  );
  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) csb_sync_q <= 1'b 1;
    else        csb_sync_q <= csb_sync;
  end

  assign csb_deasserted_busclk = !csb_sync_q && csb_sync;

  logic p2s_valid, p2s_sent;
  logic [7:0] p2s_data;

  io_mode_e dut_iomode, s2p_iomode;

  spid_upload #(
    .CmdFifoBaseAddr  (SramCmdFifoIdx),
    .CmdFifoDepth     (SramCmdFifoDepth),
    .AddrFifoBaseAddr (SramAddrFifoIdx),
    .AddrFifoDepth    (SramAddrFifoDepth),
    .PayloadBaseAddr  (SramPayloadIdx),
    .PayloadDepth     (SramPayloadDepth),

    .SpiByte ($bits(spi_byte_t))
  ) u_upload (
    .clk_i  (gated_sck),
    .rst_ni (rst_spi_n),

    .sys_clk_i  (clk),
    .sys_rst_ni (rst_n),

    .clk_csb_i  (sif.csb),

    .sys_csb_deasserted_pulse_i (csb_deasserted_busclk),

    .sel_dp_i (dut_sel_dp),

    .sck_sram_o (sck_l2m),
    .sck_sram_i (sck_m2l),

    .sys_cmdfifo_sram_o (arb_l2m[0]),
    .sys_cmdfifo_sram_i (arb_m2l[0]),
    .sys_cmdfifo_gnt_i  (arb_gnt[0]),

    .sys_addrfifo_sram_o (arb_l2m[1]),
    .sys_addrfifo_sram_i (arb_m2l[1]),
    .sys_addrfifo_gnt_i  (arb_gnt[1]),

    // SYS clock FIFO interface
    .sys_cmdfifo_rvalid_o (cmdfifo_rvalid),
    .sys_cmdfifo_rready_i (cmdfifo_rready),
    .sys_cmdfifo_rdata_o  (cmdfifo_rdata),

    .sys_addrfifo_rvalid_o (addrfifo_rvalid),
    .sys_addrfifo_rready_i (addrfifo_rready),
    .sys_addrfifo_rdata_o  (addrfifo_rdata),

    // Interface: SPI to Parallel
    .s2p_valid_i  (s2p_valid),
    .s2p_byte_i   (s2p_data),
    .s2p_bitcnt_i (s2p_bitcnt),

    // Interface: Parallel to SPI
    .p2s_valid_o (p2s_valid),
    .p2s_data_o  (p2s_data ),
    .p2s_sent_i  (p2s_sent ),

    .spi_mode_i (spi_mode),

    .cfg_addr_4b_en_i (cfg_addr_4b_en),

    .cmd_info_i     (cmd_info),
    .cmd_info_idx_i (cmd_info_idx),

    .io_mode_o (dut_iomode),

    .set_busy_o (sck_busy_set),

    .sys_cmdfifo_set_o       (cmdfifo_set_pulse),
    .sys_cmdfifo_notempty_o  (cmdfifo_notempty),
    .sys_cmdfifo_full_o      (), // not used
    .sys_addrfifo_notempty_o (addrfifo_notempty),
    .sys_addrfifo_full_o     (), // not used
    .sys_payload_overflow_o  (payload_overflow),

    .sys_cmdfifo_depth_o     (cmdfifo_depth),
    .sys_addrfifo_depth_o    (addrfifo_depth),
    .sys_payload_depth_o     (payload_depth),
    .sys_payload_start_idx_o (payload_start_idx)
  );

  spi_cmdparse cmdparse (
    .clk_i  (gated_sck),
    .rst_ni (rst_spi_n),

    .data_valid_i (s2p_valid),
    .data_i       (s2p_data ),

    .spi_mode_i   (spi_mode),

    .cmd_info_i   (spid_common::CmdInfo),

    .io_mode_o    (s2p_iomode),

    .sel_dp_o       (dut_sel_dp),
    .cmd_info_o     (cmd_info),
    .cmd_info_idx_o (cmd_info_idx),

    .cmd_config_req_o (),
    .cmd_config_idx_o ()
  );

  spi_s2p s2p (
    .clk_i  (gated_sck),
    .rst_ni (rst_spi_n),

    .s_i    (sif.sd_in),

    .data_valid_o (s2p_valid),
    .data_o       (s2p_data),
    .bitcnt_o     (s2p_bitcnt),

    .order_i      (1'b 0),
    .io_mode_i    (s2p_iomode)
  );

  spi_p2s p2s (
    .clk_i  (gated_sck_inverted),
    .rst_ni (rst_spi_n),

    .data_valid_i (p2s_valid),
    .data_i       (p2s_data),
    .data_sent_o  (p2s_sent),

    .csb_i        (sif.csb),
    .s_en_o       (dut_sd_en),
    .s_o          (dut_sd),

    .cpha_i       (1'b 0),

    .order_i      (1'b 0),

    .io_mode_i    (dut_iomode)
  );

  // Memory (DPSRAM)
  prim_ram_2p_async_adv #(
    .Depth (1024),      // 4kB
    .Width (SramDw),    // 32
    .DataBitsPerMask (8),

    .EnableECC           (0),
    .EnableParity        (1),
    .EnableInputPipeline (0),
    .EnableOutputPipeline(0)
  ) u_memory_2p (
    .clk_a_i    (clk),
    .rst_a_ni   (rst_n),

    .clk_b_i    (gated_sck),
    .rst_b_ni   (rst_n),

    .a_req_i    (bus_mem_req),
    .a_write_i  (bus_mem_write),
    .a_addr_i   (bus_mem_addr),
    .a_wdata_i  (bus_mem_wdata),
    .a_wmask_i  (bus_mem_wmask),
    .a_rvalid_o (bus_mem_rvalid),
    .a_rdata_o  (bus_mem_rdata),
    .a_rerror_o (bus_mem_rerror),

    .b_req_i    (spi_mem_req),
    .b_write_i  (spi_mem_write),
    .b_addr_i   (spi_mem_addr),
    .b_wdata_i  (spi_mem_wdata),
    .b_wmask_i  (spi_mem_wmask),
    .b_rvalid_o (spi_mem_rvalid),
    .b_rdata_o  (spi_mem_rdata),
    .b_rerror_o (spi_mem_rerror),

    .cfg_i      ('0)
  );

  // Arbiter for bus clock
  // 0: cmdaddr_sram
  // 1: payload_sram
  // 2: sw_sram
  // condition, should be one-hot0 for the requests
  prim_sram_arbiter #(
    .N      (ArbCnt),
    .SramDw (SramDw),
    .SramAw (SramAw)
  ) u_bus_arbiter (
    .clk_i  (clk  ),
    .rst_ni (rst_n),

    .req_i       (arb_req  ),
    .req_addr_i  (arb_addr ),
    .req_write_i (arb_write),
    .req_wdata_i (arb_wdata),
    .req_wmask_i (arb_wmask),
    .gnt_o       (arb_gnt  ),

    .rsp_rvalid_o (arb_rvalid),
    .rsp_rdata_o  (arb_rdata ),
    .rsp_error_o  (arb_error ),

    .sram_req_o    (bus_mem_req   ),
    .sram_addr_o   (bus_mem_addr  ),
    .sram_write_o  (bus_mem_write ),
    .sram_wdata_o  (bus_mem_wdata ),
    .sram_wmask_o  (bus_mem_wmask ),
    .sram_rvalid_i (bus_mem_rvalid),
    .sram_rdata_i  (bus_mem_rdata ),
    .sram_rerror_i (bus_mem_rerror)
  );

  static task read_sram(
    ref       sram_l2m_t l2m,
    const ref sram_m2l_t m2l,
    input logic [SramAw-1:0] addr,
    input int unsigned       size,    // in byte
    output logic [7:0]       data [$]
  );
    automatic logic [7:0] result [$];

    automatic int unsigned loop = (size+(SramDw/8)-1)/(SramDw/8);

    // Fetch
    for (int i = 0 ; i < loop; i++) begin
      l2m.addr  = addr + i;
      l2m.we    = 1'b 0;
      l2m.wstrb = '1;
      l2m.wdata = '0;
      l2m.req   = 1'b 1;
      fork
        begin
          @(posedge clk);
          l2m.req   = 1'b 0;
        end
        begin
          @(posedge clk iff (m2l.rvalid == 1'b1));
          for (int j = 0 ; j < SramDw/8 ; j++) begin
            result.push_back(m2l.rdata[8*j+:8]);
          end
          $display("Read Sram @ %x: %x", (addr+i), m2l.rdata);

          // Wait m2l.rvalid lowered
          @(posedge clk iff (m2l.rvalid == 1'b 0));
        end
      join
    end

    data = result;
  endtask : read_sram

  static task read_sram_wrap(
    ref       sram_l2m_t      l2m,
    const ref sram_m2l_t      m2l,
    input logic [SramAw-1:0]  BaseAddr, // Buffer Base Address
    input int                 MaxSize,  // Max buffer size (in bytes)
    input logic [SramAw-1:0]  addr,
    input logic [OffsetW-1:0] offset,
    input int unsigned        size,     // in byte
    output logic [7:0]        data [$]
  );
    automatic logic [7:0] result    [$];
    automatic logic [7:0] sram_data [$];
    automatic logic [SramAw-1:0]  current_addr;
    automatic logic [OffsetW-1:0] current_offset;
    automatic int                 remained_bytes;
    automatic int                 request_bytes; // sram request bytes

    // Check if wrap
    automatic bit wrap = (({BaseAddr, {OffsetW{1'b0}}} + MaxSize)
                       > ({addr, offset} + size)) ? 1'b 1 : 1'b 0;

    if (wrap) begin
      $display("Overflow: Read will be twice");
    end
    //  don't wrap: just read. loop depends on the offset, size
    //
    //  wrap: first:  (2*size - MaxSize) bytes
    //        second: (MaxSize - size)   bytes
    current_addr   = addr;
    current_offset = offset;
    remained_bytes = size;

    do begin
      $display("Transaction: CurAddr('h%X) / CurOffset('h%X) / RemainedByte('d%3d)",
               current_addr, current_offset, remained_bytes);
      // start addr of current transaction

      // end addr of current transaction
      if (({BaseAddr, {OffsetW{1'b0}}} + MaxSize) < ({current_addr, current_offset} + remained_bytes)) begin
        // Read to the end of the buffer
        request_bytes = MaxSize - (current_addr - BaseAddr)*(SramDw/8);
      end else begin
        // Request only remained bytes
        request_bytes = remained_bytes;
      end

      // request SRAM read
      $display("Sending SRAM request");
      read_sram(l2m, m2l, current_addr, request_bytes, sram_data);

      // push to result (based on current_offset, currnt_size)
      $display("Pushing the return data(from SRAM) into the result queue");
      data = {data, sram_data[current_offset:$]}; // push back the sram read

      // start addr of next transaction
      $display("Calculating for the next SRAM transaction");
      remained_bytes = remained_bytes - (request_bytes - current_offset);
      current_offset = '0; // always word based for the next transaction
      current_addr = BaseAddr; // always read from the first entry of buffer

      sram_data = {}; // Delete all

      if (remained_bytes == 0) begin
        $display("All payloads are read out.");
      end else begin
        $display("Still pending bytes ('d%3d). Requesting the next transaction",
          remained_bytes);
      end
    end while (remained_bytes != 0);


    // Check the # entires per transaction
    // first entry, addr
    // last entry,  ceil({addr,offset} + size)/(SramDw/8)

  endtask : read_sram_wrap

endmodule : spid_upload_tb
