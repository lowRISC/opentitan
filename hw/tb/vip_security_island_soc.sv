// Copyright 2023 ETH Zurich and University of Bologna.
// Solderpad Hardware License, Version 0.51, see LICENSE for details.
// SPDX-License-Identifier: SHL-0.51
//
// Alessandro Ottaviano <aottaviano@iis.ee.ethz.ch>

// collects all existing verification ip (vip) for carfield SoC

module vip_security_island_soc
  import carfield_pkg::*;
  import cheshire_pkg::*;
#(
  // Timing
  parameter time         ClkPeriodSys      = 10ns,
  parameter time         ClkPeriodJtag     = 20ns,
  parameter int unsigned RstCycles         = 5,
  parameter real         TAppl             = 0.1,
  parameter real         TTest             = 0.9,
  // UART
  parameter int unsigned UartBaudRate      = 1250000,
  parameter int unsigned UartParityEna     = 0,
  parameter int unsigned UartBurstBytes    = 256,
  parameter int unsigned UartWaitCycles    = 60
) (
  output logic       clk_vip,
  output logic       rst_n_vip,
  // secure boot enabled
  output logic       secure_boot,
  output logic [1:0] bootmode,
  // UART interface
  input logic        uart_tx,
  output logic       uart_rx,
  // JTAG interface
  output logic       jtag_tck,
  output logic       jtag_trst_n,
  output logic       jtag_tms,
  output logic       jtag_tdi,
  input logic        jtag_tdo,
  // SPI hots
  output logic [3:0] spi_secd_sd_o,
  input logic [3:0]  spi_secd_sd_i,
  input logic [3:0]  spi_secd_sd_oe_i,
  input logic        spi_secd_csb_oe_i,
  input logic        spi_secd_csb_i,
  input logic        spi_secd_sck_oe_i,
  input logic        spi_secd_sck_i
);

  ///////////////////////////////
  //  SoC Clock, Reset, Modes  //
  ///////////////////////////////

  logic clk, rst_n;
  assign clk_vip   = clk;
  assign rst_n_vip = rst_n;

  initial begin
    bootmode = '0;
  end

  clk_rst_gen #(
    .ClkPeriod    ( ClkPeriodSys ),
    .RstClkCycles ( RstCycles )
  ) i_clk_rst_sys (
    .clk_o  ( clk   ),
    .rst_no ( rst_n )
  );

  task wait_for_reset;
    @(posedge rst_n);
    @(posedge clk);
  endtask

  task set_secd_boot_mode(input logic [1:0] mode);
    bootmode = mode;
  endtask

  /////////////////
  // Secure boot //
  /////////////////

  // TODO: secure boot emulation mode is currently not tested
  assign secure_boot = bootmode[0];

  ////////////////
  //  SPI Host  //
  ////////////////

  wire  SPI_D0, SPI_D1, SPI_SCK, SPI_CSB, WPNeg, RESETNeg;
  wire  PWROK_S, IOPWROK_S, BIAS_S, RETC_S;

  assign RESETNeg = 1'b1;
  assign WPNeg    = 1'b0;

  pad_alsaqr i_I0 ( .OEN(~spi_secd_sd_oe_i[0]), .I(spi_secd_sd_i[0]), .O(), .PUEN(1'b1), .PAD(SPI_D0),
                    .DRV(2'b00), .SLW(1'b0), .SMT(1'b0), .PWROK(PWROK_S),
                    .IOPWROK(IOPWROK_S), .BIAS(BIAS_S), .RETC(RETC_S)   );
  pad_alsaqr i_I1 ( .OEN(~spi_secd_sd_oe_i[1]), .I(), .O(spi_secd_sd_o[1]), .PUEN(1'b1), .PAD(SPI_D1),
                    .DRV(2'b00), .SLW(1'b0), .SMT(1'b0), .PWROK(PWROK_S),
                    .IOPWROK(IOPWROK_S), .BIAS(BIAS_S), .RETC(RETC_S)   );
  pad_alsaqr i_SCK (.OEN(~spi_secd_sck_oe_i), .I(spi_secd_sck_i), .O(), .PUEN(1'b1), .PAD(SPI_SCK),
                    .DRV(2'b00), .SLW(1'b0), .SMT(1'b0), .PWROK(PWROK_S),
                    .IOPWROK(IOPWROK_S), .BIAS(BIAS_S), .RETC(RETC_S)   );
  pad_alsaqr i_CSB (.OEN(~spi_secd_csb_oe_i), .I(spi_secd_csb_i), .O(), .PUEN(1'b1), .PAD(SPI_CSB),
                    .DRV(2'b00), .SLW(1'b0), .SMT(1'b0), .PWROK(PWROK_S),
                    .IOPWROK(IOPWROK_S), .BIAS(BIAS_S), .RETC(RETC_S)   );

  s25fs512s #(
    .UserPreload ( 0 )
  ) i_spi_norflash (
    .SI       ( SPI_D0   ),
    .SO       ( SPI_D1   ),
    .WPNeg    ( RESETNeg ),
    .RESETNeg ( WPNeg    ),
    .SCK      ( SPI_SCK  ),
    .CSNeg    ( SPI_CSB  )
  );

  // Preload function called by testbench
  task automatic spih_norflash_preload(string image);
    // We overlay the entire memory with an alternating pattern
    for (int k = 0; k < $size(i_spi_norflash.Mem); ++k)
        i_spi_norflash.Mem[k] = 'h9a;
    // We load an image into chip 0 only if it exists
    if (image != "")
      $readmemh(image, i_spi_norflash.Mem);
  endtask

  //////////
  // JTAG //
  //////////

  localparam         AxiWideBeWidth_ib    = 4;
  localparam         AxiWideByteOffset_ib = $clog2(AxiWideBeWidth_ib);
  logic [31:0]       secd_memory   [bit [31:0]];
  int                secd_sections [bit [31:0]];

  clk_rst_gen #(
    .ClkPeriod    ( ClkPeriodJtag ),
    .RstClkCycles ( RstCycles )
  ) i_clk_secd_jtag (
    .clk_o  ( jtag_tck ),
    .rst_no ( )
  );

  JTAG_DV jtag_secd(jtag_tck);

  typedef jtag_ot_test::riscv_dbg #(
    .IrLength ( 5 ),
    .TA       ( ClkPeriodJtag * TAppl ),
    .TT       ( ClkPeriodJtag * TTest )
  ) riscv_dbg_ot_t;

  riscv_dbg_ot_t::jtag_driver_t  jtag_secd_dv   = new (jtag_secd);
  riscv_dbg_ot_t                 jtag_secd_dbg  = new (jtag_secd_dv);

  assign jtag_trst_n   = jtag_secd.trst_n;
  assign jtag_tms      = jtag_secd.tms;
  assign jtag_tdi      = jtag_secd.tdi;
  assign jtag_secd.tdo = jtag_tdo;

  initial begin
    @(negedge rst_n);
    jtag_secd_dbg.reset_master();
  end

  task debug_secd_module_init;
     logic [31:0]  idcode;
     automatic dm_ot::sbcs_t sbcs = '{
       sbautoincrement: 1'b1,
       sbreadondata   : 1'b1,
       sbaccess       : 3'h2,
       default        : 1'b0
     };
     //dm_ot::dtm_op_status_e op;
     automatic int dmi_wait_cycles = 10;
     $display("[JTAG SECD] JTAG Preloading Starting");
     jtag_secd_dbg.wait_idle(300);
     jtag_secd_dbg.get_idcode(idcode);
     // Check Idcode
     $display("[JTAG SECD] IDCode = %h", idcode);
     // Activate Debug Module
     jtag_secd_dbg.write_dmi(dm_ot::DMControl, 32'h0000_0001);
     do jtag_secd_dbg.read_dmi(dm_ot::SBCS, sbcs, dmi_wait_cycles);
     while (sbcs.sbbusy);

  endtask

  task jtag_secd_data_preload;
     logic [31:0] rdata;
     automatic dm_ot::sbcs_t sbcs = '{
       sbautoincrement: 1'b1,
       sbreadondata   : 1'b1,
       sbaccess       : 3'h2,
       default        : 1'b0
     };
     automatic int dmi_wait_cycles = 10;
     debug_secd_module_init();
     jtag_secd_dbg.write_dmi(dm_ot::SBCS, sbcs);
     do jtag_secd_dbg.read_dmi(dm_ot::SBCS, sbcs, dmi_wait_cycles);
     while (sbcs.sbbusy);
     // Start writing to SRAM
     foreach (secd_sections[addr]) begin
       $display("[JTAG SECD] Writing %h with %0d words", addr << 2, secd_sections[addr]); // word = 8 bytes here
       jtag_secd_dbg.write_dmi(dm_ot::SBAddress0, (addr << 2));
       do jtag_secd_dbg.read_dmi(dm_ot::SBCS, sbcs, dmi_wait_cycles);
       while (sbcs.sbbusy);
       for (int i = 0; i < secd_sections[addr]; i++) begin
         if (i%100 == 0)
           $display("[JTAG SECD] loading: %0d/100%%", i*100/secd_sections[addr]);
         jtag_secd_dbg.write_dmi(dm_ot::SBData0, secd_memory[addr + i]);
         // Wait until SBA is free to write next 32 bits
         do jtag_secd_dbg.read_dmi(dm_ot::SBCS, sbcs, dmi_wait_cycles);
         while (sbcs.sbbusy);
       end
       $display("[JTAG SECD] loading: 100/100%%");
     end
    $display("[JTAG SECD] Preloading finished");
    // Preloading finished. Can now start executing
    sbcs.sbreadonaddr = 0;
    sbcs.sbreadondata = 0;
    jtag_secd_dbg.write_dmi(dm_ot::SBCS, sbcs);

  endtask

  task jtag_secd_wakeup;
    input logic [31:0] start_addr;
    logic [31:0] dm_status;

    automatic dm_ot::sbcs_t sbcs = '{
      sbautoincrement: 1'b1,
      sbreadondata   : 1'b1,
      sbaccess       : 3'h2,
      default        : 1'b0
    };
    //dm_ot::dtm_op_status_e op;
    automatic int dmi_wait_cycles = 10;
    $display("[JTAG SECD] Waking up Secd");
    // Initialize the dm module again, otherwise it will not work
    debug_secd_module_init();
    do jtag_secd_dbg.read_dmi(dm_ot::SBCS, sbcs, dmi_wait_cycles);
    while (sbcs.sbbusy);
    // Write PC to Data0 and Data1
    jtag_secd_dbg.write_dmi(dm_ot::Data0, start_addr);
    do jtag_secd_dbg.read_dmi(dm_ot::SBCS, sbcs, dmi_wait_cycles);
    while (sbcs.sbbusy);
    // Halt Req
    jtag_secd_dbg.write_dmi(dm_ot::DMControl, 32'h8000_0001);
    do jtag_secd_dbg.read_dmi(dm_ot::SBCS, sbcs, dmi_wait_cycles);
    while (sbcs.sbbusy);
    // Wait for CVA6 to be halted
    do jtag_secd_dbg.read_dmi(dm_ot::DMStatus, dm_status, dmi_wait_cycles);
    while (!dm_status[8]);
    // Ensure haltreq, resumereq and ackhavereset all equal to 0
    jtag_secd_dbg.write_dmi(dm_ot::DMControl, 32'h0000_0001);
    do jtag_secd_dbg.read_dmi(dm_ot::SBCS, sbcs, dmi_wait_cycles);
    while (sbcs.sbbusy);
    // Register Access Abstract Command
    jtag_secd_dbg.write_dmi(dm_ot::Command, {8'h0,1'b0,3'h2,1'b0,1'b0,1'b1,1'b1,4'h0,dm_ot::CSR_DPC});
    do jtag_secd_dbg.read_dmi(dm_ot::SBCS, sbcs, dmi_wait_cycles);
    while (sbcs.sbbusy);
    // Resume req. Exiting from debug mode Secd CVA6 will jump at the DPC address.
    // Ensure haltreq, resumereq and ackhavereset all equal to 0
    jtag_secd_dbg.write_dmi(dm_ot::DMControl, 32'h4000_0001);
    do jtag_secd_dbg.read_dmi(dm_ot::SBCS, sbcs, dmi_wait_cycles);
    while (sbcs.sbbusy);
    jtag_secd_dbg.write_dmi(dm_ot::DMControl, 32'h0000_0001);
    do jtag_secd_dbg.read_dmi(dm_ot::SBCS, sbcs, dmi_wait_cycles);

    while (sbcs.sbbusy);
    $display("[JTAG SECD] Wait for Completion");
  endtask

  task load_secd_binary;
    input string binary;                   // File name
    logic [31:0] section_addr, section_len;
    byte         buffer[];

    // Read ELF
    void'(read_elf(binary));
    $display("[JTAG SECD] Reading %s", binary);

    while (get_section(section_addr, section_len)) begin
      // Read Sections
      automatic int num_words = (section_len + AxiWideBeWidth_ib - 1)/AxiWideBeWidth_ib;
      $display("[JTAG SECD] Reading section %x with %0d words", section_addr, num_words);

      secd_sections[section_addr >> AxiWideByteOffset_ib] = num_words;
      buffer = new[num_words * AxiWideBeWidth_ib];
      void'(read_section(section_addr, buffer, section_len));
      for (int i = 0; i < num_words; i++) begin
        automatic logic [AxiWideBeWidth_ib-1:0][7:0] word = '0;
        for (int j = 0; j < AxiWideBeWidth_ib; j++) begin
          word[j] = buffer[i * AxiWideBeWidth_ib + j];
        end
        secd_memory[section_addr/AxiWideBeWidth_ib + i] = word;
      end
    end

  endtask // load_secd_binary

  task jtag_secd_wait_eoc;
    automatic dm_ot::sbcs_t sbcs = '{
      sbautoincrement: 1'b1,
      sbreadondata   : 1'b1,
      default        : 1'b0
    };
    logic [31:0] retval;
    logic [31:0] to_host_addr;
    to_host_addr = 32'h c11c0018;

    // Initialize the dm module again, otherwise it will not work
    debug_secd_module_init();
    sbcs.sbreadonaddr = 1;
    sbcs.sbautoincrement = 0;
    jtag_secd_dbg.write_dmi(dm_ot::SBCS, sbcs);
    do jtag_secd_dbg.read_dmi(dm_ot::SBCS, sbcs);
    while (sbcs.sbbusy);

    jtag_secd_dbg.write_dmi(dm_ot::SBAddress0, to_host_addr); // tohost address
    jtag_secd_dbg.wait_idle(10);
    do begin
	     do jtag_secd_dbg.read_dmi(dm_ot::SBCS, sbcs);
	     while (sbcs.sbbusy);
       jtag_secd_dbg.write_dmi(dm_ot::SBAddress0, to_host_addr); // tohost address
	     do jtag_secd_dbg.read_dmi(dm_ot::SBCS, sbcs);
	     while (sbcs.sbbusy);
       jtag_secd_dbg.read_dmi(dm_ot::SBData0, retval);
       $display(retval);
       # 400ns;
    end while (~retval[0]);

    if (retval != 32'h00000001) $error("[JTAG] FAILED: return code %0d", retval);
    else $display("[JTAG] SUCCESS");

    $finish;

  endtask // jtag_read_eoc

  //////////
  // UART //
  //////////

  localparam time UartBaudPeriod = 1000ns*1000*1000/UartBaudRate;

  localparam byte_bt UartDebugCmdRead  = 'h11;
  localparam byte_bt UartDebugCmdWrite = 'h12;
  localparam byte_bt UartDebugCmdExec  = 'h13;
  localparam byte_bt UartDebugAck      = 'h06;
  localparam byte_bt UartDebugEot      = 'h04;
  localparam byte_bt UartDebugEoc      = 'h14;

  byte_bt uart_boot_byte;
  logic   uart_boot_ena;
  logic   uart_boot_eoc;

  initial begin
    uart_rx       = 1;
    uart_boot_eoc = 0;
    uart_boot_ena = 0;
  end

  task automatic uart_read_byte(output byte_bt bite);
    // Start bit
    @(negedge uart_tx);
    #(UartBaudPeriod/2);
    // 8-bit byte
    for (int i = 0; i < 8; i++) begin
      #UartBaudPeriod bite[i] = uart_tx;
    end
    // Parity bit
    if(UartParityEna) begin
      bit parity;
      #UartBaudPeriod parity = uart_tx;
      if(parity ^ (^bite))
        $error("[UART] - Parity error detected!");
    end
    // Stop bit
    #UartBaudPeriod;
  endtask

  task automatic uart_write_byte(input byte_bt bite);
    // Start bit
    uart_rx = 1'b0;
    // 8-bit byte
    for (int i = 0; i < 8; i++)
      #UartBaudPeriod uart_rx = bite[i];
    // Parity bit
    if (UartParityEna)
      #UartBaudPeriod uart_rx = (^bite);
    // Stop bit
    #UartBaudPeriod uart_rx = 1'b1;
    #UartBaudPeriod;
  endtask

  task automatic uart_boot_scoop(output byte_bt bite);
    // Assert our intention to scoop the next received byte
    uart_boot_ena = 1;
    // Wait until read task notifies us a scooped byte is available
    @(negedge uart_boot_ena);
    // Grab scooped byte
    bite = uart_boot_byte;
  endtask

  task automatic uart_boot_scoop_expect(input string name, input byte_bt exp);
    byte_bt bite;
    uart_boot_scoop(bite);
    if (bite != exp)
      $fatal(1, "[UART] Expected %s (%0x) after read command, received %0x", name, exp, bite);
  endtask

  // Continually read characters and print lines
  // TODO: we should be able to support CR properly, but buffers are hard to deal with...
  initial begin
    static byte_bt uart_read_buf [$];
    byte_bt bite;
    wait_for_reset();
    forever begin
      uart_read_byte(bite);
      if (uart_boot_ena) begin
        uart_boot_byte  = bite;
        uart_boot_ena = 0;
      end else if (bite == "\n") begin
        $display("[UART] %s", {>>8{uart_read_buf}});
        uart_read_buf.delete();
      end else if (bite == UartDebugEoc) begin
        uart_boot_eoc = 1;
      end else begin
        uart_read_buf.push_back(bite);
      end
    end
  end

  // A length of zero indcates a write (write lengths are inferred from their queue)
  task automatic uart_debug_rw(doub_bt addr, doub_bt len_or_w, ref byte_bt data [$]);
    byte_bt bite;
    doub_bt len = len_or_w ? len_or_w : data.size();
    // Send command, address, and length
    uart_write_byte(len_or_w ? UartDebugCmdRead : UartDebugCmdWrite);
    for (int i = 0; i < 8; ++i)
      uart_write_byte(addr[8*i +: 8]);
        for (int i = 0; i < 8; ++i)
      uart_write_byte(len[8*i +: 8]);
    // Receive and check ACK
    uart_boot_scoop_expect("ACK", UartDebugAck);
    // Send or receive requested data
    for (int i = 0; i < len; ++i) begin
      if (len_or_w) begin
        uart_boot_scoop(bite);
        data.push_back(bite);
      end else begin
        uart_write_byte(data[i]);
      end
    end
    // Receive and check EOT
    uart_boot_scoop_expect("EOT", UartDebugEot);
  endtask

  // Load a binary
  task automatic uart_debug_elf_preload(input string binary, output doub_bt entry);
    longint sec_addr, sec_len;
    $display("[UART] Preloading ELF binary: %s", binary);
    if (read_elf(binary))
      $fatal(1, "[UART] Failed to load ELF!");
    while (get_section(sec_addr, sec_len)) begin
      byte bf[] = new [sec_len];
      $display("[UART] Preloading section at 0x%h (%0d bytes)", sec_addr, sec_len);
      if (read_section(sec_addr, bf, sec_len)) $fatal(1, "[UART] Failed to read ELF section!");
      // Write section in blocks
      for (longint i = 0; i <= sec_len ; i += UartBurstBytes) begin
        byte_bt bytes [$];
        if (i != 0)
          $display("[UART] - %0d/%0d bytes (%0d%%)", i, sec_len, i*100/(sec_len>1 ? sec_len-1 : 1));
        for (int b = 0; b < UartBurstBytes; b++) begin
          if (i+b >= sec_len) break;
          bytes.push_back(bf [i+b]);
        end
        uart_debug_rw(sec_addr + i, 0, bytes);
      end
    end
    void'(get_entry(entry));
    $display("[UART] Preload complete");
  endtask

  task automatic uart_debug_elf_run_and_wait(input string binary, output word_bt exit_code);
    byte_bt bite;
    doub_bt entry;
    // Wait some time for boot ROM to settle (No way to query this using only UART)
    $display("[UART] Waiting for debug loop to start");
    #(UartWaitCycles*UartBaudPeriod);
    // We send an ACK challenge to the debug server and wait for an ACK response
    $display("[UART] Sending ACK chellenge");
    uart_write_byte(UartDebugAck);
    uart_boot_scoop_expect("ACK", UartDebugAck);
    // Preload
    uart_debug_elf_preload(binary, entry);
  $display("[UART] Sending EXEC command for address %0x", entry);
    // Send exec command and receive ACK
    uart_write_byte(UartDebugCmdExec);
    for (int i = 0; i < 8; ++i)
      uart_write_byte(entry[8*i +: 8]);
    uart_boot_scoop_expect("ACK", UartDebugAck);
    // Wait for EOC and read return code
    wait (uart_boot_eoc == 1);
    $display("[UART] Received EOC signal");
    uart_boot_eoc = 0;
    for (int i = 0; i < 4; ++i)
      uart_boot_scoop(exit_code[8*i +: 8]);
    // Report exit code
    if (exit_code) $error("[UART] FAILED: return code %0d", exit_code);
    else $display("[UART] SUCCESS");
  endtask
 
endmodule
