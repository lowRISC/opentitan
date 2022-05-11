// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Behavioral model of SPI Flash

program spiflash #(
  parameter int unsigned FlashSize = 1024*1024, // 1MB
  parameter int unsigned PageSize = 256, // Bytes

  parameter bit EnFastSim = 1'b 1, // Reduce the latencies

  // Timing information               s_ ms_ us
  // Program Latency
  parameter int unsigned tPPTyp   =       1_000, // us
  parameter int unsigned tPPMax   =       3_000, // us
  // Sector Erase(4kB) Latency
  parameter int unsigned tSETyp   =      45_000, // us
  parameter int unsigned tSEMax   =     200_000, // us
  // Block Erase 32kB Latency
  parameter int unsigned tBE32Typ =     200_000, // us
  parameter int unsigned tBE32Max =   1_000_000, // us
  // Block Erase 64kB Latency
  parameter int unsigned tBE64Typ =     400_000, // us
  parameter int unsigned tBE64Max =   2_000_000, // us
  // Chip Erase Latency
  parameter int unsigned tCETyp   = 200_000_000, // us
  parameter int unsigned tCEMax   = 320_000_000, // us

  // Num of Repeating Continuous Code ('h7F)
  parameter int unsigned CcNum    = 7,
  parameter logic [7:0]  JedecId  = 8'h 1F,
  parameter logic [15:0] DeviceId = 16'h 1234,

  // Command Support
  parameter bit EnFastReadDual = 1'b 1,
  parameter bit EnFastReadQuad = 1'b 1,

  // Dummy Cycle
  parameter int unsigned DummySizeNormal = 8,
  parameter int unsigned DummySizeDual   = 4,
  parameter int unsigned DummySizeQuad   = 2
) (
  input logic sck,
  input logic csb,
  inout [3:0] sd
  // TODO: Add WP
);

  // Local parameter : affected by EnFastSim

  // Timing information               s_ ms_ us
  localparam int unsigned tPPDiv   = (EnFastSim) ?      1_000 : 1 ;
  localparam int unsigned tSEDiv   = (EnFastSim) ?      5_000 : 1 ;
  localparam int unsigned tBE32Div = (EnFastSim) ?     10_000 : 1 ;
  localparam int unsigned tBE64Div = (EnFastSim) ?    100_000 : 1 ;
  localparam int unsigned tCEDiv   = (EnFastSim) ? 10_000_000 : 1 ;
  // Program Latency
  localparam int unsigned LocalPPTyp   = tPPTyp   / tPPDiv; // us
  localparam int unsigned LocalPPMax   = tPPMax   / tPPDiv; // us
  // Sector Erase(4kB) Latency
  localparam int unsigned LocalSETyp   = tSETyp   / tSEDiv; // us
  localparam int unsigned LocalSEMax   = tSEMax   / tSEDiv; // us
  // Block Erase 32kB Latency
  localparam int unsigned LocalBE32Typ = tBE32Typ / tBE32Div; // us
  localparam int unsigned LocalBE32Max = tBE32Max / tBE32Div; // us
  // Block Erase 64kB Latency
  localparam int unsigned LocalBE64Typ = tBE64Typ / tBE64Div; // us
  localparam int unsigned LocalBE64Max = tBE64Max / tBE64Div; // us
  // Chip Erase Latency
  localparam int unsigned LocalCETyp   = tCETyp   / tCEDiv; // us
  localparam int unsigned LocalCEMax   = tCEMax   / tCEDiv; // us


  typedef enum int unsigned {
    Addr3B,
    Addr4B,
    AddrCfg
  } addr_mode_e;

  // Return Output mode
  typedef enum int unsigned {
    IoSingle = 1,
    IoDual   = 2,
    IoQuad   = 4
  } io_mode_e;

  typedef logic [7:0] spiflash_byte_t;

  localparam spiflash_byte_t Cc = 8'h 7F;

  localparam int unsigned StorageAw = $clog2(FlashSize);

  // Status Bit Location
  typedef enum int unsigned {
    StatusBUSY = 0,
    StatusWEL  = 1,
    StatusBP0  = 2,
    StatusBP1  = 3,
    StatusBP2  = 4,
    StatusBP3  = 5,
    StatusQE   = 6, // Quad Enable
    StatusSRWD = 7  // Status Register Write Protect
  } status_bit_e;

  // spiflash_addr_t is the smallest address width to represent FlashSize bytes
  typedef logic [StorageAw-1:0] spiflash_addr_t;

  logic [3:0] sd_out, sd_en;

  assign sd[0] = sd_en[0] ? sd_out[0] : 1'b z;
  assign sd[1] = sd_en[1] ? sd_out[1] : 1'b z;
  assign sd[2] = sd_en[2] ? sd_out[2] : 1'b z;
  assign sd[3] = sd_en[3] ? sd_out[3] : 1'b z;

  // SPI Flash internal state variables
  addr_mode_e     addr_mode;
  spiflash_byte_t [2:0] status; // 24 bit
  spiflash_byte_t storage[spiflash_addr_t]; // Associative Array to store data

  spiflash_byte_t page_buffer[PageSize]; // page buffer to be used
  int unsigned    page_buffer_size;

  spiflash_byte_t sfdp[256]; // SFDP storage 256Byte

  mailbox backend_process; // Start delayed process (after CSb release)
  mailbox backend_data; // Deliver the address to the backend task

  initial begin
    print_banner();

    // Init values
    status = '0;

    backend_process = new(1); // Only one process at a time but multiple data
    backend_data = new(1);

    // SFDP initialization
    // FIXME: Appropriate SFDP table rather than random data
    foreach(sfdp[i]) sfdp[i] = $urandom_range(255, 0);
    // Should wait ??
    fork
      main();
      backend();
    join
  end

  function automatic void print_banner();
    $display("/////////////////////");
    $display("// SPI Flash Model //");
    $display("/////////////////////");

    // Print current config
    $display("");
    $display("Configurations:");
    $display("  JEDEC ID:  ID(0x%2X) CC_NUM (%2d)", JedecId, CcNum);
    $display("  Capacity:  %s", print_capacity(FlashSize));
    $display("  Fast Read: %s/ Dummy Cycle (%1d)",
      "Enabled", DummySizeNormal);
    $display("  Dual Mode:%s/ Dummy Cycle (%1d)",
      (EnFastReadDual) ? "Enabled" : "Disabled", DummySizeDual);
    $display("  Quad Mode:%s/ Dummy Cycle (%1d)",
      (EnFastReadQuad) ? "Enabled" : "Disabled", DummySizeQuad);
  endfunction : print_banner

  function automatic string print_capacity(int unsigned size);
    string str;
    // Get the highest unit (GB, MB, kB)
    automatic int unsigned quotient;
    automatic int unsigned order; // 0: B, 1: kB, 2: MB, 3: GB
    automatic string unit;
    quotient = size;
    forever begin
      if (quotient < 1024) break;
      quotient = quotient / 1024;
      order = order + 1;
    end

    case (order)
      0: unit = "B";
      1: unit = "kB";
      2: unit = "MB";
      3: unit = "GB";
      4: unit = "TB";
      default: unit = "Unsupported";
    endcase

    str = $sformatf("%0d%s", quotient, unit);
    return str;
  endfunction : print_capacity

  static task main();
    // Main function
    forever begin
      automatic spiflash_byte_t opcode;
      automatic bit             early_termination;
      automatic int unsigned    excessive_sck = 0;
      // Indication of process needed after CSb release
      automatic bit             process_after_csb = 1'b 0;
      // Big loop. Wait transaction
      sd_en = 4'h 0; // Off the output by default
      wait(csb == 1'b 0);
      early_termination = 1'b 0;
      fork
        begin
          // If cmd process comes first, this forked process won't set
          // early_termination bit
          @(posedge csb);
          early_termination = 1'b 1;
        end
        begin
          // Main
          cmdparse(opcode); // Store incoming into opcod
          process_cmd(opcode, process_after_csb);

          // Count remaining edges of SCK. opcode completed command should
          // have no additional data, or should be discarded
          sd_en = 4'h 0;
          forever begin
            @(posedge sck);
            excessive_sck++;
          end
        end
      join_any
      // Float the line
      sd_en = 4'h 0;

      // Determine early termination, if not early terminated, the main block
      // waits CSb de-assertion too
      // For many Output commands, the logic sends data until host releases
      // CSb. In this case, early_termination is set too. If the command is
      // output command, do not process early_termination.

      // Kill the forked process
      disable fork;

      // Process program, etc
      // If excessive sck, then discard.
      if (process_after_csb) begin
        if (backend_process.num() != 0) begin
          $display("T+%0d] SPIFlash: Can't handle two backend commands", $time);
          $display("       Discarding the latter %2Xh", opcode);
          continue;
        end
        backend_process.put(opcode);
      end
    end
  endtask : main

  static task backend();
    forever begin
      automatic spiflash_byte_t opcode;
      backend_process.get(opcode);

      case (opcode)
        spi_device_pkg::CmdPageProgram: begin
          backend_page_program();
        end
      endcase
    end
  endtask : backend

  task automatic cmdparse(
    output spiflash_byte_t opcode
  );
    automatic spiflash_byte_t spi_byte = 0;
    get_byte(IoSingle, spi_byte);
    $display("SPIFlash: Command(%2Xh) received", spi_byte);
    opcode = spi_byte;
  endtask : cmdparse

  task automatic process_cmd(
    input spiflash_byte_t opcode,
    output bit en_backend
  );
    // Main case block to call subtasks depending on the opcode
    en_backend = 1'b 0;
    case (opcode)
      spi_device_pkg::CmdReadStatus1: begin
        // Return status data
        return_status(0); // 0-2
      end

      spi_device_pkg::CmdJedecId: begin
        return_jedec();
      end

      spi_device_pkg::CmdReadSfdp: begin
        return_sfdp();
      end

      spi_device_pkg::CmdReadData, spi_device_pkg::CmdReadFast,
      spi_device_pkg::CmdReadDual, spi_device_pkg::CmdReadQuad: begin
        read(opcode);
      end

      spi_device_pkg::CmdEn4B, spi_device_pkg::CmdEx4B: begin
        addr_4b(opcode);
      end

      spi_device_pkg::CmdWriteEnable, spi_device_pkg::CmdWriteDisable: begin
        wel(opcode);
      end

      spi_device_pkg::CmdPageProgram: begin
        page_program(opcode);
        en_backend = 1'b 1;
      end

      // TODO: SectorErase
      // TODO: BlockErase32
      // TODO: BlockErase64
      default: begin
        $display("Unrecognized Opcode (%2Xh) received", opcode);
      end
    endcase

  endtask : process_cmd

  task automatic process_cmd_after_csb(

  );
  endtask : process_cmd_after_csb

  task automatic get_byte(
    input  io_mode_e       io_mode,
    output spiflash_byte_t data
  );
    // Receive a byte on SPI
    // Expected to be called @(negedge sck);
    automatic spiflash_byte_t spi_byte = 0;
    // Receive first 8 beats and decoding the byte, call subsequence tasks.
    repeat(8/io_mode) begin
      @(posedge sck);
      case (io_mode)
        IoSingle: spi_byte = {spi_byte[6:0], sd[  0]};
        IoDual:   spi_byte = {spi_byte[5:0], sd[1:0]};
        IoQuad:   spi_byte = {spi_byte[3:0], sd[3:0]};
        default:  spi_byte = {spi_byte[6:0], sd[  0]};
      endcase
    end
    @(negedge sck); // Wait the data line fully completed
    data = spi_byte;
  endtask : get_byte

  task automatic get_address(
    input  io_mode_e    imode,
    input  addr_mode_e  amode,
    output logic [31:0] addr
  );
    automatic spiflash_byte_t spi_byte;
    automatic addr_mode_e mode;
    case (amode)
      AddrCfg: mode = addr_mode;
      Addr3B, Addr4B: mode = amode;
      default: mode = Addr3B;
    endcase

    if (mode == Addr4B) begin
      // Get upper byte
      get_byte(imode, spi_byte);
      addr[31:24] = spi_byte;
    end else begin
      addr[31:24] = 8'h 0;
    end

    for(int i = 2 ; i >= 0 ; i--) begin
      get_byte(imode, spi_byte);
      addr[8*i+:8] = spi_byte;
    end

  endtask : get_address

  task automatic return_byte(spiflash_byte_t data, io_mode_e io_mode);
    // Assume the task is called at @(negedge sck);
    automatic int unsigned rails;
    automatic logic [7:0]  lines;
    case (io_mode)
      IoSingle: begin
        rails = 1;
        sd_en = 4'b 0010;
      end
      IoDual: begin
        rails = 2;
        sd_en = 4'b 0011;
      end
      IoQuad: begin
        rails = 4;
        sd_en = 4'b 1111;
      end
      default: begin
        rails = 1;
        sd_en = 4'b 0010;
      end
    endcase

    lines = data;
    repeat(8/rails) begin
      case (io_mode)
        IoSingle: begin
          sd_out[1] = lines[7];
          lines = {lines[6:0], 1'b 0};
        end
        IoDual: begin
          sd_out[1:0] = lines[7:6];
          lines = {lines[5:0], 2'b 00};
        end
        IoQuad: begin
          sd_out[3:0] = lines[7:4];
          lines = {lines[3:0], 4'b 0000};
        end
        default: begin
          sd_out[1] = lines[7];
          lines = {lines[6:0], 1'b 0};
        end
      endcase
      @(negedge sck);
    end
  endtask : return_byte

  task automatic dummy(int unsigned cycle);
    // Assume the task is called @(negedge sck);
    sd_en = 4'b 0000;
    repeat (cycle) @(negedge sck);
  endtask : dummy

  task automatic return_status(int unsigned idx);
    // Starting from the index and wraps %3 until host releases CSb
    automatic int unsigned s_idx = idx;

    // Copy the status into internal variable to not be corrupted by on-going
    // backend tasks.
    automatic spiflash_byte_t [2:0] committed_status = status;
    forever begin
      return_byte(committed_status[s_idx], IoSingle);
      s_idx = (s_idx + 1)%3;
    end
  endtask : return_status

  task automatic return_jedec();
    // Repeat CcNum then JedecId and DeviceId(MSB to LSB)
    repeat (CcNum) begin
      return_byte(Cc, IoSingle);
    end
    return_byte(JedecId, IoSingle);
    return_byte(DeviceId[ 7:0], IoSingle);
    return_byte(DeviceId[15:8], IoSingle);
    // Float
  endtask : return_jedec

  task automatic return_sfdp();
    automatic logic [31:0] address;
    // Get address field
    get_address(IoSingle, Addr3B, address);
    $display("%d] SPIFlash: SFDP Address %6Xh", $time, address);

    // dummy byte
    dummy(8); // 8 cycle dummy

    // fetch data and return
    forever begin
      return_byte(sfdp[address++], IoSingle);
    end
  endtask : return_sfdp

  task automatic read(
    input spiflash_byte_t opcode
  );
    // Return Read data
    automatic logic [31:0]    address;
    automatic spiflash_addr_t spi_addr;
    automatic io_mode_e       io_mode     = IoSingle;
    automatic int unsigned    dummy_cycle = 0;

    // get address field
    get_address(IoSingle, AddrCfg, address);
    $display("T:%0d] SPIFlash: Read Address %8Xh", $time, address);
    assert(address[31:StorageAw] == '0)
      else $display("Out-of-Bound Address received");

    // Dummy cycle?
    case (opcode)
      spi_device_pkg::CmdReadData: begin
        io_mode     = IoSingle;
        dummy_cycle = 0;
      end

      spi_device_pkg::CmdReadFast: begin
        io_mode     = IoSingle;
        dummy_cycle = DummySizeNormal;
      end

      spi_device_pkg::CmdReadDual: begin
        io_mode     = IoDual;
        dummy_cycle = DummySizeDual;
      end

      spi_device_pkg::CmdReadQuad: begin
        io_mode     = IoQuad;
        dummy_cycle = DummySizeQuad;
      end
    endcase

    if (dummy_cycle != 0) dummy(dummy_cycle);

    // fetch from storage and return
    while (address <= FlashSize) begin
      // Check if exists, if not fill with random data
      if (!storage.exists(address)) storage[address] = $urandom_range(255,0);
      return_byte(storage[address++], io_mode);
    end
  endtask : read

  task automatic addr_4b(spiflash_byte_t opcode);
    // Set / clear addr_mode
    case (opcode)
      spi_device_pkg::CmdEn4B: addr_mode = Addr4B;
      spi_device_pkg::CmdEx4B: addr_mode = Addr3B;
      default: $display("addr_4b: Unrecognized Cmd (%2Xh)", opcode);
    endcase
  endtask : addr_4b

  task automatic wel(spiflash_byte_t opcode);
    // TODO: Set only when CSb is deasserted right after 8th beat
    case (opcode)
      spi_device_pkg::CmdWriteEnable:  status[0][StatusWEL] = 1'b 1;
      spi_device_pkg::CmdWriteDisable: status[0][StatusWEL] = 1'b 0;
      default: $display("WEL: Unrecognized Cmd (%2Xh)", opcode);
    endcase
  endtask : wel

  task automatic page_program(spiflash_byte_t opcode);
    // Return Read data
    automatic logic [31:0]    address;
    automatic logic [7:0]     buffer_idx;

    // Set BUSY
    status[0][StatusBUSY] = 1'b 1;

    // get address field
    get_address(IoSingle, AddrCfg, address);
    $display("T:%0d] SPIFlash: Program Address %8Xh", $time, address);
    if (address[31:StorageAw] != '0) begin
      $display("Out-of-Bound Address received");
      $display("Discarding the contents");
      return;
    end

    backend_data.put({opcode, address});

    // Starting with buffer offset and wraps 256B always
    buffer_idx = address[7:0];
    page_buffer_size = 0;

    // Stack bytes
    forever begin
      automatic spiflash_byte_t data;
      get_byte(IoSingle, data);
      page_buffer[buffer_idx % PageSize] = data;

      buffer_idx = (buffer_idx + 1 ) % PageSize;

      if (page_buffer_size != PageSize) page_buffer_size++;
    end

  endtask : page_program

  task automatic backend_page_program();
    automatic spiflash_addr_t spi_addr;
    automatic spiflash_byte_t opcode;
    automatic logic [39:0] mbx_data;
    automatic logic [31:0] host_address;
    automatic logic [7:0]  buffer_offset;

    if (backend_data.num() == 0) begin
      // The transaction got cancelled before receiving the address.
      // Skip the backend task
      status[0][StatusBUSY] = 1'b 0;
      return;
    end
    // Fetch address from mailbox
    backend_data.get(mbx_data);
    opcode = mbx_data[39:32];
    host_address = mbx_data[31:0];

    // if opcode is not PageProgram, somehow mailbox corrupted. Report error and put it back to mailbox
    if (opcode != spi_device_pkg::CmdPageProgram) begin
      $display("SPIFlash: Opcode is not PageProgram, putting the data back to backend_data");
      backend_data.put({opcode, host_address});
      return;
    end

    // Write data into storage
    buffer_offset = host_address[7:0];
    repeat (page_buffer_size) begin
      storage[{host_address[31:8], buffer_offset%PageSize}] = page_buffer[buffer_offset%256];
      buffer_offset = (buffer_offset+1) % PageSize;
    end

    // Determines delay
    // Didn't use $dist_normal() as Typ is most likely lower bound.
    // Maybe Poisson Distribution is appropriate?
    #($urandom_range(LocalPPTyp*1.1, LocalPPTyp*0.9) * 1us)

    // At the end, clear BUSY
    status[0][StatusBUSY] = 1'b 0;
  endtask : backend_page_program

  initial begin
    assert(PageSize == 256)
      else begin
        $display("SPIFlash currently supports 256B Page only");
        $finish();
      end
  end

endprogram : spiflash
