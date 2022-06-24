// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Serial Peripheral Interface (SPI) Device module.
//

package spi_device_pkg;

  // Passthrough Inter-module signals
  typedef struct packed {
    // passthrough_en: switch the mux for downstream SPI pad to host system not
    // the internal SPI_HOST IP
    logic       passthrough_en;

    // Passthrough includes SCK also. The sck_en is pad out enable not CG
    // enable. The CG is placed in SPI_DEVICE IP.
    logic       sck;
    logic       sck_en;

    // CSb should be pull-up pad. In passthrough mode, CSb is directly connected
    // to the host systems CSb except when SPI_DEVICE decides to drop the
    // command.
    logic       csb;
    logic       csb_en;

    // SPI data from host system to downstream flash device.
    logic [3:0] s;
    logic [3:0] s_en;
  } passthrough_req_t;

  typedef struct packed {
    // SPI data from downstream flash device to host system.
    logic [3:0] s;
  } passthrough_rsp_t;

  parameter passthrough_req_t PASSTHROUGH_REQ_DEFAULT = '{
    passthrough_en: 1'b 0,
    sck:            1'b 0,
    sck_en:         1'b 0,
    csb:            1'b 1,
    csb_en:         1'b 0,
    s:              4'h 0,
    s_en:           4'h 0
  };

  parameter passthrough_rsp_t PASSTHROUGH_RSP_DEFAULT = '{
    s: 4'h 0
  };

  // Command Type
  //
  // Passthrough module does not strictly follow every bit on the SPI line but
  // loosely tracks the phase of the commands.
  //
  // The command in SPI Flash can be categorized as follow:
  //
  // - {Address, PayloadOut}:        examples are ReadData
  // - {Address, Dummy, PayloadOut}: FastRead / Dual/ Quad commands have dummy
  // - {Dummy, PayloadOut}:          Release Power-down / Manufacturer ID
  // - {PayloadOut}:                 Right after opcode, the device sends data
  //                                 to host
  // - {Address, PayloadIn}:         Host sends address and payload back-to-back
  // - {PayloadIn}:                  Host sends payload without any address hint
  // - None:                         The commands complete without any address /
  //                                 payload(in/out)
  //
  // If a received command has more than one state, the counter value will be
  // set to help the state machine to move to the next state with the exact
  // timing.
  //
  // A `cmd_type_t` struct has information for a command. The actual value for
  // commands are compile-time parameters. When the logic receives 8 bits of
  // opcode, it latches the parameter into this struct and references this
  // through the transaction.

  // Address or anything host driving after opcode counter
  localparam int unsigned MaxAddrBit = 32;
  localparam int unsigned AddrCntW = $clog2(MaxAddrBit);

  // Dummy

  localparam int unsigned MaxDummyBit = 8;
  localparam int unsigned DummyCntW = $clog2(MaxDummyBit);

  // TPM
  localparam int unsigned AccessRegSize    = 8; // times Locality
  localparam int unsigned IntEnRegSize     = 32;
  localparam int unsigned IntVectorRegSize = 8;
  localparam int unsigned IntStsRegSize    = 32;
  localparam int unsigned IntfCapRegSize   = 32;
  localparam int unsigned StatusRegSize    = 32;
  localparam int unsigned IdRegSize        = 32; // {DID; VID}
  localparam int unsigned RidRegSize       = 8;
  localparam int unsigned ActiveLocalityBitPos = 5; // Access[5

  typedef enum logic {
    PayloadIn  = 1'b 0,
    PayloadOut = 1'b 1
  } payload_dir_e;

  // addr_mode_e: CMD_INFO.addr_mode informs HW if a command has address field,
  // CFG.addr_4b_en affected, or address is 3B/4B.
  typedef enum logic [1:0] {
    AddrDisabled = 2'b 00,
    AddrCfg      = 2'b 01,
    Addr3B       = 2'b 10,
    Addr4B       = 2'b 11
  } addr_mode_e;

  // cmd_info_t defines the command relevant information. SPI Device IP has
  // #NumCmdInfo cmd registers (default 16). A few of them are assigned to a
  // specific commands such as Read Status, Read SFDP.
  //
  // These fields are SW programmable via CSR interface.
  typedef struct packed {
    // If 1, the cmd_info slot is in active and contains valid config.
    logic valid;

    // opcode: Each cmd_info type has 8bit opcode. SPI_DEVICE has 16 command
    // slots. The logic compares the opcode and uses the command info when
    // opcode is matched. If same opcode exists, SPI_DEVICE uses the command
    // info slot having the lowest index among the matched ones.
    logic [7:0] opcode;

    // Look at addr_mode_e description for details
    // - 00: Address disabled
    // - 01: Address is affected by CFG
    // - 10: Address is 3 bytes field
    // - 11: Address is 4 bytes field
    addr_mode_e addr_mode;

    // swap_en is used in the passthrough logic. If this field is set to 1, the
    // address in the passthrough command is replaced to the preconfigured
    // value.
    logic addr_swap_en;

    // Mbyte field exist. If set to 1, the command waits 1 byte before moving
    // to dummy field. This field data is ignored.
    logic mbyte_en;

    // set to 1 if the command has a dummy cycle following the address field.
    logic                 dummy_en;
    logic [DummyCntW-1:0] dummy_size;

    // set to non-zero if the command has payload at the end of the protocol. If
    // dummy_en is 1, then the payload follows the dummy cycle. payload_en has
    // four bits. Each bit represents the SPI line. If a command is single IO
    // command and returns data to the host system, the data is returned on the
    // MISO line (IO[1]). In this case, SW sets payload_en to 4'b0010 and
    // payload_dir to PayloadOut.
    logic [3:0]   payload_en;
    payload_dir_e payload_dir;

    // If payload_swap_en is set, the passthrough logic swaps the first
    // 4 bytes of the write payload with PAYLOAD_SWAP_MASK and
    // PAYLOAD_SWAP_DATA CSR.
    //
    // `payload_swap_en` only works with write data and SingleIO mode.
    // `payload_en` should be 4'b 0001 && `payload_dir` to be PayloadIn.
    logic payload_swap_en;

    // upload: If upload field in the command info entry is set, the cmdparse
    // activates the upload submodule when the opcode is received. `addr_en`,
    // `addr_4B_affected`, and `addr_4b_forced` (TBD) affect the upload
    // functionality. The three address related configs defines the command
    // address field size.

    // The logic assumes the following SPI input stream as payload, which max
    // size is 256B. If the command exceeds the maximum payload size 256B, the
    // logic wraps the payload and overwrites.
    logic upload;

    // busy: Set to 1 to set the BUSY bit in the FLASH_STATUS when the command
    // is received.  This bit is active only when `upload` bit is set.
    logic busy;

  } cmd_info_t;

  // CmdInfoInput parameter is the default value if no opcode in the cmd info
  // slot is matched to the received command opcode.
  parameter cmd_info_t CmdInfoInput = '{
    valid:            1'b 0,
    opcode:           8'h 00,
    addr_mode:        AddrDisabled,
    addr_swap_en:     1'b 0,
    mbyte_en:         1'b 0,
    dummy_en:         1'b 0,
    dummy_size:       3'h 0,
    payload_en:       4'b 0001, // MOSI active
    payload_dir:      PayloadIn,
    payload_swap_en:  1'b 0,
    upload:           1'b 0,
    busy:             1'b 0
  };

  function automatic logic is_cmdinfo_addr_4b(cmd_info_t ci, logic addr_4b_en);
    logic result;
    result = ci.addr_mode == AddrCfg ? addr_4b_en : (ci.addr_mode == Addr4B);
    return result;
  endfunction : is_cmdinfo_addr_4b

  // get_addr_mode removes AddrCfg.
  // It returns {AddrDisabled, Addr3B, Addr4B}
  function automatic addr_mode_e get_addr_mode(cmd_info_t ci, logic addr_4b_en);
    addr_mode_e result;
    result = (ci.addr_mode != AddrCfg) ? ci.addr_mode
           : (addr_4b_en) ? Addr4B : Addr3B ;
    return result;
  endfunction : get_addr_mode

  // SPI_DEVICE HWIP has 16 command info slots. A few of them are pre-assigned.
  // (defined in the spi_device_pkg)
  //
  //parameter int unsigned NumCmdInfo = 16;

  // cmd_info_index_e assigns some cmd_info slots to specific commands. The
  // reason why command slots cannot be fully flexible (unlike NumCmdInfo-way $)
  // is that the slots are used in the Flash mode also. The Read Status/ SFDP/
  // etc submodules only see the pre-assigned slot and use it.
  typedef enum int unsigned {
    // Read Status subblock in Flash mode only uses opcode of cmd_info
    CmdInfoReadStatus1 = 0,
    CmdInfoReadStatus2 = 1,
    CmdInfoReadStatus3 = 2,

    CmdInfoReadJedecId = 3,

    CmdInfoReadSfdp = 4,

    // 6 slots are assigned to Read commands in Flash mode.
    //
    // Read Data / Fast Read / Fast Read Dual / Fast Read Quad
    // Fast Read Dual IO / Fast Read Quad IO (IO commands are TBD)
    CmdInfoReadCmdStart = 5,
    CmdInfoReadCmdEnd   = 10,

    // other slots are used in the Passthrough and/or upload submodules. These
    // free slots may be used for the commands that are not processed in the
    // flash mode.  Examples are "Release Power-down / ID",
    // "Manufacture/Device ID", etc.  They are not always Input mode. Some has
    // a dummy cycle followed by the output field.
    CmdInfoReserveStart = 11,
    CmdInfoReserveEnd   = spi_device_reg_pkg::NumCmdInfo - 1,
    CmdInfoEn4B         = CmdInfoReserveEnd + 1,
    CmdInfoEx4B         = CmdInfoEn4B + 1,
    CmdInfoWrEn         = CmdInfoEx4B + 1,
    CmdInfoWrDi         = CmdInfoWrEn + 1,
    NumTotalCmdInfo
  } cmd_info_index_e;

  parameter int unsigned NumReadCmdInfo = CmdInfoReadCmdEnd - CmdInfoReadCmdStart + 1;

  // NumCmdInfo adds two more entries (EN4B/ EX4B)
  // or, add NumTotalCmdInfo inside cmd_info_index_e and use?
  //parameter int unsigned NumFixedCmdInfo = 2;
  //parameter int unsigned NumTotalCmdInfo = NumFixedCmdInfo
  //                                       + spi_device_reg_pkg::NumCmdInfo;

  parameter int unsigned CmdInfoIdxW = $clog2(NumTotalCmdInfo);

  // Jedec Configuration Structure
  typedef struct packed {
    logic [7:0]  num_cc;    // continuation code repeat
    logic [7:0]  cc;        // the value of CC (default 7Fh)
    logic [7:0]  jedec_id;  // JEDEC Manufacturer ID
    logic [15:0] device_id; // Device ID
  } jedec_cfg_t ;

  // SPI Operation mode
  typedef enum logic [1:0] {
    FwMode      = 'h0,
    FlashMode   = 'h1,
    PassThrough = 'h2
  } spi_mode_e;

  // SPI IO mode
  typedef enum logic [1:0] {
    SingleIO = 2'h 0,
    DualIO   = 2'h 1,
    QuadIO   = 2'h 2
  } io_mode_e;

  typedef enum int unsigned {
    IoModeFw       = 0,
    IoModeCmdParse = 1,
    IoModeReadCmd  = 2,
    IoModeStatus   = 3,
    IoModeJedec    = 4,
    IoModeUpload   = 5,
    IoModeEnd      = 6 // Indicate of Length
  } sub_io_mode_e;

  // SPI Line Mode (Mode0 <-> Mode3)
  // This HWIP does not support Mode1 and Mode2
  typedef enum logic {
    // Mode0: CPOL=0, CPHA=0
    //  Data sampled on rising edge and shifted on falling edge
    LineMode0 = 1'b 0,
    // Mode3: CPOL=1, CPHA=1
    //  Data sampled on falling edge and shifted on rising edge
    LineMode3 = 1'b 1
  } line_mode_e;

  // SPI Read mode. QUAD uses additional two pins to read
  // Bit 0: Single, Bit 1: Dual Bit 2: Quad
  typedef logic [2:0] spi_rdmode_t;

  typedef logic [7:0] spi_byte_t;

  // eSPI utilizes Alert# signal (from device to host)
  typedef enum logic [1:0] {
    Spi    = 2'h0,
    Espi   = 2'h1,
    Tpm    = 2'h2
  } spi_type_e;

  typedef enum logic [1:0] {
    AddrByte = 2'h0,  // 1 byte for address
    AddrWord = 2'h1,  // 2 bytes for address
    AddrFull = 2'h2   // 3 bytes for address
  } spi_addr_size_e;

  localparam int MEM_AW = 12; // Memory Address width (Byte based)

  typedef enum logic [9:0] {
    DpNone       = 'b 0000000000,
    DpReadCmd    = 'b 0000000001,
    DpReadStatus = 'b 0000000010,
    DpReadSFDP   = 'b 0000000100,
    DpReadJEDEC  = 'b 0000001000,

    // Command + Address only: e.g Block Erase
    // Command + Address + Paylod: Program
    // Command followed by direct payload
    // Write Status could be an example
    // Command only: Write Protect Enable / Chip Erase
    DpUpload     = 'b 0000010000,

    DpEn4B       = 'b 0000100000,
    DpEx4B       = 'b 0001000000,
    DpWrEn       = 'b 0010000000,
    DpWrDi       = 'b 0100000000,
    // Unrecognizable commands: Just handle this as DpPayload
    DpUnknown    = 'b 1000000000
  } sel_datapath_e;

  typedef enum spi_byte_t {
    CmdNone = 8'h 00,

    CmdWriteStatus1 = 8'h 01,
    CmdWriteStatus2 = 8'h 31,
    CmdWriteStatus3 = 8'h 11,

    CmdReadStatus1 = 8'h 05,
    CmdReadStatus2 = 8'h 35,
    CmdReadStatus3 = 8'h 15,

    CmdJedecId = 8'h 9F,

    CmdPageProgram     = 8'h 02,
    CmdQuadPageProgram = 8'h 32, // Not supported

    CmdSectorErase  = 8'h 20, // 4kB erase
    CmdBlockErase32 = 8'h 52, // 32kB
    CmdBlockErase64 = 8'h D8, // 64kB

    CmdReadData   = 8'h 03,
    CmdReadFast   = 8'h 0B, // with Dummy
    CmdReadDual   = 8'h 3B,
    CmdReadQuad   = 8'h 6B,
    CmdReadDualIO = 8'h BB,
    CmdReadQuadIO = 8'h EB,

    CmdWriteDisable = 8'h 04,
    CmdWriteEnable  = 8'h 06,

    CmdEn4B = 8'h B7,
    CmdEx4B = 8'h E9,

    CmdReadSfdp = 8'h 5A,

    CmdChipErase = 8'h C7,

    CmdEnableReset = 8'h 66,
    CmdResetDevice = 8'h 99
  } spi_cmd_e;

  // Sram parameters
  parameter int unsigned SramDw      = 32;
  parameter int unsigned SramStrbW   = SramDw/8;
  parameter int unsigned SramOffsetW = $clog2(SramStrbW);

  // Msg region is used for read cmd in Flash and Passthrough region
  parameter int unsigned SramMsgDepth = 512; // 2kB
  parameter int unsigned SramMsgBytes = SramMsgDepth * SramStrbW;

  // Address Width of a Buffer in bytes
  parameter int unsigned SramBufferBytes = SramMsgBytes / 2; // Double Buffer
  parameter int unsigned SramBufferAw    = $clog2(SramBufferBytes);

  parameter int unsigned SramMailboxDepth = 256; // 1kB for mailbox

  // SPI Flash Discoverable Parameter is for host to get the device
  // information. It is a separate Command. The device provides a region in
  // DPSRAM for SW. The size is 256B
  parameter int unsigned SramSfdpDepth = 64;
  parameter int unsigned SramPayloadDepth = 64; // 256B for Program
  parameter int unsigned SramCmdFifoDepth = 16; // 16 x 1B for Cmd
  parameter int unsigned SramAddrFifoDepth = 16; // 16 x 4B for Addr
  parameter int unsigned SramTotalDepth = SramMsgDepth + SramMailboxDepth
                                        + SramSfdpDepth + SramPayloadDepth
                                        + SramCmdFifoDepth + SramAddrFifoDepth ;

  // Sram Depth is set to 1024 to satisfy DPSRAM parameter even though
  // SramTotalDepth above is 928.
  //parameter int unsigned SramDepth = 1024;
  import spi_device_reg_pkg::SramDepth;
  export spi_device_reg_pkg::SramDepth;

  parameter int unsigned SramAw = $clog2(spi_device_reg_pkg::SramDepth);

  typedef logic [SramAw-1:0]    sram_addr_t;
  typedef logic [SramDw-1:0]    sram_data_t;
  typedef logic [SramStrbW-1:0] sram_strb_t;
  typedef struct packed {
    logic uncorr;
    logic corr;
  } sram_err_t;

  typedef struct packed {
    logic       req;
    logic       we;
    sram_addr_t addr;
    sram_data_t wdata;
    sram_strb_t wstrb;
  } sram_l2m_t; // logic to Memory

  typedef struct packed {
    logic       rvalid;
    sram_data_t rdata;
    sram_err_t  rerror;
  } sram_m2l_t; // Memory to logic

  function automatic logic [SramDw-1:0] sram_strb2mask(logic [SramStrbW-1:0] strb);
    logic [SramDw-1:0] result;
    for (int unsigned i = 0 ; i < SramStrbW ; i++) begin
      result[8*i+:8] = strb[i] ? 8'h FF : 8'h 00;
    end
    return result;
  endfunction : sram_strb2mask

  function automatic logic [SramStrbW-1:0] sram_mask2strb(
    logic [SramDw-1:0] mask
  );
    logic [SramStrbW-1:0] result;
    for (int unsigned i = 0 ; i < SramStrbW ; i++) begin
      result[i] = &mask[8*i+:8];
    end
    return result;
  endfunction : sram_mask2strb

  // Calculate each space's base and size
  parameter sram_addr_t SramReadBufferIdx  = sram_addr_t'(0);
  parameter sram_addr_t SramReadBufferSize = sram_addr_t'(SramMsgDepth);

  parameter sram_addr_t SramMailboxIdx  = SramReadBufferIdx + SramReadBufferSize;
  parameter sram_addr_t SramMailboxSize = sram_addr_t'(SramMailboxDepth);

  parameter sram_addr_t SramSfdpIdx  = SramMailboxIdx + SramMailboxSize;
  parameter sram_addr_t SramSfdpSize = sram_addr_t'(SramSfdpDepth);

  parameter sram_addr_t SramPayloadIdx  = SramSfdpIdx + SramSfdpSize;
  parameter sram_addr_t SramPayloadSize = sram_addr_t'(SramPayloadDepth);

  parameter sram_addr_t SramCmdFifoIdx  = SramPayloadIdx + SramPayloadSize ;
  parameter sram_addr_t SramCmdFifoSize = sram_addr_t'(SramCmdFifoDepth);

  parameter sram_addr_t SramAddrFifoIdx  = SramCmdFifoIdx + SramCmdFifoSize ;
  parameter sram_addr_t SramAddrFifoSize = sram_addr_t'(SramAddrFifoDepth);

  // Max BitCount in a transaction
  parameter int unsigned BitLength = SramMsgDepth * 32;
  parameter int unsigned BitCntW   = $clog2(BitLength + 1);

  // spi device scanmode usage
  typedef enum logic [3:0] {
    ClkInvSel,
    CsbRstMuxSel,
    TxRstMuxSel,
    RxRstMuxSel,
    ClkMuxSel,
    ClkSramSel,
    RstSramSel,
    TpmRstSel,
    ScanModeUseLast
  } scan_mode_e;

  // TPM ======================================================================
  typedef struct packed {
    logic [7:0] rev;
    logic       locality;
    logic [2:0] max_wr_size;
    logic [2:0] max_rd_size;
  } tpm_cap_t;
  // TPM ----------------------------------------------------------------------

endpackage : spi_device_pkg
