// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Serial Peripheral Interface (SPI) Trusted Platform Module (TPM)
/*
*/

module spi_tpm
  import spi_device_pkg::*;
  import spi_device_reg_pkg::NumLocality;
#(
  parameter int unsigned CmdAddrFifoDepth  = 2,

  // Max Write/Read buffer size to support is 64B in TPM spec.
  // But more than 4B is for future use. So, 4B is recommended.
  parameter int unsigned WrFifoDepth = 4,
  parameter int unsigned RdFifoDepth = 4,
  parameter int unsigned RdFifoWidth = 32,

  // Locality determines the number of TPM_ACCESS registers.
  // Other HW managed registers are shared across the locality.
  // If host accesses the HW managed registers that are unsupported locality,
  // the HW returns 0xFF. The SW is responsible to the other SW managed
  // registers.
  parameter bit EnLocality   = 1,

  // derived
  localparam int unsigned CmdAddrPtrW = $clog2(CmdAddrFifoDepth+1),
  localparam int unsigned WrFifoPtrW  = $clog2(WrFifoDepth+1),
  localparam int unsigned RdFifoPtrW  = $clog2(RdFifoDepth+1),

  localparam int unsigned AccessRegSize    = 8, // times Locality
  localparam int unsigned IntEnRegSize     = 32,
  localparam int unsigned IntVectorRegSize = 8,
  localparam int unsigned IntStsRegSize    = 32,
  localparam int unsigned IntfCapRegSize   = 32,
  localparam int unsigned StatusRegSize    = 32,
  localparam int unsigned IdRegSize        = 32, // {DID, VID}
  localparam int unsigned RidRegSize       = 8,

  localparam int unsigned ActiveLocalityBitPos = 5, // Access[5]

  localparam int unsigned NumBits        = $bits(spi_byte_t),
  localparam int unsigned CmdAddrSize    = 32, // Cmd 8bit + Addr 24bit
  localparam int unsigned FifoRegSize    = 12, // lower 12bit excluding locality

  localparam int unsigned WrFifoWidth    = NumBits,

  // Read FIFO byte_offset calculation
  localparam int unsigned RdFifoNumBytes = RdFifoWidth / NumBits,
  localparam int unsigned RdFifoOffsetW  = prim_util_pkg::vbits(RdFifoNumBytes),

  // RdFifoBytesW is used to calculate the ReadFifo data in bytes.
  // TPM FSM compares the value to the requested xfer_size.
  localparam int unsigned RdFifoBytesW   = $clog2(RdFifoNumBytes),

  // FIFO size
  localparam int unsigned RdFifoSize = RdFifoDepth * RdFifoNumBytes,
  localparam int unsigned WrFifoSize = WrFifoDepth * (WrFifoWidth / NumBits),

  // TPM_CAP related constants.
  //  - Revision: the number visible in TPM_CAP CSR. Need to update the
  //    revision when the SW interface is revised.
  localparam logic [7:0] CapTpmRevision = 8'h 00,
  //  - Max Write Size: the supported write FIFO size is visible to the SW via
  //    TPM_CAP CSR
  localparam logic [2:0] CapMaxWrSize = 3'(unsigned'($clog2(WrFifoSize))),
  localparam logic [2:0] CapMaxRdSize = 3'(unsigned'($clog2(RdFifoSize)))
) (
  input clk_in_i,
  input clk_out_i,

  input sys_clk_i,

  input sys_rst_ni,
  input rst_n,
  input sys_sync_rst_ni,

  // SPI interface
  input        csb_i, // TPM needs separate CS#
  input        mosi_i,
  output logic miso_o,
  output logic miso_en_o,

  // TPM Capability
  output spi_device_pkg::tpm_cap_t tpm_cap_o,

  // sys_csb_pulse generated from CDC synchronizer
  input sys_csb_pulse_stretch,

  // Configurations
  //  tpm_en to turn on the TPM function
  input cfg_tpm_en_i,

  //  tpm_mode to switch TPM between FIFO anc CRB
  input cfg_tpm_mode_i,

  //  hw_reg_dis to turn off return-by-HW registers
  input cfg_tpm_hw_reg_dis_i,

  //  Disable TPM register checker. Logic won't compare addr[23:16] with 8'h
  //  D4 (TpmAddr).
  input cfg_tpm_reg_chk_dis_i,

  //  tpm_invalid_locality : TPM function returns invalid (0xFF) when the
  //  received address is out of the Locality.  If this bit is turned off, the
  //  logic uploads the command and address even the address is out of the max
  //  Locality.
  input cfg_tpm_invalid_locality_i,

  // Registers in SYS clock
  input [NumLocality*AccessRegSize-1:0] sys_access_reg_i,
  input [IntEnRegSize-1:0]              sys_int_enable_reg_i,
  input [IntVectorRegSize-1:0]          sys_int_vector_reg_i,
  input [IntStsRegSize-1:0]             sys_int_status_reg_i,
  input [IntfCapRegSize-1:0]            sys_intf_capability_reg_i,
  input [StatusRegSize-1:0]             sys_status_reg_i,
  input [IdRegSize-1:0]                 sys_id_reg_i,
  input [RidRegSize-1:0]                sys_rid_reg_i,

  // Buffer and FIFO status
  output logic                   sys_cmdaddr_rvalid_o,
  output logic [CmdAddrSize-1:0] sys_cmdaddr_rdata_o,
  input                          sys_cmdaddr_rready_i,

  output logic                   sys_wrfifo_rvalid_o,
  output logic [WrFifoWidth-1:0] sys_wrfifo_rdata_o,
  input                          sys_wrfifo_rready_i,

  input                    sys_rdfifo_wvalid_i,
  input  [RdFifoWidth-1:0] sys_rdfifo_wdata_i,
  output logic             sys_rdfifo_wready_o,

  // TPM_STATUS
  output logic                  sys_cmdaddr_notempty_o,
  output logic [WrFifoPtrW-1:0] sys_wrfifo_depth_o
);

  // Capability
  assign tpm_cap_o = '{
    rev:         CapTpmRevision,
    locality:    EnLocality,
    max_wr_size: CapMaxWrSize,
    max_rd_size: CapMaxRdSize
  };

  localparam int unsigned TpmRegisterSize = (AccessRegSize * NumLocality)
                                          + IntEnRegSize + IntVectorRegSize
                                          + IntStsRegSize + IntfCapRegSize
                                          + StatusRegSize + IdRegSize
                                          + RidRegSize;

  localparam logic [7:0]  TpmAddr           = 8'h D4;

  typedef enum logic [3:0] {
    RegAccess    = 4'h 0,
    RegIntEn     = 4'h 1,
    RegIntVect   = 4'h 2,
    RegIntSts    = 4'h 3,
    RegIntfCap   = 4'h 4,
    RegSts       = 4'h 5,
    RegHashStart = 4'h 6,
    RegId        = 4'h 7,
    RegRid       = 4'h 8,
    HwRegEnd     = 4'h 9
  } hw_reg_idx_e;
  localparam int unsigned NumHwReg = 32'(HwRegEnd);

  localparam logic [11:0] TpmReturnByHwAddr [NumHwReg] = '{
    12'h 000, // 000     Access_x
    12'h 008, // 00B:008 Interrupt Enable
    12'h 00C, // 00C     Interrupt Vector
    12'h 010, // 013:010 Interrupt Status
    12'h 014, // 017:014 Interface Capability
    12'h 018, // 01B:018 Status_x
    12'h 028, // 02B:028 Hash Start
    12'h F00, // F03:F00 DID_VID
    12'h F04  // F04:F04 RID
  };
  // TODO: internal reset (sys_rst_ni & csb_i)
  // Do we really need the csb reset for TPM?

  ////////////////
  // Definition //
  ////////////////

  // Configuration structure
  typedef struct packed {
    logic tpm_en;
    logic tpm_mode;
    logic hw_reg_dis;
    logic tpm_reg_chk_dis;
    logic invalid_locality;
  } tpm_cfg_t;

  typedef enum logic {
    Write = 1'b 0,
    Read  = 1'b 1
  } cmd_type_e;

  typedef enum logic [3:0] {
    // In Idle state, the TPM waits for the opcode from the host system. When
    // Opcode (first byte) is received, the TPM configures internal datapath
    // based on the opcode.  opcode[7]: Read(1)/Write(0) opcode[5:0]: transfer
    // size in 0-based number (e.g 'd63 == 64B)
    //
    // Next state:
    //  - StAddr: when bitcnt hits 5'h7, the state moves to StAddr state.
    //  - StErr??: If the xfer_size is bigger than the compile-time parameter,
    //    reports error.
    StIdle,

    // Address is 3B register offset. The logic decodes the address and
    // determines if the register to be returned by HW or by SW.
    //
    // HW managed registers:
    //  - TPM_ACCESS_x
    //  - TPM_INT_ENABLE
    //  - TPM_INT_VECTOR
    //  - TPM_INT_STATUS
    //  - TPM_INTF_CAPABILITY
    //  - TPM_STS_x
    //  - TPM_DID , TPM_VID
    //
    // Next state:
    //  - StWait: If the address is not for a Return-by-HW register, or the
    //    hw_reg_dis configuration is set, the state machine moves to WAIT
    //    state to send more WAIT byte to the SB.
    //  - StStartByte: If the received command is a read command and the
    //    address is for a Return-by-HW register and the hw_reg_dis config is
    //    not set, the state machine does not need more WAIT state. The state
    //    machine directly moves to StStartByte to send `START (0x01)`.
    //  - StWrite: If the received command is a write command, and the write
    //    FIFO is empty, the state machine moves to the StWrite state
    //    directly.  If this condition is met, the state machine sends `START`
    //    byte at the last byte of the address phase.
    StAddr,

    // In Wait state, the TPM sends 0x00 to SPI MISO line in order to hold the
    // host system to send write data or to receive the read data.
    //
    // Next state:
    //  - StStartByte: From Wait state, it always moves to StStartByte when
    //    FIFOs are ready to be used.
    StWait,

    // In StartByte state, TPM sends 0x01 to SPI MISO line. When the host
    // receives the data[0], it assumes the TPM device is ready to receive
    // data or to send the requested data if the value is 1.
    //
    // Next state:
    //  - StReadFifo: If the received command is a read command (cmd_type ==
    //    Read), the state machine moves to StRead and sends the output of the
    //    read FIFO to the parallel-to-serial module.
    //  - StReadHwReg: If the received address is hw reg, and enabled hw
    //    return, move to ReadHwReg state to return the HW data.
    //  - StWrite: If the received command is a write command (cmd_type ==
    //    Write), the state machine moves to StWrite and stacks the incoming
    //    data into the write FIFO. It is assumed that the write FIFO has
    //    enough empty space to store the incoming transfer size.
    StStartByte,

    // In Read state, the module reads data from the Read FIFO and returns to
    // the host system. After the transfer size amount of data is sent, it
    // moves to the End state.
    //
    // Next state:
    //  - ??? : If the SB toggles more than the xfer size?
    StReadFifo,

    StReadHwReg,

    // In Write state, the module accepts the data from MOSI and stores into
    // the Write FIFO. After the transfer size amount of data is received, the
    // TPM stop receiving the data and move to the End state.
    //
    // Next state:
    //  - StEnd: When the module stores the xfer_size amount of the write data
    //    into the write FIFO, it moves to StEnd state and waits for the CS#
    //    deassertion.
    StWrite,

    StInvalid,

    // In End state, TPM waits for the CSb de-assertion. This is
    // TERMINAL_STATE.
    StEnd
  } st_e;

  st_e sck_st_q, sck_st_d;

  // tpm_reg_t struct defines the Return-by-HW registers. These registers must
  // be processed by the HW to return the data in at most one WAIT cycle.
  //
  // The TPM submodule returns WAIT by default at the last byte of the address
  // phase. Then, when the module receives the addr[2], it knows the SB is
  // accessing the Return-by-HW registers. It sets the `is_hw_reg` flag.
  //
  // When the state machine in this submodule moves from the Address state, if
  // the flag is set and the `cfg_tpm_hw_reg_dis_i` is cleard, the state
  // machine directly moves to `START` state as it does not need to wait
  // longer.
  typedef struct packed {
    logic [AccessRegSize*NumLocality-1:0] access;
    logic [IntEnRegSize-1:0]              int_enable;
    logic [IntVectorRegSize-1:0]          int_vector;
    logic [IntStsRegSize-1:0]             int_status;
    logic [IntfCapRegSize-1:0]            intf_capacity;
    logic [StatusRegSize-1:0]             status;
    logic [IdRegSize-1:0]                 id;  // Device ID, Vendor ID
    logic [RidRegSize-1:0]                rid; // Revision ID
  } tpm_reg_t;

  ///////////
  // Signal//
  ///////////

  tpm_cfg_t sys_tpm_cfg;
  tpm_cfg_t sys_clk_tpm_cfg;
  logic sys_clk_tpm_en;

  assign sys_tpm_cfg = '{
    tpm_en:           cfg_tpm_en_i,
    tpm_mode:         cfg_tpm_mode_i,
    hw_reg_dis:       cfg_tpm_hw_reg_dis_i,
    invalid_locality: cfg_tpm_invalid_locality_i,
    tpm_reg_chk_dis:  cfg_tpm_reg_chk_dis_i
  };

  tpm_reg_t sys_tpm_reg;
  tpm_reg_t sys_clk_tpm_reg;


  logic [NumLocality-1:0] sys_active_locality; // TPM_ACCESS_x[5]

  assign sys_tpm_reg = '{
    access:        sys_access_reg_i,
    int_enable:    sys_int_enable_reg_i,
    int_vector:    sys_int_vector_reg_i,
    int_status:    sys_int_status_reg_i,
    intf_capacity: sys_intf_capability_reg_i,
    status:        sys_status_reg_i,
    id:            sys_id_reg_i,
    rid:           sys_rid_reg_i
  };

  // FIFOs
  logic                   sck_cmdaddr_wvalid,  sck_cmdaddr_wready;
  logic [CmdAddrSize-1:0] sck_cmdaddr_wdata_q, sck_cmdaddr_wdata_d;
  logic [CmdAddrPtrW-1:0] sys_cmdaddr_rdepth,  sck_cmdaddr_wdepth;

  logic [FifoRegSize-1:0] isck_fifoaddr; // latched from sck_cmdaddr_wdata_d
  logic                   sck_fifoaddr_latch;
  // isck_fifoaddr_latch converts sck_fifoaddr_latch by half SPI_CLK period.
  logic                   isck_fifoaddr_latch;

  logic isck_fifoaddr_inc;

  // (sys_cmdaddr_rdepth > 0)
  assign sys_cmdaddr_notempty_o = |sys_cmdaddr_rdepth;

  logic                   sck_wrfifo_wvalid, sck_wrfifo_wready;
  logic [WrFifoWidth-1:0] sck_wrfifo_wdata;
  logic [WrFifoPtrW-1:0]  sys_wrfifo_rdepth, sck_wrfifo_wdepth;

  assign sys_wrfifo_depth_o = sys_wrfifo_rdepth;

  // Read FIFO uses inverted SCK (clk_out_i)
  logic                     isck_rdfifo_rvalid, isck_rdfifo_rready;
  logic [RdFifoWidth-1:0]   isck_rdfifo_rdata;
  logic [RdFifoPtrW-1:0]    isck_rdfifo_rdepth;

  logic [RdFifoOffsetW-1:0]     isck_rdfifo_idx;
  logic                         isck_rd_byte_sent;

  // If NumBytes != 1, then the logic selects a byte from isck_rdfifo_rdata
  logic [NumBits-1:0] isck_sel_rdata;

  // Assume the NumBytes is power of two
  `ASSERT_INIT(RdFifoNumBytesPoT_A,
    (2**RdFifoOffsetW == RdFifoNumBytes) || (RdFifoNumBytes == 1))
  `ASSERT_INIT(RdFifoDepthPoT_A, 2**$clog2(RdFifoDepth) == RdFifoDepth)

  // If cmdaddr_shift_en is 1, the logic stacks the incoming MOSI into cmdaddr
  // register.
  logic       cmdaddr_shift_en;
  logic [4:0] cmdaddr_bitcnt;

  logic [23:0] addr; // used temporary while shifting the cmd address

  // Write Data Latch Enable: Latch and generate a pulse when a byte is stacked.
  logic       wrdata_shift_en;
  logic [2:0] wrdata_bitcnt;

  logic [7:0] wrdata_q, wrdata_d;

  // Read FIFO is in inverted SCK domain (clk_out)
  logic       sck_rddata_shift_en;

  // Indicate if the received address is FIFO/CRB register. Should start with
  // D4_xxxx
  logic is_tpm_reg;
  logic check_tpm_reg;

  // If the received command falls into the return-by-HW registers, then
  // `is_hw_reg` is set.
  logic is_hw_reg;
  hw_reg_idx_e sck_hw_reg_idx, isck_hw_reg_idx;

  logic [31:0] isck_hw_reg_word;
  logic [7:0]  isck_hw_reg_byte;

  // Set this signal when the received address bits are enough, which should
  // be address[23:2] or bigger.
  logic check_hw_reg;

  // When the address shifted up to addr[12] (cmdaddr_bitcnt == 5'h 13), the
  // module can decide if the received address is in the Locality or not. If
  // it is not in the locality, the logic may return the invalid and discard
  // the request.
  logic latch_locality;

  // bit[15:12] in the received address is the locality if the address is FIFO
  // addr.
  logic [3:0] locality;

  // Indicate the locality is greater than or equal to NumLocality.
  // with tpm_cfg.invalid_locality, the logic returns FFh if host sends read
    // requests to unsupported locality.
  logic       invalid_locality;


  // The first bit of the command (Command[7]) indicates the command direction.
  logic      latch_cmd_type;
  cmd_type_e cmd_type;

  // xfer_size: Command[5:0] is the command xfer size. currently the logic
  // supports up to WrFifoDepth.
  logic       latch_xfer_size;
  logic [5:0] xfer_size;
  logic [5:0] xfer_bytes_q, xfer_bytes_d;
  logic       xfer_size_met;

  // Indicating that the Read FIFO has enough data to send to the host.
  logic       enough_payload_in_rdfifo;

  // Output MISO
  typedef enum logic [2:0] {
    SelWait     = 3'h 0, // 0x00
    SelStart    = 3'h 1, // 0x01
    SelInvalid  = 3'h 2, // 0xFF
    SelHwReg    = 3'h 3, // depends on hw_reg_idx
    SelRdFifo   = 3'h 4  // from RdFifo
  } tpm_data_sel_e;

  logic       sck_p2s_valid;

  logic       isck_p2s_valid;
  logic [7:0] isck_p2s_data;
  logic       isck_p2s_sent;

  tpm_data_sel_e sck_data_sel, isck_data_sel;

  logic isck_miso_en;
  logic isck_miso;

  assign miso_en_o = isck_miso_en;
  assign miso_o    = isck_miso;

  /////////
  // CDC //
  /////////

  assign sys_clk_tpm_en = cfg_tpm_en_i;

  // Configuration latched into sys_clk
  always_ff @(posedge sys_clk_i or negedge sys_rst_ni) begin
    if (!sys_rst_ni) begin
      sys_clk_tpm_cfg <= '{default: '0};
      sys_clk_tpm_reg <= '{default: '0};
    end else begin
      if (sys_csb_pulse_stretch) begin
        sys_clk_tpm_cfg <= sys_tpm_cfg;
        sys_clk_tpm_reg <= sys_tpm_reg;
        for (int unsigned i = 0 ; i < NumLocality ; i++) begin
          sys_active_locality[i] <=
            sys_tpm_reg.access[AccessRegSize*i + ActiveLocalityBitPos];
        end
      end
    end
  end

  // data_sel (sck -> isck)
  always_ff @(posedge clk_out_i or negedge rst_n) begin
    if (!rst_n) begin
      isck_data_sel <= SelWait;
    end else begin
      isck_data_sel <= sck_data_sel;
    end
  end

  //////////////
  // Datapath //
  //////////////

  // command, addr latch
  always_ff @(posedge clk_in_i or negedge rst_n) begin
    if (!rst_n) begin
      cmdaddr_bitcnt <= 5'h 0;
    end else if (cmdaddr_shift_en) begin
      cmdaddr_bitcnt <= cmdaddr_bitcnt + 5'h 1;
    end
  end

  // Control signals:
  //  latch_cmd_type
  assign latch_cmd_type = (cmdaddr_bitcnt == 5'h 0) && (sck_st_q == StIdle);

  assign check_tpm_reg = (cmdaddr_bitcnt == 5'h 0F);

  assign check_hw_reg = (cmdaddr_bitcnt == 5'h 1D);

  // sck_fifoaddr_latch & isck_fifoaddr_latch.
  //
  // isck_fifoaddr_latch is used to latch `isck_fifoaddr` as the name implies.
  // The sck_fifoaddr_latch is high at the last beat of the address field as
  // shown below.
  //           _   _   _   _   _
  // SPI_CLK _/ \_/ \_/ \_/ \_/ \_
  //           ___ ___ ___ ___ ___
  // bitcnt   X 0 X ..X 1EX 1FX
  //
  // But the data is valid second half of the 'h 1F phase. However, the
  // latching logic latches @ clk_out_i (Inverted SPI_CLK). So it latches at
  // a cycle earlier.
  //
  //                       | err here
  //            _   _   _   _   _
  // iSPI_CLK _/ \_/ \_/ \_/ \_/ \_
  //         ___ ___ ___ ___ ___
  // bitcnt  X 0 X ..X 1EX 1FX
  //
  //
  // isck_fifoaddr_latch delays sck_fifoaddr_latch for the logic latches the
  // address correctly.
  assign sck_fifoaddr_latch = (cmdaddr_bitcnt == 5'h 1F);

  always_ff @(posedge clk_out_i or negedge rst_n) begin
    if (!rst_n) begin
      isck_fifoaddr_latch <= 1'b 0;
    end else begin
      isck_fifoaddr_latch <= sck_fifoaddr_latch;
    end
  end

  always_ff @(posedge clk_in_i or negedge rst_n) begin
    if (!rst_n) begin
      sck_cmdaddr_wdata_q <= '0;
    end else if (cmdaddr_shift_en) begin
      sck_cmdaddr_wdata_q <= sck_cmdaddr_wdata_d;
    end
  end

  assign sck_cmdaddr_wdata_d = {sck_cmdaddr_wdata_q[0+:CmdAddrSize-1], mosi_i};

  logic  unused_cmdaddr_wdata_q;
  assign unused_cmdaddr_wdata_q = sck_cmdaddr_wdata_q[CmdAddrSize-1];

  // fifoaddr latch
  //  clk_out (iSCK)
  always_ff @(posedge clk_out_i or negedge rst_n) begin
    if (!rst_n) begin
      isck_fifoaddr <= '0;
    end else if (isck_fifoaddr_latch) begin
      // Shall assert when sck_st_q moves away from StAddr
      isck_fifoaddr <= sck_cmdaddr_wdata_q[FifoRegSize-1:0];
    end else if (isck_fifoaddr_inc) begin
      isck_fifoaddr <= isck_fifoaddr + 1'b 1;
    end
  end
  `ASSERT(SckFifoAddrLatchCondition_A,
          sck_fifoaddr_latch |=>
            $past(sck_st_q) == StAddr && (sck_st_q inside {StWait, StStartByte}
                                          || invalid_locality),
          clk_in_i, !rst_n)

  // only fifoaddr[1:0] is used in this version.
  logic  unused_fifoaddr;
  assign unused_fifoaddr = ^isck_fifoaddr[FifoRegSize-1:2];

  // fifoaddr_inc @ iSCK :: SCK is not useful at all. SW can compute the
  // address with the xfer_size and input address in CmdAddr buffer.
  //
  // Increase the address only when HwReg is selected (for now)
  // Other cases have no usecase as of now.
  assign isck_fifoaddr_inc = isck_p2s_sent && (isck_data_sel == SelHwReg);

  // Write Data Latch
  always_ff @(posedge clk_in_i or negedge rst_n) begin
    if (!rst_n) begin
      wrdata_bitcnt <= '0;
    end else if (wrdata_shift_en) begin
      wrdata_bitcnt <= wrdata_bitcnt + 3'h 1;
    end
  end

  assign sck_wrfifo_wvalid = (wrdata_bitcnt == 3'h 7);

  always_ff @(posedge clk_in_i or negedge rst_n) begin
    if (!rst_n) begin
      wrdata_q <= 8'h 0;
    end else if (wrdata_shift_en) begin
      wrdata_q <= wrdata_d;
    end
  end

  assign wrdata_d = {wrdata_q[6:0], mosi_i};

  assign sck_wrfifo_wdata = wrdata_d;

  // Address: This is a comb logic that shows correct address value when the
  // address is compared with other logics
  always_comb begin
    addr = 24'h 00_0000;
    unique case (1'b 1)
      check_tpm_reg: begin
        // when checking the tpm_reg, only 8bit address is received.
        // Look at the assertion TpmRegCondition_A.
        addr = {sck_cmdaddr_wdata_d[7:0], 16'h 0000};
      end

      // locality in the TPM transaction is in addr[15:12].
      // latch_locality is asserted at the 16th beat.
      // Look at the assertion LocalityLatchCondition_A
      latch_locality: begin
        addr = {sck_cmdaddr_wdata_d[11:0], 12'h 000};
      end

      check_hw_reg: begin
        // In Return-by-HW Reg check stage, the lower 2 bits were not arrived.
        // Look at the assertion HwRegCondition_A
        addr = {sck_cmdaddr_wdata_d[21:0], 2'b 00};
      end

      default: addr = 24'h 00_0000;
    endcase
  end

  // when the address[16] is received, check if the address is for FIFO/CRB.
  // If checker is turned off, `is_tpm_reg` becomes 1 regardless of addr
  always_ff @(posedge clk_in_i or negedge rst_n) begin
    if (!rst_n) begin
      is_tpm_reg <= 1'b 0;
    end else if (check_tpm_reg &&
      (sys_clk_tpm_cfg.tpm_reg_chk_dis || (addr[23:16] == TpmAddr))) begin
      is_tpm_reg <= 1'b 1;
    end
  end

  // Return-by-HW register check
  logic        is_hw_reg_d;
  hw_reg_idx_e sck_hw_reg_idx_d;

  always_ff @(posedge clk_in_i or negedge rst_n) begin
    if (!rst_n) begin
      is_hw_reg      <= 1'b 0;
      sck_hw_reg_idx <= RegAccess;
    end else if (!sys_clk_tpm_cfg.tpm_mode && check_hw_reg && (cmd_type == Read)
      && is_tpm_reg && !invalid_locality && !sys_clk_tpm_cfg.hw_reg_dis) begin
      // HW register is set only when the following conditions are met:
      //
      // 1. TPM is in FIFO mode
      // 2. The command received is a Read command.
      // 3. Is TPM register (starting with 0xD4_XXXX) or tpm_reg_chk_dis is set
      // 4. Received locality is in the range of supported Locality.
      is_hw_reg      <= is_hw_reg_d;
      sck_hw_reg_idx <= sck_hw_reg_idx_d;
    end // if check_hw_reg
  end

  always_comb begin
    is_hw_reg_d = 1'b 0;
    sck_hw_reg_idx_d = hw_reg_idx_e'(0);
    // check_hw_reg asserts when cmdaddr_bitcnt is 29.
    for (int i = 0 ; i < NumHwReg; i ++) begin
      if (TpmReturnByHwAddr[i][11:2] == addr[11:2]) begin
        is_hw_reg_d      = 1'b 1;
        sck_hw_reg_idx_d = hw_reg_idx_e'(i);
      end
    end // for
  end

  // hw_reg_idx (sck -> isck)
  // Remember that the logic chooses only one HwReg at a transaction.
  // It does not send continuously even the transfer size is greater than the
  // word boundary.
  always_ff @(posedge clk_out_i or negedge rst_n) begin
    if (!rst_n) isck_hw_reg_idx <= RegAccess;
    else        isck_hw_reg_idx <= sck_hw_reg_idx;
  end

  // locality store
  always_ff @(posedge clk_in_i or negedge rst_n) begin
    if (!rst_n) begin
      locality         <= '0;
      invalid_locality <= 1'b 0;
    end else if (latch_locality && is_tpm_reg) begin
      locality         <= addr[15:12];
      invalid_locality <= (addr[15:12] < 4'(NumLocality)) ? 1'b 0: 1'b 1;
    end
  end

  // cmd_type
  always_ff @(posedge clk_in_i or negedge rst_n) begin
    if (!rst_n) begin
      cmd_type <= Write;
    end else if (latch_cmd_type) begin
      // latch at the very first SCK edge
      cmd_type <= cmd_type_e'(sck_cmdaddr_wdata_d[0]);
    end
  end

  // xfer_size
  always_ff @(posedge clk_in_i or negedge rst_n) begin
    if (!rst_n) begin
      xfer_size <= 6'h 0;
    end else if (latch_xfer_size) begin
      xfer_size <= sck_cmdaddr_wdata_d[5:0];
    end
  end

  // Xfer size count
  always_ff @(posedge clk_in_i or negedge rst_n) begin
    if (!rst_n) begin
      xfer_bytes_q <= '0;
    end else if ((isck_p2s_sent && sck_rddata_shift_en) ||
      (sck_wrfifo_wvalid && wrdata_shift_en)) begin
      xfer_bytes_q <= xfer_bytes_d;
    end
  end
  assign xfer_bytes_d  = xfer_bytes_q + 6'h 1;
  assign xfer_size_met = xfer_bytes_q == xfer_size;

  // xfer_size is 0 based. FIFO depth is 1 based. GTE -> Greater than
  assign enough_payload_in_rdfifo =
    (7'({isck_rdfifo_rdepth, RdFifoBytesW'(0)}) > {1'b 0, xfer_size})
    | (7'(RdFifoSize) <= 7'(xfer_size));

  // Output data mux
  `ASSERT_KNOWN(DataSelKnown_A, isck_data_sel, clk_out_i, !rst_n)
  always_comb begin
    isck_p2s_data = 8'h 00;

    unique case (isck_data_sel)
      SelWait: begin
        isck_p2s_data = 8'h 00;
      end

      SelStart: begin
        isck_p2s_data = 8'h 01;
      end

      SelInvalid: begin
        isck_p2s_data = 8'h FF;
      end

      SelHwReg: begin
        isck_p2s_data = isck_hw_reg_byte;
      end

      SelRdFifo: begin
        isck_p2s_data = isck_sel_rdata;
      end

      default: begin
        isck_p2s_data = 8'h 00;
      end
    endcase
  end

  // HW REG mux
  prim_slicer #(
    .InW    (32),
    .OutW   (8),
    .IndexW (2)
  ) u_hw_reg_slice (
    .sel_i (isck_fifoaddr[1:0]),
    .data_i (isck_hw_reg_word),
    .data_o (isck_hw_reg_byte)
  );

  `ASSERT_KNOWN(HwRegIdxKnown_A, isck_hw_reg_idx, clk_out_i, !rst_n)
  always_comb begin : hw_reg_mux
    isck_hw_reg_word = 32'h FFFF_FFFF;

    unique case (isck_hw_reg_idx)
      RegAccess: begin
        for (int unsigned i = 0 ; i < NumLocality ; i++) begin
          if (!invalid_locality && (4'(i) == locality)) begin
            isck_hw_reg_word = { {(32-AccessRegSize){1'b1}},
              sys_clk_tpm_reg.access[AccessRegSize*i+:AccessRegSize]};
          end
        end
      end

      RegIntEn: begin
        isck_hw_reg_word = sys_clk_tpm_reg.int_enable;
      end

      RegIntVect: begin
        isck_hw_reg_word = {24'h FFFFFF, sys_clk_tpm_reg.int_vector};
      end

      RegIntSts: begin
        isck_hw_reg_word = sys_clk_tpm_reg.int_status;
      end

      RegIntfCap: begin
        isck_hw_reg_word = sys_clk_tpm_reg.intf_capacity;
      end

      RegSts: begin
        // Check locality to return FFh or correct value
        if (!invalid_locality && sys_active_locality[locality[2:0]]) begin
          // return data
          isck_hw_reg_word = sys_clk_tpm_reg.status;
        end else begin
          isck_hw_reg_word = 32'h FFFF_FFFF;
        end
      end

      RegHashStart: begin
        isck_hw_reg_word = 32'h FFFF_FFFF;
      end

      RegId: begin
        isck_hw_reg_word = sys_clk_tpm_reg.id;
      end

      RegRid: begin
        isck_hw_reg_word = {24'h FFFFFF, sys_clk_tpm_reg.rid};
      end

      default: begin
        isck_hw_reg_word = 32'h FFFF_FFFF;
      end
    endcase
  end : hw_reg_mux

  // Parallel to Serial (Output)
  //
  //  Parallel to Serial datapath in the TPM submodule differs from spi_p2s
  //  module used in the SPI_DEVICE.
  //
  //  The logic in the TPM always works as byte granularity. The logic loops
  //  8 stage. Each stage sends the bit of the input p2s_data from 7 to 0.
  //  Even the p2s_valid is asserted not in the byte granularity (e.g:
  //  asserted when bit position is 4), the logic directly sends the
  //  p2s_data[4] and turns on the output enable signal.
  //
  //  The single IO characteristic of the TPM submodule simplifies the logic
  //  above.
  //
  //  The p2s logic does not have the problem that spi_fwmode has. As SPI TPM
  //  does not support Mode 3, there's no case that the CSb de-asserted
  //  without the 8th negedge of SCK. So, the logic asserts the FIFO pop
  //  signal (`rready`) at the 8th beat.
  logic [2:0] isck_p2s_bitcnt; // loop from 7 to 0

  always_ff @(posedge clk_out_i or negedge rst_n) begin
    if (!rst_n) begin
      isck_p2s_bitcnt <= 3'h 7;
    end else begin
      isck_p2s_bitcnt <= isck_p2s_bitcnt - 1'b 1;
    end
  end

  // p2s_valid & p2s_sent & p2s_data
  //                                        ~|isck_p2s_bitcnt
  assign isck_p2s_sent = isck_p2s_valid && (isck_p2s_bitcnt == '0);

  always_ff @(posedge clk_out_i or negedge rst_n) begin
    if (!rst_n) isck_p2s_valid <= 1'b 0;
    else        isck_p2s_valid <= sck_p2s_valid;
  end

  // Decided to implement 8-to-1 mux rather than conventional shift out for
  // Parallel-to-Serial. It is to support sending StartByte in StAddr phase.
  // This logic affects the timing. If the logic cannot meet the timing
  // requirement, the FSM must not send Start Byte at the last byte of the
  // address phase and change the logic to shift out logic.
  //
  // The datapath can be reduced to use 3-to-1 mux. The condition of sending
  // Start/Wait bit is determined at the addr[2] beat. It means, the MISO data
  // comes from:
  //
  // - registered_data[7]
  // - input p2s_data[7]
  // - input p2s_data[2]
  //
  // The logic, however, introduces more limitation and gains little benefit.
  // The logic depth is just one depth less than the original implementation.
  assign isck_miso    = isck_p2s_data[isck_p2s_bitcnt];
  assign isck_miso_en = isck_p2s_valid;


  // Read FIFO data selection and FIFO ready
  // rvalid -> rready is OK not the opposit direction (rready -> rvalid)
  assign isck_rd_byte_sent = isck_rdfifo_rvalid
                             && isck_p2s_sent
                             && (isck_data_sel == SelRdFifo);
  if (RdFifoNumBytes == 1) begin : g_rdfifo_1_to_1
    assign isck_rdfifo_rready = isck_rd_byte_sent;

    assign isck_sel_rdata = isck_rdfifo_rdata;

    logic  unused_rdfifo_idx;
    assign unused_rdfifo_idx = isck_rdfifo_idx;
    assign isck_rdfifo_idx = 1'b 0;
  end else begin : g_rdfifo_n_to_1
    // Select RdFIFO RDATA
    assign isck_sel_rdata = isck_rdfifo_rdata[NumBits*isck_rdfifo_idx+:NumBits];

    // Index Increase
    always_ff @(posedge clk_out_i or negedge rst_n) begin
      if (!rst_n) begin
        isck_rdfifo_idx <= '0;
      end else if (isck_rd_byte_sent) begin
        isck_rdfifo_idx <= isck_rdfifo_idx + 1'b 1;
      end
    end

    // Only when isck_rdfifo_idx reached end byte, pop the FIFO entry
    assign isck_rdfifo_rready = isck_rd_byte_sent && (&isck_rdfifo_idx);

  end

  ///////////////////
  // State Machine //
  ///////////////////

  // Inputs
  //  - CFG: (tpm_en, tpm_hw_reg_dis, tpm_invalid_locality)
  //  - is_hw_reg
  //
  // Outputs
  //  - latch_cmd_type
  //  - latch_xfer_size
  //  - latch_locality
  //  - check_hw_reg
  //  - check_tpm_reg
  //  - cmdaddr_shift_en
  //  - wrdata_shift_en
  //  - p2s_valid
  //  - sck_data_sel

  always_ff @(posedge clk_in_i or negedge rst_n) begin
    if (!rst_n) begin
      sck_st_q <= StIdle;
    end else begin
      sck_st_q <= sck_st_d;
    end
  end

  always_comb begin : next_state
    sck_st_d = sck_st_q;

    // Default output values
    latch_xfer_size = 1'b 0;
    latch_locality  = 1'b 0;

    cmdaddr_shift_en    = 1'b 0;
    wrdata_shift_en     = 1'b 0;
    sck_rddata_shift_en = 1'b 0;

    sck_p2s_valid = 1'b 0;
    sck_data_sel  = SelWait;

    // Upload commands when HW needs SW returning data.
    //
    // if host issues to invalid locality or return-by-HW registers, TPM HW
    // does not push the command and address to FIFO.
    sck_cmdaddr_wvalid = 1'b 0;

    unique case (sck_st_q)
      StIdle: begin
        cmdaddr_shift_en = 1'b 1;

        if (cmdaddr_bitcnt == 5'h 7) begin
          if (sys_clk_tpm_en) begin
            sck_st_d = StAddr;

            latch_xfer_size = 1'b 1;
          end else begin
            // Stop processing and move to End state.
            // sys_clk_tpm_cfg.tpm_en cannot be compared right after reset.  Due
            // to the absent of the SCK, the configuration cannot be
            // synchronized into SCK domain at the first 3 clock cycle.
            // So, the enable signal is checked when the state is about to
            // move to StAddr.
            sck_st_d = StEnd;
          end
        end // cmdaddr_bitcnt == 5'h 7
      end // StIdle

      StAddr: begin
        // NOTE: The coding style in this state is ugly. How can we improve?
        cmdaddr_shift_en = 1'b 1;

        // Latch locality
        if (cmdaddr_bitcnt == 5'h 13) begin
          latch_locality = 1'b 1;
        end

        if (cmdaddr_bitcnt >= 5'h 18) begin
          // Send Wait byte [18h:1Fh]
          sck_p2s_valid = 1'b 1;
          sck_data_sel  = SelWait;
        end

        // Next state: if is_tpm_reg 1 && !cfg_hw_reg_dis
        if (cmdaddr_bitcnt == 5'h 1F && cmd_type == Read) begin
          if (!is_tpm_reg || sys_clk_tpm_cfg.tpm_mode) begin
            // If out of TPM register (not staring with 0xD4_XXXX) or
            // TPM mode is CRB, always processed by SW
            sck_st_d = StWait;

            sck_cmdaddr_wvalid = 1'b 1;
          end else if (is_hw_reg) begin
            // If read command and HW REG, then return by HW
            // is_hw_reg contains (is_tpm_reg && (locality < NumLocality))
            sck_st_d = StStartByte;
          end else if (invalid_locality && sys_clk_tpm_cfg.invalid_locality) begin
            // The read request is out of supported Localities.
            // Return FFh
            sck_st_d = StInvalid;
          end else begin
            // Other read command sends to Wait, till SW response
            sck_st_d = StWait;

            sck_cmdaddr_wvalid = 1'b 1;
          end
        end // cmdaddr_bitcnt == 5'h 1F

        if (cmdaddr_bitcnt == 5'h 1F && cmd_type == Write) begin
          // Always upload for SW to process
          sck_cmdaddr_wvalid = 1'b 1;

          if (~|sck_wrfifo_wdepth) begin
            // Write command and FIFO is empty. Ready to push
            // TODO: Change the state machine to send start byte at
            //       cmdaddr_bitcnt == 5'h 17 if write command and FIFO is
            //       empty, then the state can go to StWrite directly.
            sck_st_d = StStartByte;
          end else begin
            // FIFO is not empty. Move to StWait and waits for the empty write
            // fifo.
            sck_st_d = StWait;
          end
        end // cmd_type == Write
      end // StAddr

      StWait: begin
        sck_p2s_valid = 1'b 1;
        sck_data_sel = SelWait;

        // at every LSB of a byte, check the next state condition
        if (isck_p2s_sent &&
          (((cmd_type == Read) && enough_payload_in_rdfifo) ||
          ((cmd_type == Write) && ~|sck_wrfifo_wdepth))) begin
          sck_st_d = StStartByte;
        end
      end // StWait

      StStartByte: begin
        sck_p2s_valid = 1'b 1;
        sck_data_sel  = SelStart;

        if (isck_p2s_sent) begin
          // Must move to next state as StartByte is a byte
          if ((cmd_type == Read) && is_hw_reg) begin
            sck_st_d = StReadHwReg;
          end else if (cmd_type == Read) begin
            sck_st_d = StReadFifo;
          end else if (cmd_type == Write) begin
            sck_st_d = StWrite;
          end
        end
      end // StStartByte

      StReadFifo: begin
        sck_rddata_shift_en = 1'b 1;

        sck_p2s_valid = 1'b 1;
        sck_data_sel  = SelRdFifo;

        // TODO: RdFifo rready (sck --> isck)

        // TODO: check xfer_size handling
        if (isck_p2s_sent && xfer_size_met) begin
          sck_st_d = StEnd;
        end
      end // StReadFifo

      StReadHwReg: begin
        sck_p2s_valid = 1'b 1;
        sck_data_sel  = SelHwReg;

        // HW Reg slice? using index

        if (isck_p2s_sent && xfer_size_met) begin
          sck_st_d = StEnd;
        end
      end // StReadHwReg

      StWrite: begin
        wrdata_shift_en = 1'b 1;
        // Processed by the logic. Does not have to do

        // TODO: check xfer_size handling
        if (sck_wrfifo_wvalid && xfer_size_met) begin
          sck_st_d = StEnd;
        end
      end // StWrite

      StInvalid: begin // TERMINAL_STATE
        // Send FFh
        if (cmd_type == Read) begin
          sck_p2s_valid = 1'b 1;
          sck_data_sel  = SelInvalid;
        end
      end // StInvalid

      StEnd: begin // TERMINAL_STATE
        // TODO: Check if open pull-up cancel the transaction?
        //       If yes, then drive 0x00 for the read command
        if (cmd_type == Read) begin
          sck_p2s_valid = 1'b 1;
          sck_data_sel  = SelWait; // drive 0x00
        end
      end // StEnd

      default: begin
        sck_st_d = StIdle;
      end
    endcase

  end : next_state

  //////////////
  // Instance //
  //////////////
  prim_fifo_async #(
    .Width (CmdAddrSize),
    .Depth (CmdAddrFifoDepth),
    .OutputZeroIfEmpty (1'b 1)
  ) u_cmdaddr_buffer (
    .clk_wr_i  (clk_in_i),
    .rst_wr_ni (sys_rst_ni),
    .wvalid_i  (sck_cmdaddr_wvalid),
    .wready_o  (sck_cmdaddr_wready),
    .wdata_i   (sck_cmdaddr_wdata_d),
    .wdepth_o  (sck_cmdaddr_wdepth),

    .clk_rd_i  (sys_clk_i),
    .rst_rd_ni (sys_rst_ni),
    .rvalid_o  (sys_cmdaddr_rvalid_o),
    .rready_i  (sys_cmdaddr_rready_i),
    .rdata_o   (sys_cmdaddr_rdata_o),
    .rdepth_o  (sys_cmdaddr_rdepth)
  );

  prim_fifo_async #(
    .Width (WrFifoWidth),
    .Depth (WrFifoDepth),
    .OutputZeroIfEmpty (1'b 1)
  ) u_wrfifo (
    .clk_wr_i  (clk_in_i),
    .rst_wr_ni (sys_rst_ni),
    .wvalid_i  (sck_wrfifo_wvalid),
    .wready_o  (sck_wrfifo_wready),
    .wdata_i   (sck_wrfifo_wdata),
    .wdepth_o  (sck_wrfifo_wdepth),

    .clk_rd_i  (sys_clk_i),
    .rst_rd_ni (sys_rst_ni),
    .rvalid_o  (sys_wrfifo_rvalid_o),
    .rready_i  (sys_wrfifo_rready_i),
    .rdata_o   (sys_wrfifo_rdata_o),
    .rdepth_o  (sys_wrfifo_rdepth)

  );

  // The content inside the Read FIFO needs to be flush out when a TPM
  // transaction is completed (CSb deasserted).  So, everytime CSb is
  // deasserted --> rst_n asserted. So, reset the read FIFO.
  prim_fifo_async #(
    .Width (RdFifoWidth),
    .Depth (RdFifoDepth),
    .OutputZeroIfEmpty (1'b 1)
  ) u_rdfifo (
    .clk_wr_i  (sys_clk_i),
    .rst_wr_ni (sys_sync_rst_ni),
    .wvalid_i  (sys_rdfifo_wvalid_i),
    .wready_o  (sys_rdfifo_wready_o),
    .wdata_i   (sys_rdfifo_wdata_i),
    .wdepth_o  (),

    .clk_rd_i  (clk_out_i),
    .rst_rd_ni (rst_n),
    .rvalid_o  (isck_rdfifo_rvalid),
    .rready_i  (isck_rdfifo_rready),
    .rdata_o   (isck_rdfifo_rdata),
    .rdepth_o  (isck_rdfifo_rdepth)

  );

  // Logic Not Used
  logic unused_logic;
  assign unused_logic = ^{ sck_cmdaddr_wready,
                           sck_cmdaddr_wdepth,
                           sck_wrfifo_wready
                         };

  ///////////////
  // Assertion //
  ///////////////

  // Parameters
  `ASSERT_INIT(CmdPowerof2_A,  CmdAddrFifoDepth  == 2**$clog2(CmdAddrFifoDepth))
  `ASSERT_INIT(RdPowerof2_A,   RdFifoDepth       == 2**$clog2(RdFifoDepth))
  // Write FIFO: should be in the range of TPM spec supported (4B, 8B, 32B, 64B)
  // Read FIFO can have more flexible size as SW can push more bytes in
  // a transaction.
  `ASSERT_INIT(WrDepthSpec_A, WrFifoDepth inside {4, 8, 32, 64})

  `ASSERT_INIT(DataFifoLessThan64_A, RdFifoDepth <= 64)

  `ASSERT_INIT(TpmRegSizeMatch_A, TpmRegisterSize == $bits(tpm_reg_t))

  // CMDADDR buffer should be available, if not, at least error to be propagated
  `ASSERT(CmdAddrAvailable_A,
          sck_cmdaddr_wvalid |-> sck_cmdaddr_wready,
          clk_in_i, !rst_n)

  // When a byte is being pushed to WrFifo, the FIFO should have a space
  `ASSERT(WrFifoAvailable_A,
          sck_wrfifo_wvalid |-> sck_wrfifo_wready,
          clk_in_i, !rst_n)

  // If the command and the address have been shifted, the Locality, command
  // type should be matched with the shifted register.
  `ASSERT(CmdAddrInfo_A,
          $fell(cmdaddr_shift_en) && !csb_i && sys_clk_tpm_cfg.tpm_en && is_tpm_reg |->
            (locality == sck_cmdaddr_wdata_q[15:12]) &&
            (cmd_type == sck_cmdaddr_wdata_q[31]),
          clk_in_i, !rst_n)

  // The condition of tpm_reg check
  `ASSERT(TpmRegCondition_A,
          check_tpm_reg |-> (cmdaddr_bitcnt == 5'h F),
          clk_in_i, !rst_n)

  // when latch_locality, the address should have 16 bits received.
  `ASSERT(LocalityLatchCondition_A,
          latch_locality |-> (cmdaddr_bitcnt == 5'h 13),
          clk_in_i, !rst_n)

  // when check_hw_reg is set, the address should have a word size
  `ASSERT(HwRegCondition_A,
          check_hw_reg |-> (cmdaddr_bitcnt == 5'h 1D),
          clk_in_i, !rst_n)

  // If is_hw_reg set, then it should be FIFO reg and within locality
  `ASSERT(HwRegCondition2_a,
          $rose(is_hw_reg) |->
            is_tpm_reg && !invalid_locality && !sys_clk_tpm_cfg.hw_reg_dis,
          clk_in_i, !rst_n)

  // If module returns data in StAddr, the cmdaddr_bitcount should be the last
  // byte
  `ASSERT(CmdAddrBitCntInAddrSt_A,
          (sck_st_q == StAddr) && sck_p2s_valid |-> (cmdaddr_bitcnt inside {[23:31]}),
          clk_in_i, !rst_n)

endmodule : spi_tpm
