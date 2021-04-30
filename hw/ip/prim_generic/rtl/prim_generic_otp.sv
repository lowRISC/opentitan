// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module prim_generic_otp
  import prim_otp_pkg::*;
#(
  // Native OTP word size. This determines the size_i granule.
  parameter  int Width       = 16,
  parameter  int Depth       = 1024,
  // This determines the maximum number of native words that
  // can be transferred accross the interface in one cycle.
  parameter  int SizeWidth   = 2,
  // Width of the power sequencing signal.
  parameter  int PwrSeqWidth = 2,
  // Number of Test TL-UL words
  parameter  int TlDepth     = 16,
  // Derived parameters
  localparam int AddrWidth   = prim_util_pkg::vbits(Depth),
  localparam int IfWidth     = 2**SizeWidth*Width,
  // VMEM file to initialize the memory with
  parameter      MemInitFile = ""
) (
  input                          clk_i,
  input                          rst_ni,
  // Macro-specific power sequencing signals to/from AST
  output logic [PwrSeqWidth-1:0] pwr_seq_o,
  input        [PwrSeqWidth-1:0] pwr_seq_h_i,
  // Test interface
  input  tlul_pkg::tl_h2d_t      test_tl_i,
  output tlul_pkg::tl_d2h_t      test_tl_o,
  // Ready valid handshake for read/write command
  output logic                   ready_o,
  input                          valid_i,
  input [SizeWidth-1:0]          size_i, // #(Native words)-1, e.g. size == 0 for 1 native word.
  input  cmd_e                   cmd_i,  // 00: read command, 01: write command, 11: init command
  input [AddrWidth-1:0]          addr_i,
  input [IfWidth-1:0]            wdata_i,
  // Response channel
  output logic                   valid_o,
  output logic [IfWidth-1:0]     rdata_o,
  output err_e                   err_o,
  // External programming voltage
  inout wire ext_voltage_io, //TODO enable it after the change in prim_otp file
  input ext_voltage_en_i, // TODO
  //// alert indication
  //////////////////////////
  output ast_pkg::ast_dif_t otp_alert_src_o,

  // Scan
  input lc_ctrl_pkg::lc_tx_t scanmode_i,  // Scan Mode input
  input scan_en_i,  // Scan Shift
  input scan_rst_ni  // Scan Reset
);

  // Not supported in open-source emulation model.
  logic [PwrSeqWidth-1:0] unused_pwr_seq_h;
  assign unused_pwr_seq_h = pwr_seq_h_i;
  assign pwr_seq_o = '0;

  wire unused_ext_voltage;
  assign unused_ext_voltage = ext_voltage_io;
  logic unused_ext_voltage_en;
  assign unused_ext_voltage_en = ext_voltage_en_i;

  logic unused_scan;
  assign unused_scan = ^{scanmode_i, scan_en_i, scan_rst_ni};

  assign otp_alert_src_o = '{p: '0, n: '1};

  ////////////////////////////////////
  // TL-UL Test Interface Emulation //
  ////////////////////////////////////

  // Put down a register that can be used to test the TL interface.
  // TODO: this emulation may need to be adjusted, once closed source wrapper is
  // implemented.
  localparam int TlAddrWidth = prim_util_pkg::vbits(TlDepth);
  logic tlul_req, tlul_rvalid_q, tlul_wren;
  logic [TlDepth-1:0][31:0] tlul_regfile_q;
  logic [31:0] tlul_wdata, tlul_rdata_q;
  logic [TlAddrWidth-1:0]  tlul_addr;

  tlul_adapter_sram #(
    .SramAw      ( TlAddrWidth   ),
    .SramDw      ( 32            ),
    .Outstanding ( 1             ),
    .ByteAccess  ( 0             ),
    .ErrOnWrite  ( 0             )
  ) u_tlul_adapter_sram (
    .clk_i,
    .rst_ni,
    .tl_i        ( test_tl_i          ),
    .tl_o        ( test_tl_o          ),
    .en_ifetch_i ( tlul_pkg::InstrDis ),
    .req_o       ( tlul_req           ),
    .gnt_i       ( tlul_req           ),
    .we_o        ( tlul_wren          ),
    .addr_o      ( tlul_addr          ),
    .wdata_o     ( tlul_wdata         ),
    .wmask_o     (                    ),
    .intg_error_o(                    ),
    .rdata_i     ( tlul_rdata_q       ),
    .rvalid_i    ( tlul_rvalid_q      ),
    .rerror_i    ( '0                 ),
    .req_type_o  (                    )
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_tlul_testreg
    if (!rst_ni) begin
      tlul_rvalid_q  <= 1'b0;
      tlul_rdata_q   <= '0;
      tlul_regfile_q <= '0;
    end else begin
      tlul_rvalid_q <= tlul_req & ~tlul_wren;
      if (tlul_req && tlul_wren) begin
        tlul_regfile_q[tlul_addr] <= tlul_wdata;
      end else if (tlul_req && !tlul_wren) begin
        tlul_rdata_q <= tlul_regfile_q[tlul_addr];
      end
    end
  end

  ///////////////////
  // Control logic //
  ///////////////////

  // Encoding generated with ./sparse-fsm-encode.py -d 5 -m 8 -n 10
  // Hamming distance histogram:
  //
  // 0: --
  // 1: --
  // 2: --
  // 3: --
  // 4: --
  // 5: |||||||||||||||||||| (53.57%)
  // 6: ||||||||||||| (35.71%)
  // 7: | (3.57%)
  // 8: || (7.14%)
  // 9: --
  // 10: --
  //
  // Minimum Hamming distance: 5
  // Maximum Hamming distance: 8
  //
  localparam int StateWidth = 10;
  typedef enum logic [StateWidth-1:0] {
    ResetSt      = 10'b1100000011,
    InitSt       = 10'b1100110100,
    IdleSt       = 10'b1010111010,
    ReadSt       = 10'b0011100000,
    ReadWaitSt   = 10'b1001011111,
    WriteCheckSt = 10'b0111010101,
    WriteWaitSt  = 10'b0000001100,
    WriteSt      = 10'b0110101111
  } state_e;

  state_e state_d, state_q;
  err_e err_d, err_q;
  logic valid_d, valid_q;
  logic req, wren, rvalid;
  logic [1:0] rerror;
  logic [Width-1:0] rdata_d;
  logic [2**SizeWidth-1:0][Width-1:0] rdata_q, wdata_q;
  logic [AddrWidth-1:0] addr_q;
  logic [SizeWidth-1:0] size_q;
  logic [SizeWidth-1:0] cnt_d, cnt_q;
  logic cnt_clr, cnt_en;

  assign cnt_d = (cnt_clr) ? '0           :
                 (cnt_en)  ? cnt_q + 1'b1 : cnt_q;

  assign valid_o = valid_q;
  assign rdata_o = rdata_q;
  assign err_o   = err_q;

  always_comb begin : p_fsm
    // Default
    state_d = state_q;
    ready_o = 1'b0;
    valid_d = 1'b0;
    err_d   = err_q;
    req     = 1'b0;
    wren    = 1'b0;
    cnt_clr = 1'b0;
    cnt_en  = 1'b0;

    unique case (state_q)
      // Wait here until we receive an initialization command.
      ResetSt: begin
        err_d = NoError;
        ready_o = 1'b1;
        if (valid_i) begin
          if (cmd_i == Init) begin
            state_d = InitSt;
          end else begin
            // Invalid commands get caught here
            valid_d = 1'b1;
            err_d = MacroError;
          end
        end
      end
      // Wait for some time until the OTP macro is ready.
      InitSt: begin
        state_d = IdleSt;
        valid_d = 1'b1;
        err_d = NoError;
      end
      // In the idle state, we basically wait for read or write commands.
      IdleSt: begin
        ready_o = 1'b1;
        err_d = NoError;
        if (valid_i) begin
          cnt_clr = 1'b1;
          err_d = NoError;
          unique case (cmd_i)
            Read:  state_d = ReadSt;
            Write: state_d = WriteCheckSt;
            default:  begin
              // Invalid commands get caught here
              valid_d = 1'b1;
              err_d = MacroError;
            end
          endcase // cmd_i
        end
      end
      // Issue a read command to the macro.
      ReadSt: begin
        state_d = ReadWaitSt;
        req     = 1'b1;
      end
      // Wait for response from macro.
      ReadWaitSt: begin
        if (rvalid) begin
          cnt_en = 1'b1;
          // Uncorrectable error, bail out.
          if (rerror[1]) begin
            state_d = IdleSt;
            valid_d = 1'b1;
            err_d = MacroEccUncorrError;
          end else begin
            if (cnt_q == size_q) begin
              state_d = IdleSt;
              valid_d = 1'b1;
            end else begin
              state_d = ReadSt;
            end
            // Correctable error, carry on but signal back.
            if (rerror[0]) begin
              err_d = MacroEccCorrError;
            end
          end
        end
      end
      // First, perform a blank check.
      WriteCheckSt: begin
        state_d = WriteWaitSt;
        req     = 1'b1;
      end
      // Wait for readout to complete first.
      // If the write data would clear an already programmed bit, or if we got an uncorrectable
      // ECC error, the check has failed and we abort the write at this point.
      WriteWaitSt: begin
        if (rvalid) begin
          cnt_en = 1'b1;
          // TODO: this blank check needs to be extended to account for the ECC bits as well.
          if (rerror[1] || (rdata_d & wdata_q[cnt_q]) != rdata_d) begin
            state_d = IdleSt;
            valid_d = 1'b1;
            err_d = MacroWriteBlankError;
          end else begin
            if (cnt_q == size_q) begin
              cnt_clr = 1'b1;
              state_d = WriteSt;
            end else begin
              state_d = WriteCheckSt;
            end
          end
        end
      end
      // Now that the write check was successful, we can write all native words in one go.
      WriteSt: begin
        req = 1'b1;
        wren = 1'b1;
        cnt_en = 1'b1;
        if (cnt_q == size_q) begin
          valid_d = 1'b1;
          state_d = IdleSt;
        end
      end
      default: begin
        state_d = ResetSt;
      end
    endcase // state_q
  end

  ///////////////////////////////////////////
  // Emulate using ECC protected Block RAM //
  ///////////////////////////////////////////

  logic [AddrWidth-1:0] addr;
  assign addr = addr_q + AddrWidth'(cnt_q);

  prim_ram_1p_adv #(
    .Depth                (Depth),
    .Width                (Width),
    .MemInitFile          (MemInitFile),
    .EnableECC            (1'b1),
    .EnableInputPipeline  (1),
    .EnableOutputPipeline (1),
    // Use a standard Hamming ECC for OTP.
    .HammingECC           (1)
  ) u_prim_ram_1p_adv (
    .clk_i,
    .rst_ni,
    .req_i    ( req            ),
    .write_i  ( wren           ),
    .addr_i   ( addr           ),
    .wdata_i  ( wdata_q[cnt_q] ),
    .wmask_i  ( {Width{1'b1}}  ),
    .rdata_o  ( rdata_d        ),
    .rvalid_o ( rvalid         ),
    .rerror_o ( rerror         ),
    .cfg_i    ( '0             )
  );

  // Currently it is assumed that no wrap arounds can occur.
  `ASSERT(NoWrapArounds_A, req |-> (addr >= addr_q))

  //////////
  // Regs //
  //////////

  // This primitive is used to place a size-only constraint on the
  // flops in order to prevent FSM state encoding optimizations.
  logic [StateWidth-1:0] state_raw_q;
  assign state_q = state_e'(state_raw_q);
  prim_flop #(
    .Width(StateWidth),
    .ResetValue(StateWidth'(ResetSt))
  ) u_state_regs (
    .clk_i,
    .rst_ni,
    .d_i ( state_d     ),
    .q_o ( state_raw_q )
  );

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_regs
    if (!rst_ni) begin
      valid_q <= '0;
      err_q   <= NoError;
      addr_q  <= '0;
      wdata_q <= '0;
      rdata_q <= '0;
      cnt_q   <= '0;
      size_q  <= '0;
    end else begin
      valid_q <= valid_d;
      err_q   <= err_d;
      cnt_q   <= cnt_d;
      if (ready_o && valid_i) begin
        addr_q  <= addr_i;
        wdata_q <= wdata_i;
        size_q  <= size_i;
      end
      if (rvalid) begin
        rdata_q[cnt_q] <= rdata_d;
      end
    end
  end

endmodule : prim_generic_otp
