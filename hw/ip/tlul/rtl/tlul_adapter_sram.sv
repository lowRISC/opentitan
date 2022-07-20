// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

/**
 * Tile-Link UL adapter for SRAM-like devices
 *
 * - Intentionally omitted BaseAddr in case of multiple memory maps are used in a SoC,
 *   it means that aliasing can happen if target device size in TL-UL crossbar is bigger
 *   than SRAM size
 * - At most one of EnableDataIntgGen / EnableDataIntgPt can be enabled. However it
 *   possible for both to be disabled.
 *   A module can neither generate an integrity response nor pass through any pre-existing
 *   integrity.  This might be the case for non-security critical memories where there is
 *   no stored integrity AND another entity upstream is already generating returning integrity.
 *   There is however no case where EnableDataIntgGen and EnableDataIntgPt are both true.
 */
module tlul_adapter_sram
  import tlul_pkg::*;
  import prim_mubi_pkg::mubi4_t;
#(
  parameter int SramAw            = 12,
  parameter int SramDw            = 32, // Must be multiple of the TL width
  parameter int Outstanding       = 1,  // Only one request is accepted
  parameter bit ByteAccess        = 1,  // 1: Enables sub-word write transactions. Note that this
                                        //    results in read-modify-write operations for integrity
                                        //    re-generation if EnableDataIntgPt is set to 1.
  parameter bit ErrOnWrite        = 0,  // 1: Writes not allowed, automatically error
  parameter bit ErrOnRead         = 0,  // 1: Reads not allowed, automatically error
  parameter bit CmdIntgCheck      = 0,  // 1: Enable command integrity check
  parameter bit EnableRspIntgGen  = 0,  // 1: Generate response integrity
  parameter bit EnableDataIntgGen = 0,  // 1: Generate response data integrity
  parameter bit EnableDataIntgPt  = 0,  // 1: Passthrough command/response data integrity
  parameter bit SecFifoPtr        = 0,  // 1: Duplicated fifo pointers
  localparam int WidthMult        = SramDw / top_pkg::TL_DW,
  localparam int IntgWidth        = tlul_pkg::DataIntgWidth * WidthMult,
  localparam int DataOutW         = EnableDataIntgPt ? SramDw + IntgWidth : SramDw
) (
  input   clk_i,
  input   rst_ni,

  // TL-UL interface
  input   tl_h2d_t          tl_i,
  output  tl_d2h_t          tl_o,

  // control interface
  input   mubi4_t en_ifetch_i,

  // SRAM interface
  output logic                req_o,
  output mubi4_t              req_type_o,
  input                       gnt_i,
  output logic                we_o,
  output logic [SramAw-1:0]   addr_o,
  output logic [DataOutW-1:0] wdata_o,
  output logic [DataOutW-1:0] wmask_o,
  output logic                intg_error_o,
  input        [DataOutW-1:0] rdata_i,
  input                       rvalid_i,
  input        [1:0]          rerror_i // 2 bit error [1]: Uncorrectable, [0]: Correctable
);

  localparam int SramByte = SramDw/8;
  localparam int DataBitWidth = prim_util_pkg::vbits(SramByte);
  localparam int WoffsetWidth = (SramByte == top_pkg::TL_DBW) ? 1 :
                                DataBitWidth - prim_util_pkg::vbits(top_pkg::TL_DBW);

  logic error_det; // Internal protocol error checker
  logic error_internal; // Internal protocol error checker
  logic wr_attr_error;
  logic instr_error;
  logic wr_vld_error;
  logic rd_vld_error;
  logic rsp_fifo_error;
  logic intg_error;
  logic tlul_error;

  // integrity check
  if (CmdIntgCheck) begin : gen_cmd_intg_check
    tlul_cmd_intg_chk u_cmd_intg_chk (
      .tl_i(tl_i),
      .err_o (intg_error)
    );
  end else begin : gen_no_cmd_intg_check
    assign intg_error = '0;
  end

  // permanently latch integrity error until reset
  logic intg_error_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      intg_error_q <= '0;
    end else if (intg_error || rsp_fifo_error) begin
      intg_error_q <= 1'b1;
    end
  end

  // integrity error output is permanent and should be used for alert generation
  // or other downstream effects
  assign intg_error_o = intg_error | rsp_fifo_error | intg_error_q;

  // wr_attr_error: Check if the request size, mask are permitted.
  //    Basic check of size, mask, addr align is done in tlul_err module.
  //    Here it checks any partial write if ByteAccess isn't allowed.
  assign wr_attr_error = (tl_i.a_opcode == PutFullData || tl_i.a_opcode == PutPartialData)
                         ? ((ByteAccess == 0) ?
                           (tl_i.a_mask != '1 || tl_i.a_size != 2'h2) : 1'b0)
                           : 1'b0;

  // An instruction type transaction is only valid if en_ifetch is enabled
  // If the instruction type is completely invalid, also considered an instruction error
  assign instr_error = prim_mubi_pkg::mubi4_test_invalid(tl_i.a_user.instr_type) |
                       (prim_mubi_pkg::mubi4_test_true_strict(tl_i.a_user.instr_type) &
                        prim_mubi_pkg::mubi4_test_false_loose(en_ifetch_i));

  if (ErrOnWrite == 1) begin : gen_no_writes
    assign wr_vld_error = tl_i.a_opcode != Get;
  end else begin : gen_writes_allowed
    assign wr_vld_error = 1'b0;
  end

  if (ErrOnRead == 1) begin: gen_no_reads
    assign rd_vld_error = tl_i.a_opcode == Get;
  end else begin : gen_reads_allowed
    assign rd_vld_error = 1'b0;
  end

  // tlul protocol check
  tlul_err u_err (
    .clk_i,
    .rst_ni,
    .tl_i(tl_i),
    .err_o (tlul_error)
  );

  // error return is transactional and thus does not used the "latched" intg_err signal
  assign error_det = wr_attr_error | wr_vld_error | rd_vld_error | instr_error |
                     tlul_error    | intg_error;

  // from sram_byte to adapter logic
  tl_h2d_t tl_i_int;
  // from adapter logic to sram_byte
  tl_d2h_t tl_o_int;
  // from sram_byte to rsp_gen
  tl_d2h_t tl_out;

  // not all parts of tl_i_int are used
  logic unused_tl_i_int;
  assign unused_tl_i_int = ^tl_i_int;

  tlul_rsp_intg_gen #(
    .EnableRspIntgGen(EnableRspIntgGen),
    .EnableDataIntgGen(EnableDataIntgGen)
  ) u_rsp_gen (
    .tl_i(tl_out),
    .tl_o
  );

  // byte handling for integrity
  tlul_sram_byte #(
    .EnableIntg(ByteAccess & EnableDataIntgPt & !ErrOnWrite),
    .Outstanding(Outstanding)
  ) u_sram_byte (
    .clk_i,
    .rst_ni,
    .tl_i,
    .tl_o(tl_out),
    .tl_sram_o(tl_i_int),
    .tl_sram_i(tl_o_int),
    .error_i(error_det),
    .error_o(error_internal)
  );

  typedef struct packed {
    logic [top_pkg::TL_DBW-1:0] mask ; // Byte mask within the TL-UL word
    logic [WoffsetWidth-1:0]    woffset ; // Offset of the TL-UL word within the SRAM word
  } sram_req_t ;

  typedef enum logic [1:0] {
    OpWrite,
    OpRead,
    OpUnknown
  } req_op_e ;

  typedef struct packed {
    req_op_e                    op ;
    logic                       error ;
    prim_mubi_pkg::mubi4_t      instr_type;
    logic [top_pkg::TL_SZW-1:0] size ;
    logic [top_pkg::TL_AIW-1:0] source ;
  } req_t ;

  typedef struct packed {
    logic [top_pkg::TL_DW-1:0] data ;
    logic [DataIntgWidth-1:0]  data_intg ;
    logic                      error ;
  } rsp_t ;

  localparam int SramReqFifoWidth = $bits(sram_req_t) ;
  localparam int ReqFifoWidth = $bits(req_t) ;
  localparam int RspFifoWidth = $bits(rsp_t) ;

  // FIFO signal in case OutStand is greater than 1
  // If request is latched, {write, source} is pushed to req fifo.
  // Req fifo is popped when D channel is acknowledged (v & r)
  // D channel valid is asserted if it is write request or rsp fifo not empty if read.
  logic reqfifo_wvalid, reqfifo_wready;
  logic reqfifo_rvalid, reqfifo_rready;
  req_t reqfifo_wdata,  reqfifo_rdata;

  logic sramreqfifo_wvalid, sramreqfifo_wready;
  logic sramreqfifo_rready;
  sram_req_t sramreqfifo_wdata, sramreqfifo_rdata;

  logic rspfifo_wvalid, rspfifo_wready;
  logic rspfifo_rvalid, rspfifo_rready;
  rsp_t rspfifo_wdata,  rspfifo_rdata;

  logic a_ack, d_ack, sram_ack;
  assign a_ack    = tl_i_int.a_valid & tl_o_int.a_ready ;
  assign d_ack    = tl_o_int.d_valid & tl_i_int.d_ready ;
  assign sram_ack = req_o        & gnt_i ;

  // Valid handling
  logic d_valid, d_error;
  always_comb begin
    d_valid = 1'b0;

    if (reqfifo_rvalid) begin
      if (reqfifo_rdata.error) begin
        // Return error response. Assume no request went out to SRAM
        d_valid = 1'b1;
      end else if (reqfifo_rdata.op == OpRead) begin
        d_valid = rspfifo_rvalid;
      end else begin
        // Write without error
        d_valid = 1'b1;
      end
    end else begin
      d_valid = 1'b0;
    end
  end



  always_comb begin
    d_error = 1'b0;

    if (reqfifo_rvalid) begin
      if (reqfifo_rdata.op == OpRead) begin
        d_error = rspfifo_rdata.error | reqfifo_rdata.error;
      end else begin
        d_error = reqfifo_rdata.error;
      end
    end else begin
      d_error = 1'b0;
    end
  end

  logic vld_rd_rsp;
  assign vld_rd_rsp = d_valid & reqfifo_rvalid & rspfifo_rvalid & (reqfifo_rdata.op == OpRead);
  // If the response data is not valid, we set it to an illegal blanking value which is determined
  // by whether the current transaction is an instruction fetch or a regular read operation.
  logic [top_pkg::TL_DW-1:0] error_blanking_data;
  assign error_blanking_data = (prim_mubi_pkg::mubi4_test_true_strict(reqfifo_rdata.instr_type)) ?
                                 DataWhenInstrError :
                                 DataWhenError;

  // Since DataWhenInstrError and DataWhenError can be arbitrary parameters
  // we statically calculate the correct integrity values for these parameters here so that
  // they do not have to be supplied externally.
  logic [top_pkg::TL_DW-1:0] unused_instr, unused_data;
  logic [DataIntgWidth-1:0] error_instr_integ, error_data_integ;
  tlul_data_integ_enc u_tlul_data_integ_enc_instr (
    .data_i(DataMaxWidth'(DataWhenInstrError)),
    .data_intg_o({error_instr_integ, unused_instr})
  );
  tlul_data_integ_enc u_tlul_data_integ_enc_data (
    .data_i(DataMaxWidth'(DataWhenError)),
    .data_intg_o({error_data_integ, unused_data})
  );

  logic [DataIntgWidth-1:0] error_blanking_integ;
  assign error_blanking_integ = (prim_mubi_pkg::mubi4_test_true_strict(reqfifo_rdata.instr_type)) ?
                                 error_instr_integ :
                                 error_data_integ;

  logic [top_pkg::TL_DW-1:0] d_data;
  assign d_data = (vld_rd_rsp & ~d_error) ? rspfifo_rdata.data   // valid read
                                          : error_blanking_data; // write or TL-UL error

  // If this a write response with data fields set to 0, we have to set all ECC bits correctly
  // since we are using an inverted Hsiao code.
  logic [DataIntgWidth-1:0] data_intg;
  assign data_intg = (vld_rd_rsp && reqfifo_rdata.error) ? error_blanking_integ    : // TL-UL error
                     (vld_rd_rsp)                        ? rspfifo_rdata.data_intg : // valid read
                     prim_secded_pkg::SecdedInv3932ZeroEcc;                          // valid write

  assign tl_o_int = '{
      d_valid  : d_valid ,
      d_opcode : (d_valid && reqfifo_rdata.op != OpRead) ? AccessAck : AccessAckData,
      d_param  : '0,
      d_size   : (d_valid) ? reqfifo_rdata.size : '0,
      d_source : (d_valid) ? reqfifo_rdata.source : '0,
      d_sink   : 1'b0,
      d_data   : d_data,
      d_user   : '{default: '0, data_intg: data_intg},
      d_error  : d_valid && d_error,
      a_ready  : (gnt_i | error_internal) & reqfifo_wready & sramreqfifo_wready
  };

  // a_ready depends on the FIFO full condition and grant from SRAM (or SRAM arbiter)
  // assemble response, including read response, write response, and error for unsupported stuff

  // Output to SRAM:
  //    Generate request only when no internal error occurs. If error occurs, the request should be
  //    dropped and returned error response to the host. So, error to be pushed to reqfifo.
  //    In this case, it is assumed the request is granted (may cause ordering issue later?)
  assign req_o      = tl_i_int.a_valid & reqfifo_wready & ~error_internal;
  assign req_type_o = tl_i_int.a_user.instr_type;
  assign we_o       = tl_i_int.a_valid & (tl_i_int.a_opcode inside {PutFullData, PutPartialData});
  assign addr_o     = (tl_i_int.a_valid) ? tl_i_int.a_address[DataBitWidth+:SramAw] : '0;

  // Support SRAMs wider than the TL-UL word width by mapping the parts of the
  // TL-UL address which are more fine-granular than the SRAM width to the
  // SRAM write mask.
  logic [WoffsetWidth-1:0] woffset;
  if (top_pkg::TL_DW != SramDw) begin : gen_wordwidthadapt
    assign woffset = tl_i_int.a_address[DataBitWidth-1:prim_util_pkg::vbits(top_pkg::TL_DBW)];
  end else begin : gen_no_wordwidthadapt
    assign woffset = '0;
  end

  // The size of the data/wmask depends on whether passthrough integrity is enabled.
  // If passthrough integrity is enabled, the data is concatenated with the integrity passed through
  // the user bits.  Otherwise, it is the data only.
  localparam int DataWidth = EnableDataIntgPt ? top_pkg::TL_DW + DataIntgWidth : top_pkg::TL_DW;

  // Final combined wmask / wdata
  logic [WidthMult-1:0][DataWidth-1:0] wmask_combined;
  logic [WidthMult-1:0][DataWidth-1:0] wdata_combined;

  // Original tlul portion
  logic [WidthMult-1:0][top_pkg::TL_DW-1:0] wmask_int;
  logic [WidthMult-1:0][top_pkg::TL_DW-1:0] wdata_int;

  // Integrity portion
  logic [WidthMult-1:0][DataIntgWidth-1:0] wmask_intg;
  logic [WidthMult-1:0][DataIntgWidth-1:0] wdata_intg;

  always_comb begin
    wmask_int = '0;
    wdata_int = '0;

    if (tl_i_int.a_valid) begin
      for (int i = 0 ; i < top_pkg::TL_DW/8 ; i++) begin
        wmask_int[woffset][8*i +: 8] = {8{tl_i_int.a_mask[i]}};
        wdata_int[woffset][8*i +: 8] = (tl_i_int.a_mask[i] && we_o) ? tl_i_int.a_data[8*i+:8] : '0;
      end
    end
  end

  always_comb begin
    wmask_intg  = '0;
    wdata_intg  = '0;

    if (tl_i_int.a_valid) begin
      wmask_intg[woffset] = {DataIntgWidth{1'b1}};
      wdata_intg[woffset] = tl_i_int.a_user.data_intg;
    end
  end

  for (genvar i = 0; i < WidthMult; i++) begin : gen_write_output
    if (EnableDataIntgPt) begin : gen_combined_output
      assign wmask_combined[i] = {wmask_intg[i], wmask_int[i]};
      assign wdata_combined[i] = {wdata_intg[i], wdata_int[i]};
    end else begin : gen_ft_output
      logic unused_w;
      assign wmask_combined[i] = wmask_int[i];
      assign wdata_combined[i] = wdata_int[i];
      assign unused_w = |wmask_intg & |wdata_intg;
    end
  end

  assign wmask_o = wmask_combined;
  assign wdata_o = wdata_combined;

  assign reqfifo_wvalid = a_ack ; // Push to FIFO only when granted
  assign reqfifo_wdata  = '{
    op:     (tl_i_int.a_opcode != Get) ? OpWrite : OpRead, // To return AccessAck for opcode error
    error:  error_internal,
    instr_type: tl_i_int.a_user.instr_type,
    size:   tl_i_int.a_size,
    source: tl_i_int.a_source
  }; // Store the request only. Doesn't have to store data
  assign reqfifo_rready = d_ack ;

  // push together with ReqFIFO, pop upon returning read
  assign sramreqfifo_wdata = '{
    mask    : tl_i_int.a_mask,
    woffset : woffset
  };
  assign sramreqfifo_wvalid = sram_ack & ~we_o;
  assign sramreqfifo_rready = rspfifo_wvalid;

  assign rspfifo_wvalid = rvalid_i & reqfifo_rvalid;

  // Make sure only requested bytes are forwarded
  logic [WidthMult-1:0][DataWidth-1:0] rdata_reshaped;
  logic [DataWidth-1:0] rdata_tlword;

  // This just changes the array format so that the correct word can be selected by indexing.
  assign rdata_reshaped = rdata_i;

  if (EnableDataIntgPt) begin : gen_no_rmask
    always_comb begin
      // If the read mask is set to zero, all read data is zeroed out by the mask.
      // We have to set the ECC bits accordingly since we are using an inverted Hsiao code.
      rdata_tlword = prim_secded_pkg::SecdedInv3932ZeroWord;
      // Otherwise, if at least one mask bit is nonzero, we are passing through the integrity.
      // In that case we need to feed back the entire word since otherwise the integrity
      // will not calculate correctly.
      if (|sramreqfifo_rdata.mask) begin
        // Select correct word.
        rdata_tlword = rdata_reshaped[sramreqfifo_rdata.woffset];
      end
    end
  end else begin : gen_rmask
    logic [DataWidth-1:0] rmask;
    always_comb begin
      rmask = '0;
      for (int i = 0 ; i < top_pkg::TL_DW/8 ; i++) begin
        rmask[8*i +: 8] = {8{sramreqfifo_rdata.mask[i]}};
      end
    end
    // Select correct word and mask it.
    assign rdata_tlword = rdata_reshaped[sramreqfifo_rdata.woffset] & rmask;
  end

  assign rspfifo_wdata  = '{
    data      : rdata_tlword[top_pkg::TL_DW-1:0],
    data_intg : EnableDataIntgPt ? rdata_tlword[DataWidth-1 -: DataIntgWidth] : '0,
    error     : rerror_i[1] // Only care for Uncorrectable error
  };
  assign rspfifo_rready = (reqfifo_rdata.op == OpRead & ~reqfifo_rdata.error)
                        ? reqfifo_rready : 1'b0 ;

  // This module only cares about uncorrectable errors.
  logic unused_rerror;
  assign unused_rerror = rerror_i[0];

  // FIFO instance: REQ, RSP

  // ReqFIFO is to store the Access type to match to the Response data.
  //    For instance, SRAM accepts the write request but doesn't return the
  //    acknowledge. In this case, it may be hard to determine when the D
  //    response for the write data should send out if reads/writes are
  //    interleaved. So, to make it in-order (even TL-UL allows out-of-order
  //    responses), storing the request is necessary. And if the read entry
  //    is write op, it is safe to return the response right away. If it is
  //    read reqeust, then D response is waiting until read data arrives.
  prim_fifo_sync #(
    .Width   (ReqFifoWidth),
    .Pass    (1'b0),
    .Depth   (Outstanding)
  ) u_reqfifo (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(reqfifo_wvalid),
    .wready_o(reqfifo_wready),
    .wdata_i (reqfifo_wdata),
    .rvalid_o(reqfifo_rvalid),
    .rready_i(reqfifo_rready),
    .rdata_o (reqfifo_rdata),
    .full_o  (),
    .depth_o (),
    .err_o   ()
  );

  // sramreqfifo:
  //    While the ReqFIFO holds the request until it is sent back via TL-UL, the
  //    sramreqfifo only needs to hold the mask and word offset until the read
  //    data returns from memory.
  prim_fifo_sync #(
    .Width   (SramReqFifoWidth),
    .Pass    (1'b0),
    .Depth   (Outstanding)
  ) u_sramreqfifo (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(sramreqfifo_wvalid),
    .wready_o(sramreqfifo_wready),
    .wdata_i (sramreqfifo_wdata),
    .rvalid_o(),
    .rready_i(sramreqfifo_rready),
    .rdata_o (sramreqfifo_rdata),
    .full_o  (),
    .depth_o (),
    .err_o   ()
  );

  // Rationale having #Outstanding depth in response FIFO.
  //    In normal case, if the host or the crossbar accepts the response data,
  //    response FIFO isn't needed. But if in any case it has a chance to be
  //    back pressured, the response FIFO should store the returned data not to
  //    lose the data from the SRAM interface. Remember, SRAM interface doesn't
  //    have back-pressure signal such as read_ready.
  prim_fifo_sync #(
    .Width   (RspFifoWidth),
    .Pass    (1'b1),
    .Depth   (Outstanding),
    .Secure  (SecFifoPtr)
  ) u_rspfifo (
    .clk_i,
    .rst_ni,
    .clr_i   (1'b0),
    .wvalid_i(rspfifo_wvalid),
    .wready_o(rspfifo_wready),
    .wdata_i (rspfifo_wdata),
    .rvalid_o(rspfifo_rvalid),
    .rready_i(rspfifo_rready),
    .rdata_o (rspfifo_rdata),
    .full_o  (),
    .depth_o (),
    .err_o   (rsp_fifo_error)
  );

  // below assertion fails when SRAM rvalid is asserted even though ReqFifo is empty
  `ASSERT(rvalidHighReqFifoEmpty, rvalid_i |-> reqfifo_rvalid)

  // below assertion fails when outstanding value is too small (SRAM rvalid is asserted
  // even though the RspFifo is full)
  `ASSERT(rvalidHighWhenRspFifoFull, rvalid_i |-> rspfifo_wready)

  // If both ErrOnWrite and ErrOnRead are set, this block is useless
  `ASSERT_INIT(adapterNoReadOrWrite, (ErrOnWrite & ErrOnRead) == 0)

  `ASSERT_INIT(SramDwHasByteGranularity_A, SramDw % 8 == 0)
  `ASSERT_INIT(SramDwIsMultipleOfTlulWidth_A, SramDw % top_pkg::TL_DW == 0)

  // These parameter options cannot both be true at the same time
  `ASSERT_INIT(DataIntgOptions_A, ~(EnableDataIntgGen & EnableDataIntgPt))

  // make sure outputs are defined
  `ASSERT_KNOWN(TlOutKnown_A,    tl_o.d_valid)
  `ASSERT_KNOWN_IF(TlOutPayloadKnown_A, tl_o, tl_o.d_valid)
  `ASSERT_KNOWN(ReqOutKnown_A,   req_o  )
  `ASSERT_KNOWN(WeOutKnown_A,    we_o   )
  `ASSERT_KNOWN(AddrOutKnown_A,  addr_o )
  `ASSERT_KNOWN(WdataOutKnown_A, wdata_o)
  `ASSERT_KNOWN(WmaskOutKnown_A, wmask_o)

endmodule
