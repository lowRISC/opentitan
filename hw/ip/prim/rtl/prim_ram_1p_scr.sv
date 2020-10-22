// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// This is a draft implementation of a low-latency memory scrambling mechanism.
//
// The module is implemented as a primitive, in the same spirit as similar prim_ram_1p_adv wrappers.
// Hence, it can be conveniently instantiated by comportable IPs (such as OTBN) or in top_earlgrey
// for the main system memory.
//
// The currently implemented architecture uses a reduced-round PRINCE cipher primitive in CTR mode
// in order to (weakly) scramble the data written to the memory macro. Plain CTR mode does not
// diffuse the data since the keystream is just XOR'ed onto it, hence we also we perform Byte-wise
// diffusion using a (shallow) substitution/permutation network layers in order to provide a limited
// avalanche effect within a Byte.
//
// In order to break the linear addressing space, the address is passed through a bijective
// scrambling function constructed using a (shallow) substitution/permutation and a nonce. Due to
// that nonce, the address mapping is not fully baked into RTL and can be changed at runtime as
// well.
//
// See also: prim_cipher_pkg, prim_prince

`include "prim_assert.sv"

module prim_ram_1p_scr #(
  parameter  int Depth                = 512, // Needs to be a power of 2 if NumAddrScrRounds > 0.
  parameter  int Width                = 256, // Needs to be Byte aligned for parity
  parameter  int DataBitsPerMask      = 8,   // Currently only 8 is supported
  parameter  int CfgWidth             = 8,   // WTC, RTC, etc

  // Scrambling parameters. Note that this needs to be low-latency, hence we have to keep the
  // amount of cipher rounds low. PRINCE has 5 half rounds in its original form, which corresponds
  // to 2*5 + 1 effective rounds. Setting this to 2 halves this to approximately 5 effective rounds.
  parameter  int NumPrinceRoundsHalf  = 2,   // Number of PRINCE half rounds, can be [1..5]
  // Number of extra intra-Byte diffusion rounds. Setting this to 0 disables intra-Byte diffusion.
  parameter  int NumByteScrRounds     = 2,
  // Number of address scrambling rounds. Setting this to 0 disables address scrambling.
  parameter  int NumAddrScrRounds     = 2,
  // If set to 1, the same 64bit key stream is replicated if the data port is wider than 64bit.
  // If set to 0, the cipher primitive is replicated, and together with a wider nonce input,
  // a unique keystream is generated for the full data width.
  parameter  bit ReplicateKeyStream   = 1'b0,

  // Derived parameters
  localparam int AddrWidth            = prim_util_pkg::vbits(Depth),
  // Depending on the data width, we need to instantiate multiple parallel cipher primitives to
  // create a keystream that is wide enough (PRINCE has a block size of 64bit)
  localparam int NumParScr            = (ReplicateKeyStream) ? 1 : (Width + 63) / 64,
  localparam int NumParKeystr         = (ReplicateKeyStream) ? (Width + 63) / 64 : 1,
  // This is given by the PRINCE cipher primitive. All parallel cipher modules
  // use the same key, but they use a different IV
  localparam int DataKeyWidth         = 128,
  // Each 64 bit scrambling primitive requires a 64bit IV
  localparam int NonceWidth           = 64 * NumParScr
) (
  input                             clk_i,
  input                             rst_ni,

  input        [DataKeyWidth-1:0]   key_i,
  input        [NonceWidth-1:0]     nonce_i,

  // Interface to TL-UL SRAM adapter
  input                             req_i,
  input                             write_i,
  input        [AddrWidth-1:0]      addr_i,
  input        [Width-1:0]          wdata_i,
  input        [Width-1:0]          wmask_i,  // Needs to be Byte-aligned for parity
  output logic [Width-1:0]          rdata_o,
  output logic                      rvalid_o, // Read response (rdata_o) is valid
  output logic [1:0]                rerror_o, // Bit1: Uncorrectable, Bit0: Correctable
  output logic [AddrWidth-1:0]      raddr_o,  // Read address for error reporting.

  // config
  input [CfgWidth-1:0]              cfg_i
);

  //////////////////////
  // Parameter Checks //
  //////////////////////

  // The depth needs to be a power of 2 in case address scrambling is turned on
  `ASSERT_INIT(DepthPow2Check_A, NumAddrScrRounds <= '0 || 2**$clog2(Depth) == Depth)

  /////////////////////////////////////////
  // Pending Write and Address Registers //
  /////////////////////////////////////////

  // Read / write strobes
  logic read_en, write_en;
  assign read_en = req_i & ~write_i;
  assign write_en = req_i & write_i;

  // Writes are delayed by one cycle, such the same keystream generation primitive (prim_prince) can
  // be reused among reads and writes. Note however that with this arrangement, we have to introduce
  // a mechanism to hold a pending write transaction in cases where that transaction is immediately
  // followed by a read. The pending write transaction is written to memory as soon as there is no
  // new read transaction incoming. The latter is a special case, and if that happens, we return the
  // data from the write holding register.
  logic macro_write;
  logic write_pending_d, write_pending_q;
  assign write_pending_d =
      (write_en)                ? 1'b1            : // Set new write request
      (macro_write)             ? 1'b0            : // Clear pending request when writing to memory
                                  write_pending_q;  // Keep pending write request alive

  logic collision_d, collision_q;
  logic [AddrWidth-1:0] waddr_q;
  assign collision_d = read_en & write_pending_q & (addr_i == waddr_q);

  // Macro requests and write strobe
  logic macro_req;
  assign macro_req   = read_en | write_pending_q;
  // We are allowed to write a pending write transaction to the memory if there is no incoming read
  assign macro_write = write_pending_q & ~read_en;

  ////////////////////////
  // Address Scrambling //
  ////////////////////////

  // TODO: check whether this is good enough for our purposes, or whether we should go for something
  // else. Also, we may want to input some secret key material into this function as well.

  // We only select the pending write address in case there is no incoming read transaction.
  logic [AddrWidth-1:0] addr_mux;
  assign addr_mux = (read_en) ? addr_i : waddr_q;

  // This creates a bijective address mapping using a substitution / permutation network.
  logic [AddrWidth-1:0] addr_scr;
  if (NumAddrScrRounds > 0) begin : gen_addr_scr
    prim_subst_perm #(
      .DataWidth ( AddrWidth        ),
      .NumRounds ( NumAddrScrRounds ),
      .Decrypt   ( 0                )
    ) i_prim_subst_perm (
      .data_i ( addr_mux ),
      // Since the counter mode concatenates {nonce_i[NonceWidth-1-AddrWidth:0], addr_i} to form
      // the IV, the upper AddrWidth bits of the nonce are not used and can be used for address
      // scrambling. In cases where N parallel PRINCE blocks are used due to a data
      // width > 64bit, N*AddrWidth nonce bits are left dangling.
      .key_i  ( nonce_i[NonceWidth - 1 : NonceWidth - AddrWidth] ),
      .data_o ( addr_scr )
    );
  end else begin : gen_no_addr_scr
    assign addr_scr = addr_mux;
  end

  // We latch the non-scrambled address for error reporting.
  logic [AddrWidth-1:0] raddr_d, raddr_q;
  assign raddr_d = addr_mux;
  assign raddr_o = raddr_q;

  //////////////////////////////////////////////
  // Keystream Generation for Data Scrambling //
  //////////////////////////////////////////////

  // This encrypts the IV consisting of the nonce and address using the key provided in order to
  // generate the keystream for the data. Note that we instantiate a register halfway within this
  // primitive to balance the delay between request and response side.
  logic [NumParScr*64-1:0] keystream;
  for (genvar k = 0; k < NumParScr; k++) begin : gen_par_scr
    prim_prince #(
      .DataWidth      (64),
      .KeyWidth       (128),
      .NumRoundsHalf  (NumPrinceRoundsHalf),
      .UseOldKeySched (1'b0),
      .HalfwayDataReg (1'b1), // instantiate a register halfway in the primitive
      .HalfwayKeyReg  (1'b0)  // no need to instantiate a key register as the key remains static
    ) u_prim_prince (
      .clk_i,
      .rst_ni,
      .valid_i ( req_i ),
      // The IV is composed of a nonce and the row address
      .data_i  ( {nonce_i[k * (64 - AddrWidth) +: (64 - AddrWidth)], addr_i} ),
      // All parallel scramblers use the same key
      .key_i,
      // Since we operate in counter mode, this can always be set to encryption mode
      .dec_i   ( 1'b0 ),
      // Output keystream to be XOR'ed
      .data_o  ( keystream[k * 64 +: 64] ),
      .valid_o ( )
    );

    // Unread unused bits from keystream
    if (k == NumParKeystr-1 && (Width % 64) > 0) begin : gen_unread_last
      localparam int UnusedWidth = 64 - (Width % 64);
      logic [UnusedWidth-1:0] unused_keystream;
      assign unused_keystream = keystream[(k+1) * 64 - 1 -: UnusedWidth];
    end
  end

  // Replicate keystream if needed
  logic [Width-1:0] keystream_repl;
  assign keystream_repl = Width'({NumParKeystr{keystream}});

  /////////////////////
  // Data Scrambling //
  /////////////////////

  // Data scrambling is a two step process. First, we XOR the write data with the keystream obtained
  // by operating a reduced-round PRINCE cipher in CTR-mode. Then, we diffuse data within each Byte
  // in order to get a limited "avalanche" behavior in case parts of the Bytes are flipped as a
  // result of a malicious attempt to tamper with the data in memory. We perform the diffusion only
  // within Bytes in order to maintain the ability to write individual Bytes. Note that the
  // keystream XOR is performed first for the write path such that it can be performed last for the
  // read path. This allows us to hide a part of the combinational delay of the PRINCE primitive
  // behind the propagation delay of the SRAM macro and the per-Byte diffusion step.

  // Write path. Note that since this does not fan out into the interconnect, the write path is not
  // as critical as the read path below in terms of timing.
  logic [Width-1:0] wdata_scr_d, wdata_scr_q, wdata_q;
  for (genvar k = 0; k < Width/8; k++) begin : gen_diffuse_wdata
    // Apply the keystream first
    logic [7:0] wdata_xor;
    assign wdata_xor = wdata_q[k*8 +: 8] ^ keystream_repl[k*8 +: 8];

    // Byte aligned diffusion using a substitution / permutation network
    prim_subst_perm #(
      .DataWidth ( 8                ),
      .NumRounds ( NumByteScrRounds ),
      .Decrypt   ( 0                )
    ) i_prim_subst_perm (
      .data_i ( wdata_xor             ),
      .key_i  ( '0                    ),
      .data_o ( wdata_scr_d[k*8 +: 8] )
    );
  end

  // Read path. This is timing critical. The keystream XOR operation is performed last in order to
  // hide the combinational delay of the PRINCE primitive behind the propagation delay of the
  // SRAM and the Byte diffusion.
  logic [Width-1:0] rdata_scr, rdata;
  for (genvar k = 0; k < Width/8; k++) begin : gen_undiffuse_rdata
    // Reverse diffusion first
    logic [7:0] rdata_xor;
    prim_subst_perm #(
      .DataWidth ( 8                ),
      .NumRounds ( NumByteScrRounds ),
      .Decrypt   ( 1                )
    ) i_prim_subst_perm (
      .data_i ( rdata_scr[k*8 +: 8]  ),
      .key_i  ( '0                   ),
      .data_o ( rdata_xor            )
    );

    // Apply Keystream, replicate it if needed
    assign rdata[k*8 +: 8] = rdata_xor ^ keystream_repl[k*8 +: 8];
  end

  ////////////////////////////////////////////////
  // Scrambled data register and forwarding mux //
  ////////////////////////////////////////////////

  // This is the scrambled data holding register for pending writes. This is needed in order to make
  // back to back patterns of the form WR -> RD -> WR work:
  //
  // cycle:          0   |  1   | 2   | 3   |
  // incoming op:    WR0 |  RD  | WR1 | -   |
  // prince:         -   |  WR0 | RD  | WR1 |
  // memory op:      -   |  RD  | WR0 | WR1 |
  //
  // The read transaction in cycle 1 interrupts the first write transaction which has already used
  // the PRINCE primitive for scrambling. If this sequence is followed by another write back-to-back
  // in cycle 2, we cannot use the PRINCE primitive a second time for the first write, and hence
  // need an additional holding register that can buffer the scrambled data of the first write in
  // cycle 1.

  // Clear this if we can write the memory in this cycle, otherwise set if there is a pending write
  logic write_scr_pending_d, write_scr_pending_q;
  assign write_scr_pending_d = (macro_write) ? 1'b0 : write_pending_q;
  // Select the correct scrambled word to be written, based on whether the word in the scrambled
  // data holding register is valid or not. Note that the write_scr_q register could in theory be
  // combined with the wdata_q register. We don't do that here for timing reasons, since that would
  // require another read data mux to inject the scrambled data into the read descrambling path.
  logic [Width-1:0] wdata_scr;
  assign wdata_scr = (write_scr_pending_q) ? wdata_scr_q : wdata_scr_d;

  // Output read valid strobe
  logic rvalid_q;
  assign rvalid_o = rvalid_q;

  // In case of a collision, we forward the write data from the unscrambled holding register
  assign rdata_o = (collision_q) ? wdata_q   : // forward pending (unscrambled) write data
                   (rvalid_q)    ? rdata     : // regular reads
                                   '0;         // tie to zero otherwise

  ///////////////
  // Registers //
  ///////////////

  logic [Width-1:0] wmask_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin : p_wdata_buf
    if (!rst_ni) begin
      write_pending_q     <= 1'b0;
      write_scr_pending_q <= 1'b0;
      collision_q         <= 1'b0;
      rvalid_q            <= 1'b0;
      waddr_q             <= '0;
      wdata_q             <= '0;
      wdata_scr_q         <= '0;
      wmask_q             <= '0;
      raddr_q             <= '0;
    end else begin
      write_scr_pending_q <= write_scr_pending_d;
      write_pending_q     <= write_pending_d;
      collision_q         <= collision_d;
      rvalid_q            <= read_en;
      raddr_q             <= raddr_d;
      if (write_en) begin
        waddr_q <= addr_i;
        wmask_q <= wmask_i;
        wdata_q <= wdata_i;
      end
      if (write_scr_pending_d) begin
        wdata_scr_q <= wdata_scr_d;
      end
    end
  end

  //////////////////
  // Memory Macro //
  //////////////////

  prim_ram_1p_adv #(
    .Depth(Depth),
    .Width(Width),
    .DataBitsPerMask(DataBitsPerMask),
    .CfgW(CfgWidth),
    .EnableECC(1'b0),
    .EnableParity(1'b1), // We are using Byte parity
    .EnableInputPipeline(1'b0),
    .EnableOutputPipeline(1'b0)
  ) u_prim_ram_1p_adv (
    .clk_i,
    .rst_ni,
    .req_i    ( macro_req   ),
    .write_i  ( macro_write ),
    .addr_i   ( addr_scr    ),
    .wdata_i  ( wdata_scr   ),
    .wmask_i  ( wmask_q     ),
    .rdata_o  ( rdata_scr   ),
    .rvalid_o ( ),
    .rerror_o,
    .cfg_i
  );

endmodule : prim_ram_1p_scr
