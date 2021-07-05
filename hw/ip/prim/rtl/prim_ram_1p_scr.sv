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
// diffuse the data since the keystream is just XOR'ed onto it, hence we also we perform byte-wise
// diffusion using a (shallow) substitution/permutation network layers in order to provide a limited
// avalanche effect within a byte.
//
// In order to break the linear addressing space, the address is passed through a bijective
// scrambling function constructed using a (shallow) substitution/permutation and a nonce. Due to
// that nonce, the address mapping is not fully baked into RTL and can be changed at runtime as
// well.
//
// See also: prim_cipher_pkg, prim_prince

`include "prim_assert.sv"

module prim_ram_1p_scr import prim_ram_1p_pkg::*; #(
  parameter  int Depth               = 16*1024, // Needs to be a power of 2 if NumAddrScrRounds > 0.
  parameter  int Width               = 32, // Needs to be byte aligned if byte parity is enabled.
  parameter  int DataBitsPerMask     = 8, // Needs to be set to 8 in case of byte parity.
  parameter  bit EnableParity        = 1, // Enable byte parity.

  // Scrambling parameters. Note that this needs to be low-latency, hence we have to keep the
  // amount of cipher rounds low. PRINCE has 5 half rounds in its original form, which corresponds
  // to 2*5 + 1 effective rounds. Setting this to 2 halves this to approximately 5 effective rounds.
  // Number of PRINCE half rounds, can be [1..5]
  parameter  int NumPrinceRoundsHalf = 2,
  // Number of extra diffusion rounds. Setting this to 0 to disable diffusion.
  parameter  int NumDiffRounds       = 2,
  // This parameter governs the block-width of additional diffusion layers.
  // For intra-byte diffusion, set this parameter to 8.
  parameter  int DiffWidth           = DataBitsPerMask,
  // Number of address scrambling rounds. Setting this to 0 disables address scrambling.
  parameter  int NumAddrScrRounds    = 2,
  // If set to 1, the same 64bit key stream is replicated if the data port is wider than 64bit.
  // If set to 0, the cipher primitive is replicated, and together with a wider nonce input,
  // a unique keystream is generated for the full data width.
  parameter  bit ReplicateKeyStream  = 1'b0,
  // Width of lfsr seed used for random init
  parameter  int LfsrWidth           = 8,
  parameter logic [LfsrWidth-1:0][$clog2(LfsrWidth)-1:0] StatePerm = {
    24'h988eab
  },
  // Derived parameters
  localparam int AddrWidth           = prim_util_pkg::vbits(Depth),
  // Depending on the data width, we need to instantiate multiple parallel cipher primitives to
  // create a keystream that is wide enough (PRINCE has a block size of 64bit)
  localparam int NumParScr           = (ReplicateKeyStream) ? 1 : (Width + 63) / 64,
  localparam int NumParKeystr        = (ReplicateKeyStream) ? (Width + 63) / 64 : 1,
  // This is given by the PRINCE cipher primitive. All parallel cipher modules
  // use the same key, but they use a different IV
  localparam int DataKeyWidth        = 128,
  // Each 64 bit scrambling primitive requires a 64bit IV
  localparam int NonceWidth          = 64 * NumParScr
) (
  input                             clk_i,
  input                             rst_ni,

  // Key interface. Memory requests will not be granted if key_valid is set to 0.
  input                             key_valid_i,
  input        [DataKeyWidth-1:0]   key_i,
  input        [NonceWidth-1:0]     nonce_i,
  input        [LfsrWidth-1:0]      init_seed_i,
  input                             init_req_i,
  output logic                      init_ack_o,

  // Interface to TL-UL SRAM adapter
  input                             req_i,
  output logic                      gnt_o,
  input                             write_i,
  input        [AddrWidth-1:0]      addr_i,
  input        [Width-1:0]          wdata_i,
  input        [Width-1:0]          wmask_i,  // Needs to be byte-aligned for parity
  // The incoming transaction contains an integrity error and the module should alter
  // its behavior appropriately.
  // On integrity errors, the primitive reverses the bit-order of the nonce and surpresses
  // any real transaction to the memory.
  input                             intg_error_i,
  output logic [Width-1:0]          rdata_o,
  output logic                      rvalid_o, // Read response (rdata_o) is valid
  output logic [1:0]                rerror_o, // Bit1: Uncorrectable, Bit0: Correctable
  output logic [31:0]               raddr_o,  // Read address for error reporting.
  output logic                      intg_error_o,

  // config
  input ram_1p_cfg_t                cfg_i
);

  //////////////////////
  // Parameter Checks //
  //////////////////////

  // The depth needs to be a power of 2 in case address scrambling is turned on
  `ASSERT_INIT(DepthPow2Check_A, NumAddrScrRounds <= '0 || 2**$clog2(Depth) == Depth)
  `ASSERT_INIT(DiffWidthMinimum_A, DiffWidth >= 4)
  `ASSERT_INIT(DiffWidthWithParity_A, EnableParity && (DiffWidth == 8) || !EnableParity)

  //////////////////////////////
  // Integrity error latching //
  //////////////////////////////

  logic intg_err_q;
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      intg_err_q <= '0;
    end else if (intg_error_i) begin
      intg_err_q <= 1'b1;
    end
  end

  prim_buf u_intg_err_out (
    .in_i(intg_error_i | intg_err_q),
    .out_o(intg_error_o)
  );

  ///////////////////////////
  // Lfsr for random init  //
  ///////////////////////////

  logic init_req_q, load_seed;
  logic [AddrWidth-1:0] addr_cnt_q;
  logic [LfsrWidth-1:0] lfsr_out;
  logic init_sel;

  // input muxed addr/data/mask
  logic [AddrWidth-1:0] addr;
  logic [Width-1:0] wdata;
  logic [Width-1:0] wmask;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      init_req_q <= '0;
    end else begin
      init_req_q <= init_req_i;
    end
  end

  assign load_seed = init_req_i & ~init_req_q;

  prim_lfsr #(
    .LfsrDw(LfsrWidth),
    .StateOutDw(LfsrWidth),
    .StatePermEn(1'b0),
    .StatePerm(StatePerm)
  ) u_lfsr (
    .clk_i,
    .rst_ni,
    .lfsr_en_i(init_req_i),
    .seed_en_i(load_seed),
    .seed_i(init_seed_i),
    .entropy_i('0),
    .state_o(lfsr_out)
  );

  // TODO: Need to harden these counters long term
  assign init_ack_o = init_req_q && addr_cnt_q == Depth - 1;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      addr_cnt_q <= '0;
    end else if (init_ack_o) begin
      addr_cnt_q <= '0;
    end else if (init_req_q && addr_cnt_q < Depth - 1) begin
      addr_cnt_q <= addr_cnt_q + AddrWidth'(1);
    end
  end

  // The lfsr width and the width of the data may not be completely aligned
  localparam int LfsrMult = (Width % LfsrWidth > 0) ? Width / LfsrWidth + 1 :
                                                      Width / LfsrWidth;
  localparam int FullRandWidth = LfsrMult * LfsrWidth;

  // The random value may be larger than what is needed
  logic [FullRandWidth-1:0] rand_val;
  assign rand_val = {LfsrMult{lfsr_out}};

  if (LfsrMult * LfsrWidth > Width) begin : gen_rand_tieoffs
    logic unused_rand;
    assign unused_rand = ^rand_val[FullRandWidth-1:Width];
  end

  assign init_sel = init_req_q;
  assign addr = init_sel ? addr_cnt_q : addr_i;
  assign wdata = init_sel ? rand_val[Width-1:0] : wdata_i;
  assign wmask = init_sel ? '1 : wmask_i;

  /////////////////////////////////////////
  // Pending Write and Address Registers //
  /////////////////////////////////////////

  // Writes are delayed by one cycle, such the same keystream generation primitive (prim_prince) can
  // be reused among reads and writes. Note however that with this arrangement, we have to introduce
  // a mechanism to hold a pending write transaction in cases where that transaction is immediately
  // followed by a read. The pending write transaction is written to memory as soon as there is no
  // new read transaction incoming. The latter can be a special case if the incoming read goes to
  // the same address as the pending write. To that end, we detect the address collision and return
  // the data from the write holding register.

  // Read / write strobes
  logic read_en, write_en_d, write_en_q;
  assign gnt_o = req_i & key_valid_i & ~init_sel;

  assign read_en = gnt_o & ~write_i;
  assign write_en_d = gnt_o & write_i | init_sel;

  logic write_pending_q;
  logic addr_collision_d, addr_collision_q;
  logic [AddrWidth-1:0] waddr_q;
  assign addr_collision_d = read_en & (write_en_q | write_pending_q) & (addr == waddr_q);

  // Macro requests and write strobe
  // The macro operation is silenced if an integrity error is seen
  logic macro_req;
  logic intg_err_macro_req;
  prim_buf u_intg_err_macro_req (
    .in_i(intg_error_i | intg_err_q),
    .out_o(intg_err_macro_req)
  );
  assign macro_req   = ~intg_err_macro_req & (read_en | write_en_q | write_pending_q);
  // We are allowed to write a pending write transaction to the memory if there is no incoming read
  logic macro_write;
  assign macro_write = (write_en_q | write_pending_q) & ~read_en;
  // New read write collision
  logic rw_collision;
  assign rw_collision = write_en_q & read_en;

  ////////////////////////
  // Address Scrambling //
  ////////////////////////

  // We only select the pending write address in case there is no incoming read transaction.
  logic [AddrWidth-1:0] addr_mux;
  assign addr_mux = (read_en) ? addr : waddr_q;

  // This creates a bijective address mapping using a substitution / permutation network.
  logic [AddrWidth-1:0] addr_scr;
  if (NumAddrScrRounds > 0) begin : gen_addr_scr

    // TODO, expand this into copies with another primitive
    logic intg_err_addr_scr;
    prim_buf u_intg_err_addr_scr (
      .in_i(intg_error_i | intg_err_q),
      .out_o(intg_err_addr_scr)
    );

    // If there is an intergirty error, the nonce used is reversed
    logic [AddrWidth-1:0] addr_scr_nonce;
    for (genvar j = 0; j < AddrWidth; j++) begin : gen_addr_scr_nonce
      assign addr_scr_nonce[j] = intg_err_addr_scr ?
                                 nonce_i[NonceWidth - 1 - j] :
                                 nonce_i[NonceWidth - AddrWidth + j];
    end

    prim_subst_perm #(
      .DataWidth ( AddrWidth        ),
      .NumRounds ( NumAddrScrRounds ),
      .Decrypt   ( 0                )
    ) u_prim_subst_perm (
      .data_i ( addr_mux       ),
      // Since the counter mode concatenates {nonce_i[NonceWidth-1-AddrWidth:0], addr} to form
      // the IV, the upper AddrWidth bits of the nonce are not used and can be used for address
      // scrambling. In cases where N parallel PRINCE blocks are used due to a data
      // width > 64bit, N*AddrWidth nonce bits are left dangling.
      .key_i  ( addr_scr_nonce ),
      .data_o ( addr_scr       )
    );
  end else begin : gen_no_addr_scr
    assign addr_scr = addr_mux;
  end

  // We latch the non-scrambled address for error reporting.
  logic [AddrWidth-1:0] raddr_q;
  assign raddr_o = 32'(raddr_q);

  //////////////////////////////////////////////
  // Keystream Generation for Data Scrambling //
  //////////////////////////////////////////////

  // This encrypts the IV consisting of the nonce and address using the key provided in order to
  // generate the keystream for the data. Note that we instantiate a register halfway within this
  // primitive to balance the delay between request and response side.
  localparam int DataNonceWidth = 64 - AddrWidth;
  logic [NumParScr*64-1:0] keystream;
  logic [NumParScr-1:0][DataNonceWidth-1:0] data_scr_nonce;

  // TODO, expand this into copies with another primitive
  logic intg_err_data_scr;
  prim_buf u_intg_err_data_scr (
    .in_i(intg_error_i | intg_err_q),
    .out_o(intg_err_data_scr)
  );

  for (genvar k = 0; k < NumParScr; k++) begin : gen_par_scr

    for (genvar j = 0; j < DataNonceWidth; j++) begin : gen_data_nonce
      assign data_scr_nonce[k][j] = intg_err_data_scr ?
                                    nonce_i[(k + 1) * DataNonceWidth - j] :
                                    nonce_i[k * DataNonceWidth + j];
    end


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
      .valid_i ( gnt_o ),
      // The IV is composed of a nonce and the row address
      //.data_i  ( {nonce_i[k * (64 - AddrWidth) +: (64 - AddrWidth)], addr} ),
      .data_i  ( {data_scr_nonce[k], addr} ),
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
  // by operating a reduced-round PRINCE cipher in CTR-mode. Then, we diffuse data within each byte
  // in order to get a limited "avalanche" behavior in case parts of the bytes are flipped as a
  // result of a malicious attempt to tamper with the data in memory. We perform the diffusion only
  // within bytes in order to maintain the ability to write individual bytes. Note that the
  // keystream XOR is performed first for the write path such that it can be performed last for the
  // read path. This allows us to hide a part of the combinational delay of the PRINCE primitive
  // behind the propagation delay of the SRAM macro and the per-byte diffusion step.

  logic [Width-1:0] rdata_scr, rdata;
  logic [Width-1:0] wdata_scr_d, wdata_scr_q, wdata_q;
  for (genvar k = 0; k < (Width + DiffWidth - 1) / DiffWidth; k++) begin : gen_diffuse_data
    // If the Width is not divisible by DiffWidth, we need to adjust the width of the last slice.
    localparam int LocalWidth = (Width - k * DiffWidth >= DiffWidth) ? DiffWidth :
                                                                       (Width - k * DiffWidth);

    // Write path. Note that since this does not fan out into the interconnect, the write path is
    // not as critical as the read path below in terms of timing.
    // Apply the keystream first
    logic [LocalWidth-1:0] wdata_xor;
    assign wdata_xor = wdata_q[k*DiffWidth +: LocalWidth] ^
                       keystream_repl[k*DiffWidth +: LocalWidth];

    // Byte aligned diffusion using a substitution / permutation network
    prim_subst_perm #(
      .DataWidth ( LocalWidth       ),
      .NumRounds ( NumDiffRounds ),
      .Decrypt   ( 0                )
    ) u_prim_subst_perm_enc (
      .data_i ( wdata_xor ),
      .key_i  ( '0        ),
      .data_o ( wdata_scr_d[k*DiffWidth +: LocalWidth] )
    );

    // Read path. This is timing critical. The keystream XOR operation is performed last in order to
    // hide the combinational delay of the PRINCE primitive behind the propagation delay of the
    // SRAM and the byte diffusion.
    // Reverse diffusion first
    logic [LocalWidth-1:0] rdata_xor;
    prim_subst_perm #(
      .DataWidth ( LocalWidth       ),
      .NumRounds ( NumDiffRounds ),
      .Decrypt   ( 1                )
    ) u_prim_subst_perm_dec (
      .data_i ( rdata_scr[k*DiffWidth +: LocalWidth] ),
      .key_i  ( '0        ),
      .data_o ( rdata_xor )
    );

    // Apply Keystream, replicate it if needed
    assign rdata[k*DiffWidth +: LocalWidth] = rdata_xor ^
                                              keystream_repl[k*DiffWidth +: LocalWidth];
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

  // Clear this if we can write the memory in this cycle. Set only if the current write cannot
  // proceed due to an incoming read operation.
  logic write_scr_pending_d;
  assign write_scr_pending_d = (macro_write)  ? 1'b0 :
                               (rw_collision) ? 1'b1 :
                                                write_pending_q;

  // Select the correct scrambled word to be written, based on whether the word in the scrambled
  // data holding register is valid or not. Note that the write_scr_q register could in theory be
  // combined with the wdata_q register. We don't do that here for timing reasons, since that would
  // require another read data mux to inject the scrambled data into the read descrambling path.
  logic [Width-1:0] wdata_scr;
  assign wdata_scr = (write_pending_q) ? wdata_scr_q : wdata_scr_d;

  // Output read valid strobe
  logic rvalid_q;
  assign rvalid_o = rvalid_q;

  logic [Width-1:0] wmask_q;
  always_comb begin : p_forward_mux
    rdata_o = '0;
    // regular reads
    if (rvalid_q) begin
      rdata_o = rdata;
    end
    // In case of a collision, we forward the valid bytes of the write data from the unscrambled
    // holding register.
    if (addr_collision_q) begin
      for (int k = 0; k < Width; k++) begin
        if (wmask_q[k]) begin
          rdata_o[k] = wdata_q[k];
        end
      end
    end
  end

  ///////////////
  // Registers //
  ///////////////

  always_ff @(posedge clk_i or negedge rst_ni) begin : p_wdata_buf
    if (!rst_ni) begin
      write_pending_q     <= 1'b0;
      addr_collision_q    <= 1'b0;
      rvalid_q            <= 1'b0;
      write_en_q          <= 1'b0;
      raddr_q             <= '0;
      waddr_q             <= '0;
      wmask_q             <= '0;
      wdata_q             <= '0;
      wdata_scr_q         <= '0;
    end else begin
      write_pending_q     <= write_scr_pending_d;
      addr_collision_q    <= addr_collision_d;
      rvalid_q            <= read_en;
      write_en_q          <= write_en_d;

      if (read_en) begin
        raddr_q           <= addr;
      end
      if (write_en_d) begin
        waddr_q <= addr;
        wmask_q <= wmask;
        wdata_q <= wdata;
      end
      if (rw_collision) begin
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
    .EnableECC(1'b0),
    .EnableParity(EnableParity),
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

  `include "prim_util_get_scramble_params.svh"

endmodule : prim_ram_1p_scr
