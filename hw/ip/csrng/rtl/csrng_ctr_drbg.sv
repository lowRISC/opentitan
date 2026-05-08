// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Implementation of the NIST SP800-90A CTR DRBG algorithm, no derivation function.

`include "prim_assert.sv"

module csrng_ctr_drbg import csrng_pkg::*; (
  input  logic               clk_i,
  input  logic               rst_ni,

  // Global enable
  input  logic               enable_i,

  // Command interface request, arbitrated from command stages
  input  logic               req_vld_i,
  output logic               req_rdy_o,
  input  csrng_core_data_t   req_data_i,
  input  logic [SeedLen-1:0] req_entropy_i,
  input  logic               req_entropy_fips_i,
  input  logic               req_glast_i,

  // Command interface response to state db and command stages
  output logic               state_db_wr_o,
  output logic               rsp_vld_o,
  output csrng_core_data_t   rsp_data_o,
  output csrng_cmd_sts_e     rsp_sts_o,

  // Generated bits output to command stages
  output logic               bits_vld_o,
  output logic  [BlkLen-1:0] bits_data_o,
  output logic               bits_fips_o,

  // Block encrypt interface request
  output logic               block_encrypt_req_vld_o,
  input  logic               block_encrypt_req_rdy_i,
  output csrng_key_v_t       block_encrypt_req_data_o,

  // Block encrypt interface response
  input  logic               block_encrypt_rsp_vld_i,
  output logic               block_encrypt_rsp_rdy_o,
  input  logic  [BlkLen-1:0] block_encrypt_rsp_data_i,

  // Error status outputs
  output logic               ctr_err_o,
  output logic               sm_err_o
);

  import csrng_reg_pkg::NumApps;

  // Number of calls to the block cipher required for each call of UPDate()
  localparam int unsigned NumBlkPerUpd   = SeedLen/BlkLen;
  localparam int unsigned NumBlkPerUpdLg = $clog2(NumBlkPerUpd);

  // The GENerate command consists of up to three sub commands
  typedef enum logic [1:0] {
    UPD_BEGIN,
    GEN_LOOP,
    UPD_FINAL
  } gen_subcmd_e;

  //--------------------------------------------
  // Sparse FSM encoding and instantiation
  //--------------------------------------------

  // Encoding generated with:
  // $ ./util/design/sparse-fsm-encode.py -d 3 -m 8 -n 6 \
  //     -s 923483574589 --language=sv
  //
  // Hamming distance histogram:
  //
  //  0: --
  //  1: --
  //  2: --
  //  3: |||||||||||||||||||| (57.14%)
  //  4: ||||||||||||||| (42.86%)
  //  5: --
  //  6: --
  //
  // Minimum Hamming distance: 3
  // Maximum Hamming distance: 4
  // Minimum Hamming weight: 1
  // Maximum Hamming weight: 5
  //
  localparam int StateWidth = 6;
  typedef enum logic [StateWidth-1:0] {
    Idle       = 6'b101110,
    CtrInc     = 6'b100001,
    ReqSend    = 6'b110100,
    RspWait    = 6'b010111,
    Hndshk     = 6'b001101,
    HndshkGen  = 6'b011000,
    HndshkLoad = 6'b111011,
    Error      = 6'b000010
  } state_e;

  state_e state_q, state_d;

  // SEC_CM: CTR_DRBG.FSM.SPARSE
  `PRIM_FLOP_SPARSE_FSM(u_state_regs, state_d, state_q, state_e, Idle)

  //--------------------------------------------
  // Signals
  //--------------------------------------------

  // Main data structure that encapsulates most of the (meta)data requried in this module
  csrng_core_data_t   core_data;

  // Control and data signals for the v and concat counters
  logic  [BlkLen-1:0] v_ctr_sized;
  logic  [CtrLen-1:0] v_ctr;
  logic               v_ctr_load;
  logic               v_ctr_inc;
  csrng_key_v_t       concat_key_v;
  logic               concat_ctr_inc;
  logic               concat_ctr_done;

  //--------------------------------------------
  // Registers, including sequential process
  //--------------------------------------------

  // adata flops for each app interface, plus one valid bit for each
  // This rather large bank of flops is unfortunately required due to the way that we handle
  // GENerate commands with more than one block of generated output bits: Instead of generating all
  // blocks in one go, we always generate one block and then allow the arbiter to give another app
  // interface access to the data path. However, on the last generated block, we require the adata
  // that are supplied at the very beginning of the GENerate command for the final update() step
  // (compare NIST specification). Since all app interfaces share a single packer for adata, its
  // content can get overwritten after the first block of generated bits, and hence we must buffer
  // adata for each app interface locally for the full "lifetime" of a multi-block GENerate command.
  // TODO(#28153) Find a smaller solution (giving each app interface an unpacker does not help)
  csrng_key_v_t [NumApps-1:0] generate_adata_q, generate_adata_d;
  logic         [NumApps-1:0] generate_adata_vld_q, generate_adata_vld_d;

  // Scratch register for commands that call block_encrypt more than once and pointer into it
  logic        [SeedLen-1:0] concat_key_v_q, concat_key_v_d;
  logic [NumBlkPerUpdLg-1:0] concat_ctr_q, concat_ctr_d;

  // Keep track of current sub command for GENerates
  gen_subcmd_e gen_subcmd_q, gen_subcmd_d;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      generate_adata_q     <= '{default: '0};
      generate_adata_vld_q <= '0;
      concat_ctr_q         <= '0;
      concat_key_v_q       <= '0;
      gen_subcmd_q         <= UPD_BEGIN;
    end else begin
      generate_adata_q     <= generate_adata_d;
      generate_adata_vld_q <= generate_adata_vld_d;
      concat_ctr_q         <= concat_ctr_d;
      concat_key_v_q       <= concat_key_v_d;
      gen_subcmd_q         <= gen_subcmd_d;
    end
  end

  //--------------------------------------------
  // Prepare/mux input values depending on cmd
  //--------------------------------------------

  always_comb begin
    core_data = req_data_i;

    unique case (req_data_i.cmd)
      INS: begin
        // Reset key, v, and reseed counter; inject entropy and FIPS status
        core_data.key    = '0;
        core_data.v      = '0;
        core_data.rs_ctr = '0;
        core_data.pdata  = req_data_i.pdata ^ req_entropy_i;
        core_data.fips   = req_entropy_fips_i;
      end
      RES: begin
        // Reset reseed counter; inject entropy and FIPS status
        core_data.rs_ctr = '0;
        core_data.pdata  = req_data_i.pdata ^ req_entropy_i;
        core_data.fips   = req_entropy_fips_i;
      end
      UPD, GEN: begin
        /* leave everything as-is */
      end
      UNI: begin
        // Set everything to zero
        core_data.key    = '0;
        core_data.v      = '0;
        core_data.rs_ctr = '0;
        core_data.pdata  = '0;
        core_data.fips   = 1'b0;
      end
      default: begin
        // Invalid command, should never happen
        core_data.cmd = INV;
      end
    endcase
  end

  //--------------------------------------------
  // Handling of generate_adata(_vld)
  //--------------------------------------------

  for (genvar i = 0; i < NumApps; i++) begin : g_assign_gen_adata
    logic capt_adata;
    logic clear_adata_vld;
    // 1) Write adata to local buffer upon a GENerate command and _vld not being set
    // 2) Clear _vld when the last GENerate beat appears on the cmd_rsp port
    assign capt_adata = req_vld_i && (core_data.cmd == GEN) && (core_data.inst_id == i) &&
                        !generate_adata_vld_q[i];
    assign clear_adata_vld = rsp_vld_o && req_glast_i && (core_data.inst_id == i);

    always_comb begin
      generate_adata_vld_d[i] = generate_adata_vld_q[i];
      generate_adata_d[i]     = generate_adata_q[i];

      if (!enable_i) begin
        generate_adata_vld_d[i] = 1'b0;
        generate_adata_d[i]     = '0;
      end else if (capt_adata) begin
        generate_adata_vld_d[i] = 1'b1;
        generate_adata_d[i]     = core_data.pdata;
      end else if (clear_adata_vld) begin
        generate_adata_vld_d[i] = 1'b0;
      end
    end
  end

  //--------------------------------------------
  // Counter logic for v
  //--------------------------------------------

  // SEC_CM: CTR_DRBG.CTR.REDUN
  prim_count #(
    .Width(CtrLen),
    .PossibleActions(prim_count_pkg::Clr |
                     prim_count_pkg::Set |
                     prim_count_pkg::Incr)
  ) u_prim_count_ctr_drbg (
    .clk_i,
    .rst_ni,

    .clr_i    (!enable_i),
    .set_i    (v_ctr_load),
    .set_cnt_i(core_data.v[CtrLen-1:0]),

    .incr_en_i(v_ctr_inc),
    .decr_en_i(1'b0),
    .step_i   (CtrLen'(1)),
    .commit_i (1'b1),

    .cnt_o             (v_ctr),
    .cnt_after_commit_o(),
    .err_o             (ctr_err_o)
  );

  // Combine the MSBs of the initial v from the state db with the current counter value as LSBs
  assign v_ctr_sized = {core_data.v[BlkLen-1:CtrLen], v_ctr};

  //--------------------------------------------
  // Block encrypt request data assign
  //--------------------------------------------

  assign block_encrypt_req_data_o = '{
    key: core_data.key,
    v:   v_ctr_sized
  };

  //--------------------------------------------
  // Scratch register for block-wise derivation of new {key,v}
  //--------------------------------------------

  // Count the number of blocks that have been received back from block_encrypt until we have enough
  // blocks for at least SeedLen bits in total.
  assign concat_ctr_done = (concat_ctr_q >= NumBlkPerUpd);

  // Type conversion for easier usage
  assign concat_key_v = csrng_key_v_t'(concat_key_v_q);

  always_comb begin
    concat_ctr_d   = concat_ctr_q;
    concat_key_v_d = concat_key_v_q;

    if (!enable_i || concat_ctr_done) begin
      concat_ctr_d   = '0;
      concat_key_v_d = '0;
    end else if (concat_ctr_inc) begin
      concat_ctr_d = concat_ctr_q + 1;
      // Steer the v-response from block encrypt to the correct lane, MSB down
      concat_key_v_d[(NumBlkPerUpd - 1 - concat_ctr_q) * BlkLen +: BlkLen]
        = block_encrypt_rsp_data_i;
    end
  end

  //--------------------------------------------
  // FSM to orchestrate everything
  //--------------------------------------------

  always_comb begin
    state_d      = state_q;
    gen_subcmd_d = gen_subcmd_q;

    // Handshake and data validity
    req_rdy_o  = 1'b0;
    rsp_vld_o  = 1'b0;
    bits_vld_o = 1'b0;
    state_db_wr_o = 1'b0;

    block_encrypt_req_vld_o = 1'b0;
    block_encrypt_rsp_rdy_o = 1'b0;

    // Counter control
    v_ctr_load = 1'b0;
    v_ctr_inc  = 1'b0;
    concat_ctr_inc = 1'b0;

    // Error output
    sm_err_o = 1'b0;

    unique case (state_q)
      Idle: begin
        if (enable_i && req_vld_i) begin
          unique case (core_data.cmd)
            UNI: begin
              // No further action needed, write to state db and flag response valid
              req_rdy_o = 1'b1;
              rsp_vld_o = 1'b1;
              state_db_wr_o = 1'b1;
            end
            INS, RES, UPD: begin
              // Load the counter with v from state db
              v_ctr_load = 1'b1;
              state_d = CtrInc;
            end
            GEN: begin
              v_ctr_load = 1'b1;
              // Decide which GENerate sub command to execute
              // TODO(#28153) Clarify what the exact condition for skipping the initial UPDate()
              // call on GENerate commands is (pdata/adata being an all-zero vector or pdata/adata
              // LENGTH being zero).
              if (core_data.pdata != '0) begin
                gen_subcmd_d = UPD_BEGIN;
              end else begin
                gen_subcmd_d = GEN_LOOP;
              end
              state_d = CtrInc;
            end
            default: begin
              // Everything else is an error
              state_d = Error;
            end
          endcase
        end else begin
          // There is no "clear" on the AES cipher, so just flush out any outstanding responses
          // Otherwise, there will be erroneous handshakes when re-enabling the CSRNG
          block_encrypt_rsp_rdy_o = 1'b1;
        end
      end
      ReqSend: begin
        // Once a request has been accepted, also process its response.
        block_encrypt_req_vld_o = 1'b1;
        if (block_encrypt_req_rdy_i) begin
          state_d = RspWait;
        end
      end
      RspWait: begin
        block_encrypt_rsp_rdy_o = 1'b1;
        if (block_encrypt_rsp_vld_i) begin
          // In the actual generate part of GENerate, the response of the cipher is the generated
          // random bits. In all other cases, the response ends up in the scratch register.
          if ((core_data.cmd == GEN) && (gen_subcmd_q == GEN_LOOP)) begin
            bits_vld_o = 1'b1;
          end else begin
            v_ctr_inc = 1'b1;
            concat_ctr_inc = 1'b1;
          end
          // GENerate requires a more involved, separate logic on how to continue
          if (core_data.cmd == GEN) begin
            state_d = HndshkGen;
          end else begin
            state_d = Hndshk;
          end
        end
      end
      Hndshk: begin
        if (concat_ctr_done) begin
          // Enough data has been received to make up the new {key,v}; command is completed
          req_rdy_o = 1'b1;
          rsp_vld_o = 1'b1;
          state_db_wr_o = 1'b1;
          state_d = Idle;
        end else begin
          // More data required
          state_d = ReqSend;
        end
      end
      HndshkGen: begin
        unique case (gen_subcmd_q)
          UPD_BEGIN: begin
            if (concat_ctr_done) begin
              // We have to commit the derived {key,v} to the state db as they are the basis for the
              // UPD_FINAL step which we potentially must execute, also requiring the scratch reg
              state_db_wr_o = 1'b1;
              gen_subcmd_d = GEN_LOOP;
              state_d = HndshkLoad;
            end else begin
              state_d = ReqSend;
            end
          end
          GEN_LOOP: begin
            if (req_glast_i) begin
              // Do the initial v increment for the UPD_FINAL step that follows
              v_ctr_inc = 1'b1;
              gen_subcmd_d = UPD_FINAL;
              state_d = ReqSend;
            end else begin
              // This was not the last beat of the generate loop; signal the command as completed
              req_rdy_o = 1'b1;
              rsp_vld_o = 1'b1;
              state_db_wr_o = 1'b1;
              state_d = Idle;
            end
          end
          UPD_FINAL: begin
            if (concat_ctr_done) begin
              // Enough data has been received to make up the new {key,v}; command is completed
              req_rdy_o = 1'b1;
              rsp_vld_o = 1'b1;
              state_db_wr_o = 1'b1;
              state_d = Idle;
            end else begin
              // More data required
              state_d = ReqSend;
            end
          end
          default: begin
            // We should never get here
            state_d = Error;
          end
        endcase
      end
      HndshkLoad: begin
        // Transitional state to load the prim_count with the new v
        v_ctr_load = 1'b1;
        state_d = CtrInc;
      end
      CtrInc: begin
        // Transitional state to perform initial v-increment after (re)loading it from state db
        v_ctr_inc = 1'b1;
        state_d = ReqSend;
      end
      Error: begin
        sm_err_o = 1'b1;
      end
      default: begin
        state_d = Error;
        sm_err_o = 1'b1;
      end
    endcase

    // Avoid wrapping every state body in an `if (enable_i)` by collectively handling !enable_i
    // here, at least for most states.
    if (!enable_i && (state_q == RspWait)) begin
      // We have to handle this edge case, where there is an outstanding response from block_encrypt
      // while CSRNG gets disabled. Wait until the response arrives; otherwise, it can arrive at a
      // somewhat random time during other states and might corrupt or deadlock the control flow
      if (block_encrypt_rsp_vld_i) begin
        state_d = Idle;
      end
    end else if (!(state_q inside {Idle, Error}) && (state_d != Error)) begin
      // Be careful to not enable error-state escape by accident (checked by assertions).
      if (!enable_i) begin
        state_d = Idle;
      end
    end
  end

  //--------------------------------------------
  // Response/data out assignments
  //--------------------------------------------

  // Make sure the command stages get an error response in case we received an invalid command
  assign rsp_sts_o = (core_data.cmd == INV) ? CMD_STS_INVALID_ACMD : CMD_STS_SUCCESS;

  always_comb begin
    // Default case only relevant for UNInstantiate and invalid commands
    rsp_data_o = core_data;

    // For all commands that update the internal state, send new {key,v} to state db
    // For GENerate commands, we need a more involved handling of the three sub commands
    if (core_data.cmd inside {INS, RES, UPD}) begin
      rsp_data_o.key = concat_key_v.key ^ core_data.pdata[BlkLen +: KeyLen];
      rsp_data_o.v   = concat_key_v.v   ^ core_data.pdata[BlkLen-1:0];
    end else if (core_data.cmd == GEN) begin
      unique case (gen_subcmd_q)
        UPD_BEGIN: begin
          rsp_data_o.key = concat_key_v.key ^ core_data.pdata[BlkLen +: KeyLen];
          rsp_data_o.v   = concat_key_v.v   ^ core_data.pdata[BlkLen-1:0];
        end
        GEN_LOOP: begin
          rsp_data_o.key = core_data.key; // Unchanged
          rsp_data_o.v   = v_ctr_sized;   // Old value + 1
        end
        UPD_FINAL: begin
          rsp_data_o.key = concat_key_v.key ^ generate_adata_q[core_data.inst_id].key;
          rsp_data_o.v   = concat_key_v.v   ^ generate_adata_q[core_data.inst_id].v;
          // Increase the reseed counter on the last beat of every GENerate
          rsp_data_o.rs_ctr = core_data.rs_ctr + 1;
        end
        default: /* We should never get here */ ;
      endcase
    end
  end

  // Genbits out; actual bits taken directly from block cipher
  assign bits_data_o = block_encrypt_rsp_data_i;
  assign bits_fips_o = core_data.fips;

  //--------------------------------------------
  // Assertions and unused signal tie-off
  //--------------------------------------------

  // Currently not supported, but most probably never intended (would yield a very wide counter)
  `ASSERT_INIT(CsrngCtrLenLessBlkLen, CtrLen < BlkLen)
  // Make sure the FSM has a stable error state that cannot be escaped
  `ASSERT(CsrngCtrDrbgSmErrorStStable_A, state_q == Error |=> $stable(state_q))
  // Outside of any non-error state, the FSM error output must be asserted
  `ASSERT(CsrngCtrDrbgSmErrorOutput_A, !(state_q inside
          {Idle, CtrInc, ReqSend, RspWait, Hndshk, HndshkGen, HndshkLoad})
          |-> sm_err_o)

endmodule
