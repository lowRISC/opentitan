// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

module otbn_top_sim (
  input IO_CLK,
  input IO_RST_N
);
  import otbn_pkg::*;

  // Size of the instruction memory, in bytes
  parameter int ImemSizeByte = otbn_reg_pkg::OTBN_IMEM_SIZE;
  // Size of the data memory, in bytes
  parameter int DmemSizeByte = otbn_reg_pkg::OTBN_DMEM_SIZE;

  localparam int ImemAddrWidth = prim_util_pkg::vbits(ImemSizeByte);
  localparam int DmemAddrWidth = prim_util_pkg::vbits(DmemSizeByte);

  // Fixed key and nonce for scrambling in verilator environment
  localparam logic [127:0] TestScrambleKey   = 128'h48ecf6c738f0f108a5b08620695ffd4d;
  localparam logic [63:0]  TestScrambleNonce = 64'hf88c2578fa4cd123;

  logic      otbn_done_d, otbn_done_q;
  err_bits_t otbn_err_bits_d, otbn_err_bits_q;
  logic      otbn_start;

  // Intialise otbn_start_done to 1 so that we only signal otbn_start after we have seen a reset. If
  // you don't do this, we start OTBN before the reset, which can generate confusing trace messages.
  logic      otbn_start_done = 1'b1;

  // Instruction memory (IMEM) signals
  logic                     imem_req;
  logic [ImemAddrWidth-1:0] imem_addr;
  logic [38:0]              imem_rdata;
  logic                     imem_rvalid;
  logic                     imem_rerror;

  // Data memory (DMEM) signals
  logic                     dmem_req;
  logic                     dmem_write;
  logic [DmemAddrWidth-1:0] dmem_addr;
  logic [ExtWLEN-1:0]       dmem_wdata;
  logic [ExtWLEN-1:0]       dmem_wmask;
  logic [ExtWLEN-1:0]       dmem_rdata;
  logic                     dmem_rvalid;
  logic                     dmem_rerror;

  // Entropy Distribution Network (EDN)
  logic                     edn_rnd_req, edn_urnd_req;
  logic                     edn_rnd_ack, edn_urnd_ack;
  logic [EdnDataWidth-1:0]  edn_rnd_data, edn_urnd_data;
  logic                     edn_rnd_data_valid;
  logic                     edn_urnd_data_valid;

  // Instruction counter (feeds into otbn.INSN_CNT in full block)
  logic [31:0]              insn_cnt;

  otbn_core #(
    .ImemSizeByte ( ImemSizeByte ),
    .DmemSizeByte ( DmemSizeByte )
  ) u_otbn_core (
    .clk_i                  ( IO_CLK           ),
    .rst_ni                 ( IO_RST_N         ),

    .start_i                ( otbn_start       ),
    .done_o                 ( otbn_done_d      ),
    .locked_o               (                  ),

    .err_bits_o             ( otbn_err_bits_d  ),

    .imem_req_o             ( imem_req         ),
    .imem_addr_o            ( imem_addr        ),
    .imem_wdata_o           (                  ),
    .imem_rdata_i           ( imem_rdata[31:0] ),
    .imem_rvalid_i          ( imem_rvalid      ),
    .imem_rerror_i          ( imem_rerror      ),

    .dmem_req_o             ( dmem_req         ),
    .dmem_write_o           ( dmem_write       ),
    .dmem_addr_o            ( dmem_addr        ),
    .dmem_wdata_o           ( dmem_wdata       ),
    .dmem_wmask_o           ( dmem_wmask       ),
    .dmem_rmask_o           ( ),
    .dmem_rdata_i           ( dmem_rdata       ),
    .dmem_rvalid_i          ( dmem_rvalid      ),
    .dmem_rerror_i          ( dmem_rerror      ),

    .edn_rnd_req_o          ( edn_rnd_req      ),
    .edn_rnd_ack_i          ( edn_rnd_ack      ),
    .edn_rnd_data_i         ( edn_rnd_data     ),

    .edn_urnd_req_o         ( edn_urnd_req     ),
    .edn_urnd_ack_i         ( edn_urnd_ack     ),
    .edn_urnd_data_i        ( edn_urnd_data    ),

    .insn_cnt_o             ( insn_cnt         ),

    .bus_intg_violation_i   ( 1'b0             ),
    .illegal_bus_access_i   ( 1'b0             ),
    .lifecycle_escalation_i ( 1'b0             )
  );

  // The top bits of IMEM rdata aren't currently used (they will eventually be used for integrity
  // checks both on the bus and within the core)
  logic unused_imem_top_rdata;
  assign unused_imem_top_rdata = &{1'b0, imem_rdata[38:32]};

  localparam logic [WLEN-1:0] FixedEdnVal = {{(WLEN / 4){4'h9}}};

  otbn_mock_edn #(
    .Width       ( WLEN        ),
    .FixedEdnVal ( FixedEdnVal )
  ) u_mock_rnd_edn(
    .clk_i      ( IO_CLK       ),
    .rst_ni     ( IO_RST_N     ),

    .edn_req_i  ( edn_rnd_req  ),
    .edn_ack_o  ( edn_rnd_ack  ),
    .edn_data_o ( edn_rnd_data )
  );

  assign edn_rnd_data_valid = edn_rnd_req & edn_rnd_ack;

  otbn_mock_edn #(
    .Width       ( WLEN        ),
    .FixedEdnVal ( FixedEdnVal )
  ) u_mock_urnd_edn(
    .clk_i      ( IO_CLK       ),
    .rst_ni     ( IO_RST_N     ),

    .edn_req_i  ( edn_urnd_req  ),
    .edn_ack_o  ( edn_urnd_ack  ),
    .edn_data_o ( edn_urnd_data )
  );

  assign edn_urnd_data_valid = edn_urnd_req & edn_urnd_ack;

  bind otbn_core otbn_trace_if #(.ImemAddrWidth, .DmemAddrWidth) i_otbn_trace_if (.*);
  bind otbn_core otbn_tracer u_otbn_tracer(.*, .otbn_trace(i_otbn_trace_if));

  // Pulse otbn_start for 1 cycle immediately out of reset.
  // Flop `done_o` from otbn_core to match up with model done signal.
  always @(posedge IO_CLK or negedge IO_RST_N) begin
    if (!IO_RST_N) begin
      otbn_start      <= 1'b0;
      otbn_start_done <= 1'b0;
      otbn_done_q     <= 1'b0;
      otbn_err_bits_q <= '0;
    end else begin
      if (!otbn_start_done) begin
        otbn_start      <= 1'b1;
        otbn_start_done <= 1'b1;
      end else if (otbn_start) begin
        otbn_start <= 1'b0;
      end

      otbn_done_q <= otbn_done_d;
      otbn_err_bits_q <= otbn_err_bits_d;
    end
  end

  localparam int DmemSizeWords = DmemSizeByte / (WLEN / 8);
  localparam int DmemIndexWidth = prim_util_pkg::vbits(DmemSizeWords);

  logic [DmemIndexWidth-1:0] dmem_index;
  logic [DmemAddrWidth-DmemIndexWidth-1:0] unused_dmem_addr;

  assign dmem_index = dmem_addr[DmemAddrWidth-1:DmemAddrWidth-DmemIndexWidth];
  assign unused_dmem_addr = dmem_addr[DmemAddrWidth-DmemIndexWidth-1:0];

  prim_ram_1p_scr #(
    .Width              ( ExtWLEN       ),
    .Depth              ( DmemSizeWords ),
    .DataBitsPerMask    ( 39            ),
    .EnableParity       ( 0             ),
    .ReplicateKeyStream ( 1             )
  ) u_dmem (
    .clk_i        ( IO_CLK            ),
    .rst_ni       ( IO_RST_N          ),

    .key_valid_i  ( 1'b1              ),
    .key_i        ( TestScrambleKey   ),
    .nonce_i      ( TestScrambleNonce ),

    .req_i        ( dmem_req          ),
    .gnt_o        (                   ),
    .write_i      ( dmem_write        ),
    .addr_i       ( dmem_index        ),
    .wdata_i      ( dmem_wdata        ),
    .wmask_i      ( dmem_wmask        ),
    .intg_error_i ( 1'b0              ),

    .rdata_o      ( dmem_rdata        ),
    .rvalid_o     ( dmem_rvalid       ),
    .raddr_o      (                   ),
    .rerror_o     (                   ),
    .cfg_i        ( '0                )
  );

  // No integrity errors in Verilator testbench
  assign dmem_rerror = 1'b0;

  localparam int ImemSizeWords = ImemSizeByte / 4;
  localparam int ImemIndexWidth = prim_util_pkg::vbits(ImemSizeWords);

  logic [ImemIndexWidth-1:0] imem_index;
  logic [1:0] unused_imem_addr;

  assign imem_index = imem_addr[ImemAddrWidth-1:2];
  assign unused_imem_addr = imem_addr[1:0];

  prim_ram_1p_scr #(
    .Width           ( 39            ),
    .Depth           ( ImemSizeWords ),
    .DataBitsPerMask ( 39            ),
    .EnableParity    ( 0             )
  ) u_imem (
    .clk_i        ( IO_CLK                  ),
    .rst_ni       ( IO_RST_N                ),

    .key_valid_i  ( 1'b1                    ),
    .key_i        ( TestScrambleKey         ),
    .nonce_i      ( TestScrambleNonce       ),

    .req_i        ( imem_req                ),
    .gnt_o        (                         ),
    .write_i      ( 1'b0                    ),
    .addr_i       ( imem_index              ),
    .wdata_i      ( '0                      ),
    .wmask_i      ( '0                      ),
    .intg_error_i ( 1'b0                    ),

    .rdata_o      ( imem_rdata              ),
    .rvalid_o     ( imem_rvalid             ),
    .raddr_o      (                         ),
    .rerror_o     (                         ),
    .cfg_i        ( '0                      )
  );

  // No integrity errors in Verilator testbench
  assign imem_rerror = 1'b0;

  // When OTBN is done let a few more cycles run then finish simulation
  logic [1:0] finish_counter;

  always @(posedge IO_CLK or negedge IO_RST_N) begin
    if (!IO_RST_N) begin
      finish_counter <= 2'd0;
    end else begin
      if (otbn_done_q) begin
        finish_counter <= 2'd1;
      end

      if (finish_counter != 0) begin
        finish_counter <= finish_counter + 2'd1;
      end

      if (finish_counter == 2'd3) begin
        $finish;
      end
    end
  end

  // The model
  //
  // This runs in parallel with the real core above, with consistency checks between the two.

  localparam string DesignScope = "..u_otbn_core";

  logic      otbn_model_done;
  err_bits_t otbn_model_err_bits;
  bit [31:0] otbn_model_insn_cnt;
  bit        otbn_model_err;

  otbn_core_model #(
    .DmemSizeByte    ( DmemSizeByte ),
    .ImemSizeByte    ( ImemSizeByte ),
    .MemScope        ( ".." ),
    .DesignScope     ( DesignScope )
  ) u_otbn_core_model (
    .clk_i                 ( IO_CLK ),
    .rst_ni                ( IO_RST_N ),

    .start_i               ( otbn_start ),
    .done_o                ( otbn_model_done ),

    .err_bits_o            ( otbn_model_err_bits ),

    .edn_rnd_data_valid_i  ( edn_rnd_data_valid ),
    .edn_rnd_data_i        ( edn_rnd_data ),
    .edn_urnd_data_valid_i ( edn_urnd_data_valid ),

    .status_o              (),
    .insn_cnt_o            ( otbn_model_insn_cnt ),

    .err_o                 ( otbn_model_err )
  );

  bit done_mismatch_latched, err_bits_mismatch_latched, cnt_mismatch_latched;
  bit model_err_latched, loop_warp_model_err;

  always_ff @(posedge IO_CLK or negedge IO_RST_N) begin
    if (!IO_RST_N) begin
      done_mismatch_latched     <= 1'b0;
      err_bits_mismatch_latched <= 1'b0;
      cnt_mismatch_latched      <= 1'b0;
      model_err_latched         <= 1'b0;
    end else begin
      if (otbn_done_q != otbn_model_done) begin
        $display("ERROR: At time %0t, otbn_done_q != otbn_model_done (%0d != %0d).",
                 $time, otbn_done_q, otbn_model_done);
        done_mismatch_latched <= 1'b1;
      end
      if (otbn_done_q && otbn_model_done) begin
        if (otbn_err_bits_q != otbn_model_err_bits) begin
          $display("ERROR: At time %0t, otbn_err_bits != otbn_model_err_bits (0x%0x != 0x%0x).",
                   $time, otbn_err_bits_q, otbn_model_err_bits);
          err_bits_mismatch_latched <= 1'b1;
        end
      end
      if (insn_cnt != otbn_model_insn_cnt) begin
        if (!cnt_mismatch_latched) begin
          $display("ERROR: At time %0t, insn_cnt != otbn_model_insn_cnt (0x%0x != 0x%0x).",
                   $time, insn_cnt, otbn_model_insn_cnt);
        end
        cnt_mismatch_latched <= 1'b1;
      end
      model_err_latched <= model_err_latched | otbn_model_err | loop_warp_model_err;
    end
  end

  bit err_latched;
  assign err_latched = model_err_latched | done_mismatch_latched | err_bits_mismatch_latched;

  int bad_cycles;
  always_ff @(negedge IO_CLK or negedge IO_RST_N) begin
    if (!IO_RST_N) begin
      bad_cycles <= 0;
    end else begin
      if (err_latched) begin
        bad_cycles <= bad_cycles + 1;
      end
      if (bad_cycles >= 3) begin
        $error("Mismatch or model error (see message above)");
      end
    end
  end

  // Defined in otbn_top_sim.cc
  import "DPI-C" context function int OtbnTopApplyLoopWarp();

  always_ff @(negedge IO_CLK or negedge IO_RST_N) begin
    if (!IO_RST_N) begin
      loop_warp_model_err <= 1'b0;
    end else begin
      if (OtbnTopApplyLoopWarp() != 0) begin
        $display("ERROR: At time %0t, OtbnTopApplyLoopWarp() failed.", $time);
        loop_warp_model_err <= 1'b1;
      end
    end
  end

  export "DPI-C" function otbn_base_call_stack_get_size;

  function automatic int unsigned otbn_base_call_stack_get_size();
    return u_otbn_core.u_otbn_rf_base.u_call_stack.stack_wr_ptr_q;
  endfunction

  export "DPI-C" function otbn_base_call_stack_get_element;

  function automatic int unsigned otbn_base_call_stack_get_element(int index);
    return u_otbn_core.u_otbn_rf_base.u_call_stack.stack_storage[index][31:0];
  endfunction

  export "DPI-C" function otbn_base_reg_get;

  function automatic int unsigned otbn_base_reg_get(int index);
    return u_otbn_core.u_otbn_rf_base.gen_rf_base_ff.u_otbn_rf_base_inner.rf_reg[index][31:0];
  endfunction

  export "DPI-C" function otbn_bignum_reg_get;

  function automatic int unsigned otbn_bignum_reg_get(int index, int word);
    return u_otbn_core.u_otbn_rf_bignum.gen_rf_bignum_ff.u_otbn_rf_bignum_inner.rf[index][word*39+:32];
  endfunction

  export "DPI-C" function otbn_err_get;

  function automatic bit otbn_err_get();
    return err_latched;
  endfunction

endmodule
