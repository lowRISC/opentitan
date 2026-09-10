// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

/**
 * RISC-V Register File
 *
 * Register file based on latches. Register 0 is set to 0 (unless used for dummy instructions).
 * This register file requires a target technology-specific clock gating cell. Use this register
 * file when targeting ASIC synthesis or event-based simulators.
 *
 * Three key parameters influence the number and size of physical registers:
 *
 * 1. RV32E == 1:
 *    Restricts the register file to 16 registers (x0–x15).
 *
 * 2. DummyInstructions == 1:
 *    Implements x0 as a physical register used to write the results of dummy instructions.
 *    It always reads back as zero for non-dummy instructions.
 *
 * 3. BaseIsa == BaseIsaRV32IorCHERIoT:
 *    Allows dynamic switching between standard RV32I/E registers (configured by the parameters
 *    above) and CHERIoT register mode when `cheriot_enable_i == IbexMuBiOn`.
 *    In CHERIoT mode, the core operates on 16 registers (x0–x15). These registers are wider
 *    because they include `CapWidth` capability metadata in addition to standard data bits.
 *
 *    To save area, the upper physical registers (x16–x31) from non-CHERIoT mode are re-purposed
 *    as `rf_shared` storage to hold CHERIoT capability metadata. Therefore, `CapWidth` must be
 *    >= `DataWidth` so that in non-CHERIoT mode, standard data writes to upper registers can be
 *    zero-extended into `rf_shared`.
 */

 `include "prim_assert.sv"

module ibex_register_file_latch import ibex_pkg::*; #(
  parameter base_isa_e            BaseIsa           = BaseIsaRV32I,
  parameter bit                   RV32E             = 0,
  parameter int unsigned          DataWidth         = 32,
  parameter bit                   DummyInstructions = 0,
  parameter logic [DataWidth-1:0] WordZeroVal       = '0,
  // Capability port width
  parameter int unsigned          CapWidth          = ibex_cheriot_pkg::REGCAP_W,
  parameter logic [CapWidth-1:0]  CapWordZeroVal    = '0
) (
  // Clock and Reset
  input  logic                 clk_i,
  input  logic                 rst_ni,

  input  logic                 test_en_i,
  input  logic                 dummy_instr_id_i,
  input  logic                 dummy_instr_wb_i,

  input  ibex_mubi_t           cheriot_enable_i,

  // Read port R1
  input  logic [4:0]           raddr_a_i,
  output logic [DataWidth-1:0] rdata_a_o,
  output logic [CapWidth-1:0]  rcap_a_o,

  // Read port R2
  input  logic [4:0]           raddr_b_i,
  output logic [DataWidth-1:0] rdata_b_o,
  output logic [CapWidth-1:0]  rcap_b_o,

  // Write port W1
  input  logic [4:0]           waddr_a_i,
  input  logic [DataWidth-1:0] wdata_a_i,
  input  logic [CapWidth-1:0]  wcap_a_i,
  input  logic                 we_a_i
);

  if (BaseIsa == BaseIsaRV32IorCHERIoT) begin : g_cheriot_rf

    // CapWidth must be larger than DataWidth to ensure no truncation in the non-CHERIoT mode
    `ASSERT_INIT(CapWidthGTEDataWidth, CapWidth >= DataWidth)

    // Decode CHERIoT enable (full 4-bit MuBi comparison against IbexMuBiOn).
    logic cheriot_enabled;
    assign cheriot_enabled = (cheriot_enable_i == IbexMuBiOn);

    // Physical registers
    logic [DataWidth-1:0] rf_data   [16]; // x0-x15 data (both modes)
    logic [CapWidth-1:0]  rf_shared [16]; // shared: cap (CHERIoT) or x16-x31 data (!CHERIoT,!RV32E)

    logic clk_int;

    ///////////
    // WRITE //
    ///////////
    // Global clock gating
    prim_clock_gating cg_we_global (
        .clk_i     ( clk_i     ),
        .en_i      ( we_a_i    ),
        .test_en_i ( test_en_i ),
        .clk_o     ( clk_int   )
    );

    // Write decode: waddr[3:0] indexes within a 16-entry bank.
    // Bank select: waddr[4]=0 → rf_data and rf_shared cap (CHERIoT co-write);
    //              waddr[4]=1 → rf_shared upper data (non-CHERIoT).
    logic [15:0] we_a_dec;
    always_comb begin : we_a_decoder
      for (int unsigned i = 0; i < 16; i++) begin
        we_a_dec[i] = (waddr_a_i[3:0] == 4'(i)) ? we_a_i : 1'b0;
      end
    end

    // Write data for the shared bank: cap metadata in CHERIoT mode, zero-extended data otherwise.
    logic [CapWidth-1:0] wshared_data;
    assign wshared_data = cheriot_enabled ? wcap_a_i : CapWidth'(wdata_a_i);

    // Sample input data: data and shared (cap or upper data).
    // Use clk_int here, since otherwise we don't want to write anything anyway.
    logic [DataWidth-1:0] wdata_a_q;
    logic [CapWidth-1:0]  wshared_a_q;

    always_ff @(posedge clk_int or negedge rst_ni) begin : sample_wdata
      if (!rst_ni) begin
        wdata_a_q <= WordZeroVal;
      end else if (we_a_i) begin
        wdata_a_q <= wdata_a_i;
      end
    end

    always_ff @(posedge clk_int or negedge rst_ni) begin : sample_wshared
      if (!rst_ni) begin
        wshared_a_q <= CapWordZeroVal;
      end else if (we_a_i) begin
        wshared_a_q <= wshared_data;
      end
    end

    logic [15:1] data_clocks;
    logic [15:1] shared_clocks;

    // Individual clock gating for data bank (x1-x15): waddr[4]=0
    for (genvar x = 1; x < 16; x++) begin : gen_data_cg_word_iter
      prim_clock_gating cg_i (
          .clk_i     ( clk_int                      ),
          .en_i      ( we_a_dec[x] && !waddr_a_i[4] ),
          .test_en_i ( test_en_i                    ),
          .clk_o     ( data_clocks[x]               )
      );
    end

    // Individual clock gating for shared bank (x1-x15):
    //   CHERIoT mode:     cap co-write with data (waddr[4]=0)
    //   non-CHERIoT mode: upper-data write (waddr[4]=1, only if !RV32E)
    for (genvar x = 1; x < 16; x++) begin : gen_shared_cg_word_iter
      prim_clock_gating cg_i (
          .clk_i     ( clk_int                                                     ),
          .en_i      ( ( cheriot_enabled && we_a_dec[x] && !waddr_a_i[4]) ||
                       (!cheriot_enabled && !RV32E && we_a_dec[x] && waddr_a_i[4]) ),
          .test_en_i ( test_en_i                                                   ),
          .clk_o     ( shared_clocks[x]                                            )
      );
    end

    // Data latches x1-x15
    for (genvar i = 1; i < 16; i++) begin : g_rf_data_latches
      always_latch begin
        if (data_clocks[i]) begin
          rf_data[i] = wdata_a_q;
        end
      end
    end

    // Shared latches x1-x15
    for (genvar i = 1; i < 16; i++) begin : g_rf_shared_latches
      always_latch begin
        if (shared_clocks[i]) begin
          rf_shared[i] = wshared_a_q;
        end
      end
    end

    // Entry 0: rf_data[0] (x0 data) and rf_shared[0] (x0 cap in CHERIoT / x16 data in non-CHERIoT).
    logic [CapWidth-1:0] rcap_r0; // x0 cap read value (null or dummy-dependent)

    // With dummy instructions enabled, R0 behaves as a real register but will always return 0 for
    // real instructions.
    if (DummyInstructions) begin : g_dummy_r0
      // SEC_CM: CTRL_FLOW.UNPREDICTABLE
      logic we_data_r0;
      logic we_shared_r0;

      // Write enable for dummy R0 register (waddr_a_i will always be 0 for dummy instructions)
      assign we_data_r0   = we_a_dec[0] && !waddr_a_i[4] && dummy_instr_wb_i;
      assign we_shared_r0 = cheriot_enabled ? we_data_r0 :
                                              (!RV32E && we_a_dec[0] && waddr_a_i[4]);
      `ASSERT(DummyWriteTargetsX0, we_a_i && dummy_instr_wb_i |-> waddr_a_i == '0)

      logic r0_data_clock;
      logic r0_shared_clock;

      prim_clock_gating cg_r0_data (
          .clk_i     ( clk_int       ),
          .en_i      ( we_data_r0    ),
          .test_en_i ( test_en_i     ),
          .clk_o     ( r0_data_clock )
      );

      prim_clock_gating cg_r0_shared (
          .clk_i     ( clk_int         ),
          .en_i      ( we_shared_r0    ),
          .test_en_i ( test_en_i       ),
          .clk_o     ( r0_shared_clock )
      );

      logic [DataWidth-1:0] rf_data_r0;
      logic [CapWidth-1:0]  rf_shared_r0;

      always_latch begin : latch_data_r0
        if (r0_data_clock) begin
          rf_data_r0 = wdata_a_q;
        end
      end

      always_latch begin : latch_shared_r0
        if (r0_shared_clock) begin
          rf_shared_r0 = wshared_a_q;
        end
      end

      // Output the dummy data for dummy instructions, otherwise R0 reads as zero
      assign rf_data[0]   = dummy_instr_id_i ? rf_data_r0 : WordZeroVal;
      // Output rf_shared[0] unconditionally for the x16 case
      assign rf_shared[0] = rf_shared_r0;
      // Output the dummy capability only for dummy instructions, otherwise R0 cap reads as zero
      assign rcap_r0      = dummy_instr_id_i ? rf_shared[0] : CapWordZeroVal;

    end else begin : g_normal_r0
      assign rf_data[0] = WordZeroVal;
      assign rcap_r0    = CapWordZeroVal;

      logic unused_dummy_instr;
      assign unused_dummy_instr = dummy_instr_id_i ^ dummy_instr_wb_i;

      // rf_shared[0] needs a real latch when x16 exists (!RV32E). Without dummy instructions, this
      // will never be used as a capability and only ever for x16 data.
      if (!RV32E) begin : g_rf_shared0_x16
        logic r0_shared_clock;
        logic [DataWidth-1:0] rf_shared_r0;

        prim_clock_gating cg_r0_shared (
            .clk_i     ( clk_int                                          ),
            .en_i      ( we_a_dec[0] && waddr_a_i[4] && !cheriot_enabled ),
            .test_en_i ( test_en_i                                        ),
            .clk_o     ( r0_shared_clock                                  )
        );

        always_latch begin : latch_shared_r0
          if (r0_shared_clock) begin
            rf_shared_r0 = wdata_a_q;
          end
        end

        assign rf_shared[0] = CapWidth'(rf_shared_r0);
      end else begin : g_rf_shared0_no_x16
        assign rf_shared[0] = CapWordZeroVal;

        logic unused_we_a_dec0;
        assign unused_we_a_dec0 = we_a_dec[0];
      end
    end

    // In CHERIoT mode all register addresses are 4-bit (implicit E extension). Hence, the MSB must
    // never be set. The bank-select bit is anyway forced to 0.
    `ASSERT(CheriotWaddrMSBClear,  cheriot_enabled |-> !waddr_a_i[4])
    `ASSERT(CheriotRaddrAMSBClear, cheriot_enabled |-> !raddr_a_i[4])
    `ASSERT(CheriotRaddrBMSBClear, cheriot_enabled |-> !raddr_b_i[4])

    //////////
    // READ //
    //////////
    // Data: raddr[4]=0 → rf_data (x0-x15)
    //       raddr[4]=1 → rf_shared lower DataWidth bits (x16-x31), non-CHERIoT only.
    assign rdata_a_o = (raddr_a_i[4] && !cheriot_enabled) ?
      DataWidth'(rf_shared[raddr_a_i[3:0]]) : rf_data[raddr_a_i[3:0]];
    assign rdata_b_o = (raddr_b_i[4] && !cheriot_enabled) ?
      DataWidth'(rf_shared[raddr_b_i[3:0]]) : rf_data[raddr_b_i[3:0]];

    // Cap: gated to CapWordZeroVal in non-CHERIoT mode.
    assign rcap_a_o = cheriot_enabled ?
      ((raddr_a_i[3:0] == '0) ? rcap_r0 : rf_shared[raddr_a_i[3:0]]) : CapWordZeroVal;
    assign rcap_b_o = cheriot_enabled ?
      ((raddr_b_i[3:0] == '0) ? rcap_r0 : rf_shared[raddr_b_i[3:0]]) : CapWordZeroVal;

  end else begin : g_plain_rf

    // BaseIsaRV32I: original latch-based register file, no capability support
    localparam int unsigned ADDR_WIDTH = RV32E ? 4 : 5;
    localparam int unsigned NUM_WORDS  = 2**ADDR_WIDTH;

    logic [DataWidth-1:0] mem[NUM_WORDS];

    logic [NUM_WORDS-1:0] waddr_onehot_a;

    logic [NUM_WORDS-1:1] mem_clocks;
    logic [DataWidth-1:0] wdata_a_q;

    // internal addresses
    logic [ADDR_WIDTH-1:0] raddr_a_int, raddr_b_int, waddr_a_int;

    assign raddr_a_int = raddr_a_i[ADDR_WIDTH-1:0];
    assign raddr_b_int = raddr_b_i[ADDR_WIDTH-1:0];
    assign waddr_a_int = waddr_a_i[ADDR_WIDTH-1:0];

    logic clk_int;

    //////////
    // READ //
    //////////
    assign rdata_a_o = mem[raddr_a_int];
    assign rdata_b_o = mem[raddr_b_int];
    assign rcap_a_o  = CapWordZeroVal;
    assign rcap_b_o  = CapWordZeroVal;

    logic unused_wcap_a;
    assign unused_wcap_a = ^wcap_a_i;

    logic unused_cheriot_enable;
    assign unused_cheriot_enable = ^cheriot_enable_i;

    ///////////
    // WRITE //
    ///////////
    // Global clock gating
    prim_clock_gating cg_we_global (
        .clk_i     ( clk_i     ),
        .en_i      ( we_a_i    ),
        .test_en_i ( test_en_i ),
        .clk_o     ( clk_int   )
    );

    // Sample input data
    // Use clk_int here, since otherwise we don't want to write anything anyway.
    always_ff @(posedge clk_int or negedge rst_ni) begin : sample_wdata
      if (!rst_ni) begin
        wdata_a_q <= WordZeroVal;
      end else begin
        if (we_a_i) begin
          wdata_a_q <= wdata_a_i;
        end
      end
    end

    // Write address decoding
    always_comb begin : wad
      for (int i = 0; i < NUM_WORDS; i++) begin : wad_word_iter
        if (we_a_i && (waddr_a_int == 5'(i))) begin
          waddr_onehot_a[i] = 1'b1;
        end else begin
          waddr_onehot_a[i] = 1'b0;
        end
      end
    end

    logic unused_strobe;
    assign unused_strobe = waddr_onehot_a[0]; // this is never read from in this case

    // Individual clock gating (if integrated clock-gating cells are available)
    for (genvar x = 1; x < NUM_WORDS; x++) begin : gen_cg_word_iter
      prim_clock_gating cg_i (
          .clk_i     ( clk_int           ),
          .en_i      ( waddr_onehot_a[x] ),
          .test_en_i ( test_en_i         ),
          .clk_o     ( mem_clocks[x]     )
      );
    end

    // Actual write operation:
    // Generate the sequential process for the NUM_WORDS words of the memory.
    // The process is synchronized with the clocks mem_clocks[i], i = 1, ..., NUM_WORDS-1.
    for (genvar i = 1; i < NUM_WORDS; i++) begin : g_rf_latches
      always_latch begin
        if (mem_clocks[i]) begin
          mem[i] = wdata_a_q;
        end
      end
    end

    // With dummy instructions enabled, R0 behaves as a real register but will always return 0 for
    // real instructions.
    if (DummyInstructions) begin : g_dummy_r0
      // SEC_CM: CTRL_FLOW.UNPREDICTABLE
      logic                 we_r0_dummy;
      logic                 r0_clock;
      logic [DataWidth-1:0] mem_r0;

      // Write enable for dummy R0 register (waddr_a_i will always be 0 for dummy instructions)
      assign we_r0_dummy = we_a_i & dummy_instr_wb_i;
      `ASSERT(DummyWriteTargetsX0, we_a_i && dummy_instr_wb_i |-> waddr_a_i == '0)

      // R0 clock gate
      prim_clock_gating cg_i (
          .clk_i     ( clk_int     ),
          .en_i      ( we_r0_dummy ),
          .test_en_i ( test_en_i   ),
          .clk_o     ( r0_clock    )
      );

      always_latch begin : latch_wdata
        if (r0_clock) begin
          mem_r0 = wdata_a_q;
        end
      end

      // Output the dummy data for dummy instructions, otherwise R0 reads as zero
      assign mem[0] = dummy_instr_id_i ? mem_r0 : WordZeroVal;

    end else begin : g_normal_r0
      logic unused_dummy_instr;
      assign unused_dummy_instr = dummy_instr_id_i ^ dummy_instr_wb_i;

      assign mem[0] = WordZeroVal;
    end

  end

`ifdef VERILATOR
  initial begin
    $display("Latch-based register file not supported for Verilator simulation");
    $fatal;
  end
`endif

endmodule
