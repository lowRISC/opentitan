// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`include "prim_assert.sv"

module otbn_predecode
  import otbn_pkg::*;
(
  input  logic                   clk_i,
  input  logic                   rst_ni,

  input  logic [31:0]            imem_rdata_i,
  input  logic                   imem_rvalid_i,

  output rf_predec_bignum_t   rf_predec_bignum_o,
  output alu_predec_bignum_t  alu_predec_bignum_o,
  output ispr_predec_bignum_t ispr_predec_bignum_o,
  output mac_predec_bignum_t  mac_predec_bignum_o,
  output logic                lsu_addr_en_predec_o
);
  logic rf_ren_a_bignum;
  logic rf_ren_b_bignum;
  logic rf_we_bignum;
  logic alu_bignum_adder_x_en;
  logic alu_bignum_adder_y_op_a_en;
  logic alu_bignum_adder_y_op_shifter_en;
  logic alu_bignum_shifter_a_en;
  logic alu_bignum_shifter_b_en;
  logic alu_bignum_logic_a_en;
  logic alu_bignum_logic_shifter_en;

  logic mac_bignum_op_en;
  logic mac_bignum_acc_rd_en;

  logic ispr_rd_en;
  logic ispr_wr_en;

  logic csr_addr_sel;
  logic [4:0] insn_rs1, insn_rs2, insn_rd;

  wsr_e  wsr_addr;
  csr_e  csr_addr;
  ispr_e ispr_addr;

  assign csr_addr = csr_e'(imem_rdata_i[31:20]);
  assign wsr_addr = wsr_e'(imem_rdata_i[20 +: WsrNumWidth]);

  always_comb begin
    rf_ren_a_bignum = 1'b0;
    rf_ren_b_bignum = 1'b0;
    rf_we_bignum    = 1'b0;

    alu_bignum_adder_x_en            = 1'b0;
    alu_bignum_adder_y_op_a_en       = 1'b0;
    alu_bignum_adder_y_op_shifter_en = 1'b0;
    alu_bignum_shifter_a_en          = 1'b0;
    alu_bignum_shifter_b_en          = 1'b0;
    alu_bignum_logic_a_en            = 1'b0;
    alu_bignum_logic_shifter_en      = 1'b0;

    mac_bignum_op_en     = 1'b0;
    mac_bignum_acc_rd_en = 1'b0;

    ispr_rd_en = 1'b0;
    ispr_wr_en = 1'b0;

    csr_addr_sel = 1'b0;

    lsu_addr_en_predec_o = 1'b0;

    if (imem_rvalid_i) begin
      unique case (imem_rdata_i[6:0])

        ///////////////////////
        // Base Load / Store //
        ///////////////////////

        InsnOpcodeBaseStore, InsnOpcodeBaseLoad: begin
          if (imem_rdata_i[14:12] == 3'b010) begin
            lsu_addr_en_predec_o = 1'b1;
          end
        end

        //////////////
        // Base CSR //
        //////////////

        InsnOpcodeBaseSystem: begin
          csr_addr_sel = 1'b1;

          if (csr_addr == CsrRndPrefetch) begin
            // Prefetch CSR does not access any ISPR
            ispr_rd_en = 1'b0;
            ispr_wr_en = 1'b0;
          end else if (imem_rdata_i[14:12] == 3'b001) begin
            // No read if destination is x0 unless read is to flags CSR. Both flag groups are in
            // a single ISPR so to write one group the other must be read to write it back
            // unchanged.
            ispr_rd_en = (imem_rdata_i[11:7] != 5'b0) | (csr_addr == CsrFg0) | (csr_addr == CsrFg1);
            ispr_wr_en = 1'b1;
          end else if (imem_rdata_i[14:12] == 3'b010) begin
            // Read and set if source register isn't x0, otherwise read only
            if (imem_rdata_i[19:15] != 5'b0) begin
              ispr_rd_en = 1'b1;
              ispr_wr_en = 1'b1;
            end else begin
              ispr_rd_en = 1'b1;
            end
          end
        end

        ////////////////
        // Bignum ALU //
        ////////////////

        InsnOpcodeBignumArith: begin
          unique case (imem_rdata_i[14:12])
            3'b000, 3'b001, 3'b010, 3'b011:  begin
              // BN.ADD/BN.SUB/BN.ADDC/BN.SUBB
              rf_ren_a_bignum                  = 1'b1;
              rf_ren_b_bignum                  = 1'b1;
              rf_we_bignum                     = 1'b1;
              alu_bignum_shifter_b_en          = 1'b1;
              alu_bignum_adder_y_op_a_en       = 1'b1;
              alu_bignum_adder_y_op_shifter_en = 1'b1;
            end
            3'b100: begin
              // BN.ADDI/BN.SUBI
              rf_ren_a_bignum                  = 1'b1;
              rf_we_bignum                     = 1'b1;
              alu_bignum_shifter_b_en          = 1'b1;
              alu_bignum_adder_y_op_a_en       = 1'b1;
              alu_bignum_adder_y_op_shifter_en = 1'b1;
            end
            3'b101: begin
              // BN.ADDM/BN.SUBM
              rf_ren_a_bignum       = 1'b1;
              rf_ren_b_bignum       = 1'b1;
              rf_we_bignum          = 1'b1;
              alu_bignum_adder_x_en = 1'b1;
            end
            default: ;
          endcase
        end

        ////////////////////////////
        // Bignum logical/BN.RSHI //
        ////////////////////////////

        InsnOpcodeBignumBaseMisc: begin
          unique case (imem_rdata_i[14:12])
            3'b010, 3'b100, 3'b110:  begin  // BN.AND/BN.OR/BN.XOR
              rf_we_bignum                = 1'b1;
              rf_ren_a_bignum             = 1'b1;
              rf_ren_b_bignum             = 1'b1;
              alu_bignum_shifter_b_en     = 1'b1;
              alu_bignum_logic_a_en       = 1'b1;
              alu_bignum_logic_shifter_en = 1'b1;
            end
            3'b111, 3'b011: begin // BN.RHSI
              rf_we_bignum            = 1'b1;
              rf_ren_a_bignum         = 1'b1;
              rf_ren_b_bignum         = 1'b1;
              alu_bignum_shifter_a_en = 1'b1;
              alu_bignum_shifter_b_en = 1'b1;
            end
            3'b101: begin // BN.NOT
              rf_we_bignum                = 1'b1;
              rf_ren_b_bignum             = 1'b1;
              alu_bignum_shifter_b_en     = 1'b1;
              alu_bignum_logic_shifter_en = 1'b1;
            end
            default: ;
          endcase
        end

        ///////////////////////////////////////////////
        // Bignum Misc WSR/LID/SID/MOV[R]/CMP[B]/SEL //
        ///////////////////////////////////////////////

        InsnOpcodeBignumMisc: begin
          unique case (imem_rdata_i[14:12])
            3'b000: begin // BN.SEL
              rf_we_bignum    = 1'b1;
              rf_ren_a_bignum = 1'b1;
              rf_ren_b_bignum = 1'b1;
            end
            3'b011, 3'b001: begin // BN.CMP[B]
              rf_ren_a_bignum                  = 1'b1;
              rf_ren_b_bignum                  = 1'b1;
              alu_bignum_shifter_b_en          = 1'b1;
              alu_bignum_adder_y_op_a_en       = 1'b1;
              alu_bignum_adder_y_op_shifter_en = 1'b1;
            end
            3'b100, 3'b101: begin  // BN.LID, BN.SID
              lsu_addr_en_predec_o = 1'b1;
            end
            3'b110: begin // BN.MOV/BN.MOVR
              if (~imem_rdata_i[31]) begin
                rf_we_bignum    = 1'b1;
                rf_ren_a_bignum = 1'b1;
              end
            end
            3'b111: begin
              if (imem_rdata_i[31]) begin  // BN.WSRW
                rf_ren_a_bignum = 1'b1;
                ispr_wr_en      = 1'b1;
              end else begin  // BN.WSRR
                rf_we_bignum = 1'b1;
                ispr_rd_en   = 1'b1;
              end
            end
            default: ;
          endcase
        end

        ////////////////////////////////////////////
        // BN.MULQACC/BN.MULQACC.WO/BN.MULQACC.SO //
        ////////////////////////////////////////////

        InsnOpcodeBignumMulqacc: begin
          rf_ren_a_bignum  = 1'b1;
          rf_ren_b_bignum  = 1'b1;
          mac_bignum_op_en = 1'b1;

          // BN.MULQACC.WO/BN.MULQACC.SO
          if (imem_rdata_i[30] == 1'b1 || imem_rdata_i[29] == 1'b1) begin
            rf_we_bignum = 1'b1;
          end

          if (imem_rdata_i[12] == 1'b0) begin
            // zero_acc not set
            mac_bignum_acc_rd_en = 1'b1;
          end
        end

        default: ;
      endcase
    end
  end

  always_comb begin
    ispr_addr = IsprMod;

    if (csr_addr_sel) begin
      unique case (csr_addr)
        CsrFlags, CsrFg0, CsrFg1:           ispr_addr = IsprFlags;
        CsrMod0, CsrMod1, CsrMod2, CsrMod3,
        CsrMod4, CsrMod5, CsrMod6, CsrMod7: ispr_addr = IsprMod;
        CsrRnd:                             ispr_addr = IsprRnd;
        CsrUrnd:                            ispr_addr = IsprUrnd;
        default: ;
      endcase
    end else begin
      unique case (wsr_addr)
        WsrMod:    ispr_addr = IsprMod;
        WsrRnd:    ispr_addr = IsprRnd;
        WsrUrnd:   ispr_addr = IsprUrnd;
        WsrAcc:    ispr_addr = IsprAcc;
        WsrKeyS0L: ispr_addr = IsprKeyS0L;
        WsrKeyS0H: ispr_addr = IsprKeyS0H;
        WsrKeyS1L: ispr_addr = IsprKeyS1L;
        WsrKeyS1H: ispr_addr = IsprKeyS1H;
        default: ;
      endcase
    end
  end

  assign alu_predec_bignum_o.adder_x_en            = alu_bignum_adder_x_en;
  assign alu_predec_bignum_o.adder_y_op_a_en       = alu_bignum_adder_y_op_a_en;
  assign alu_predec_bignum_o.adder_y_op_shifter_en = alu_bignum_adder_y_op_shifter_en;
  assign alu_predec_bignum_o.shifter_a_en          = alu_bignum_shifter_a_en;
  assign alu_predec_bignum_o.shifter_b_en          = alu_bignum_shifter_b_en;
  assign alu_predec_bignum_o.logic_a_en            = alu_bignum_logic_a_en;
  assign alu_predec_bignum_o.logic_shifter_en      = alu_bignum_logic_shifter_en;

  assign mac_predec_bignum_o.op_en     = mac_bignum_op_en;
  assign mac_predec_bignum_o.acc_rd_en = mac_bignum_acc_rd_en;

  assign insn_rs1 = imem_rdata_i[19:15];
  assign insn_rs2 = imem_rdata_i[24:20];
  assign insn_rd  = imem_rdata_i[11:7];

  prim_onehot_enc #(
    .OneHotWidth(NWdr)
  ) rf_ren_a_bignum_onehot_enc (
    .in_i  (insn_rs1),
    .en_i  (rf_ren_a_bignum),
    .out_o (rf_predec_bignum_o.rf_ren_a)
  );

  prim_onehot_enc #(
    .OneHotWidth(NWdr)
  ) rf_ren_b_bignum_onehot_enc (
    .in_i  (insn_rs2),
    .en_i  (rf_ren_b_bignum),
    .out_o (rf_predec_bignum_o.rf_ren_b)
  );

  prim_onehot_enc #(
    .OneHotWidth(NWdr)
  ) rf_we_bignum_onehot_enc (
    .in_i  (insn_rd),
    .en_i  (rf_we_bignum),
    .out_o (rf_predec_bignum_o.rf_we)
  );

  prim_onehot_enc #(
    .OneHotWidth(NIspr)
  ) ispr_rd_en_onehot_enc (
    .in_i  (ispr_addr),
    .en_i  (ispr_rd_en),
    .out_o (ispr_predec_bignum_o.ispr_rd_en)
  );

  prim_onehot_enc #(
    .OneHotWidth(NIspr)
  ) ispr_wr_en_onehot_enc (
    .in_i  (ispr_addr),
    .en_i  (ispr_wr_en),
    .out_o (ispr_predec_bignum_o.ispr_wr_en)
  );

  logic unused_clk, unused_rst;

  assign unused_clk = clk_i;
  assign unused_rst = rst_ni;

  `ASSERT(RFRenABignumOnehot, $onehot0(rf_predec_bignum_o.rf_ren_a))
  `ASSERT(RFRenBBignumOnehot, $onehot0(rf_predec_bignum_o.rf_ren_b))
  `ASSERT(RFWeBignumOnehot,   $onehot0(rf_predec_bignum_o.rf_we))
endmodule
