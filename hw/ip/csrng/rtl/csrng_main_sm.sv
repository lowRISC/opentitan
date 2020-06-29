// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
//
// Description: csrng instantiation request state machine module
//
//   handles instantiation requests from all requesting interfaces

module csrng_main_sm (
  input logic                clk_i,
  input logic                rst_ni,

   // ins req interface
  input logic                acmd_avail_i,
  output logic               acmd_accept_o,
  input logic [2:0]          acmd_i,
  input logic                acmd_eop_i,
  input logic                ctr_drbg_cmd_req_rdy_i,
  input logic                flag0_i,
  input logic                cmd_entropy_avail_i,
  output logic               instant_req_o,
  output logic               reseed_req_o,
  output logic               generate_req_o,
  output logic               update_req_o,
  output logic               uninstant_req_o
);

  typedef enum logic [2:0] {
                            INS = 3'h0,
                            RES = 3'h1,
                            GEN = 3'h2,
                            UPD = 3'h3,
                            UNI = 3'h4
                            } acmd_e;

  typedef enum logic [2:0] {
                            IDLE = 3'h0,
                            INSR = 3'h1,
                            RESR = 3'h2,
                            GENR = 3'h3,
                            UPDR = 3'h4,
                            UNIR = 3'h5
                            } state_e;

  state_e state_q, state_d;

  always_ff @(posedge clk_i or negedge rst_ni)
    if (!rst_ni) begin
      state_q    <= IDLE;
    end else begin
      state_q    <= state_d;
    end

  always_comb begin
    state_d = state_q;
    acmd_accept_o = 1'b0;
    instant_req_o = 1'b0;
    reseed_req_o = 1'b0;
    generate_req_o = 1'b0;
    update_req_o = 1'b0;
    uninstant_req_o = 1'b0;
    unique case (state_q)
//    case (state_q)
      IDLE: begin
        if (ctr_drbg_cmd_req_rdy_i) begin
          if (acmd_avail_i) begin
            acmd_accept_o = 1'b1;
            if (acmd_i == INS) begin
              if (flag0_i) begin
                state_d = INSR;
              end else begin
                if (cmd_entropy_avail_i) begin
                  state_d = INSR;
                end
              end
            end else if (acmd_i == RES) begin
              state_d = RESR;
            end else if (acmd_i == GEN) begin
              state_d = GENR;
            end else if (acmd_i == UPD) begin
              state_d = UPDR;
            end else if (acmd_i == UNI) begin
              state_d = UNIR;
            end
          end
        end
      end
      INSR: begin
        acmd_accept_o = 1'b1;
        if (acmd_eop_i) begin
          instant_req_o = 1'b1;
          state_d = IDLE;
        end
      end
      RESR: begin
        reseed_req_o = 1'b1;
        state_d = IDLE;
      end
      GENR: begin
        generate_req_o = 1'b1;
        state_d = IDLE;
      end
      UPDR: begin
        update_req_o = 1'b1;
        state_d = IDLE;
      end
      UNIR: begin
        uninstant_req_o = 1'b1;
        state_d = IDLE;
      end
      default: state_d = IDLE;
    endcase
  end

endmodule
