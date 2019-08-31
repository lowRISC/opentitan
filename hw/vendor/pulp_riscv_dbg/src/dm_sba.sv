/* Copyright 2018 ETH Zurich and University of Bologna.
 * Copyright and related rights are licensed under the Solderpad Hardware
 * License, Version 0.51 (the “License”); you may not use this file except in
 * compliance with the License.  You may obtain a copy of the License at
 * http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
 * or agreed to in writing, software, hardware and materials distributed under
 * this License is distributed on an “AS IS” BASIS, WITHOUT WARRANTIES OR
 * CONDITIONS OF ANY KIND, either express or implied. See the License for the
 * specific language governing permissions and limitations under the License.
 *
 * File:   dm_sba.sv
 * Author: Florian Zaruba <zarubaf@iis.ee.ethz.ch>
 * Date:   1.8.2018
 *
 * Description: System Bus Access Module
 *
 */
module dm_sba #(
    parameter int BusWidth = -1
) (
    input  logic                   clk_i,       // Clock
    input  logic                   rst_ni,
    input  logic                   dmactive_i,  // synchronous reset active low

    output logic                   master_req_o,
    output logic [BusWidth-1:0]    master_add_o,
    output logic                   master_we_o,
    output logic [BusWidth-1:0]    master_wdata_o,
    output logic [BusWidth/8-1:0]  master_be_o,
    input  logic                   master_gnt_i,
    input  logic                   master_r_valid_i,
    input  logic [BusWidth-1:0]    master_r_rdata_i,

    input  logic [BusWidth-1:0]    sbaddress_i,
    input  logic                   sbaddress_write_valid_i,
    // control signals in
    input  logic                   sbreadonaddr_i,
    output logic [BusWidth-1:0]    sbaddress_o,
    input  logic                   sbautoincrement_i,
    input  logic [2:0]             sbaccess_i,
    // data in
    input  logic                   sbreadondata_i,
    input  logic [BusWidth-1:0]    sbdata_i,
    input  logic                   sbdata_read_valid_i,
    input  logic                   sbdata_write_valid_i,
    // read data out
    output logic [BusWidth-1:0]    sbdata_o,
    output logic                   sbdata_valid_o,
    // control signals
    output logic                   sbbusy_o,
    output logic                   sberror_valid_o, // bus error occurred
    output logic [2:0]             sberror_o // bus error occurred
);

    typedef enum logic [2:0] { Idle, Read, Write, WaitRead, WaitWrite } state_e;
    state_e state_d, state_q;

    logic [BusWidth-1:0]   address;
    logic                  req;
    logic                  gnt;
    logic                  we;
    logic [BusWidth/8-1:0] be;

    assign sbbusy_o = (state_q != Idle) ? 1'b1 : 1'b0;

    always_comb begin
        req     = 1'b0;
        address = sbaddress_i;
        we      = 1'b0;
        be      = '0;

        sberror_o       = '0;
        sberror_valid_o = 1'b0;
        sbaddress_o     = sbaddress_i;

        state_d = state_q;

        case (state_q)
            Idle: begin
                // debugger requested a read
                if (sbaddress_write_valid_i && sbreadonaddr_i)  state_d = Read;
                // debugger requested a write
                if (sbdata_write_valid_i) state_d = Write;
                // perform another read
                if (sbdata_read_valid_i && sbreadondata_i) state_d = Read;
            end

            Read: begin
                req = 1'b1;
                if (gnt) state_d = WaitRead;
            end

            Write: begin
                req = 1'b1;
                we  = 1'b1;
                // generate byte enable mask
                case (sbaccess_i)
                    3'b000: begin
                        if (BusWidth == 64) be[ sbaddress_i[2:0]] = '1;
                        else                be[ sbaddress_i[1:0]] = '1;
                    end
                    3'b001: begin
                        if (BusWidth == 64) be[{sbaddress_i[2:1], 1'b0} +: 2] = '1;
                        else                be[{sbaddress_i[1:1], 1'b0} +: 2] = '1;
                    end
                    3'b010: begin
                        if (BusWidth == 64) be[{sbaddress_i[2:2], 2'b0} +: 4] = '1;
                        else                be = '1;
                    end
                    3'b011: be = '1;
                    default:;
                endcase
                if (gnt) state_d = WaitWrite;
            end

            WaitRead: begin
                if (sbdata_valid_o) begin
                    state_d = Idle;
                    // auto-increment address
                    if (sbautoincrement_i) sbaddress_o = sbaddress_i + (1'b1 << sbaccess_i);
                end
            end

            WaitWrite: begin
                if (sbdata_valid_o) begin
                    state_d = Idle;
                    // auto-increment address
                    if (sbautoincrement_i) sbaddress_o = sbaddress_i + (1'b1 << sbaccess_i);
                end
            end

            default:;
        endcase

        // handle error case
        if (sbaccess_i > 3 && state_q != Idle) begin
            req             = 1'b0;
            state_d         = Idle;
            sberror_valid_o = 1'b1;
            sberror_o       = 3'd3;
        end
        // further error handling should go here ...
    end

    always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
            state_q <= Idle;
        end else begin
            state_q <= state_d;
        end
    end

    assign master_req_o    = req;
    assign master_add_o    = address[BusWidth-1:0];
    assign master_we_o     = we;
    assign master_wdata_o  = sbdata_i[BusWidth-1:0];
    assign master_be_o     = be[BusWidth/8-1:0];
    assign gnt             = master_gnt_i;
    assign sbdata_valid_o  = master_r_valid_i;
    assign sbdata_o        = master_r_rdata_i[BusWidth-1:0];


    //pragma translate_off
    `ifndef VERILATOR
        // maybe bump severity to $error if not handled at runtime
        dm_sba_access_size: assert property(@(posedge clk_i) disable iff (dmactive_i !== 1'b0)
            (state_d != Idle) |-> (sbaccess_i < 4))
        else
            $warning ("accesses > 8 byte not supported at the moment");
    `endif
    //pragma translate_on

endmodule
