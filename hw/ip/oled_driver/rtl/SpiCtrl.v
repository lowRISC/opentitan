`timescale 1ns / 1ps
//////////////////////////////////////////////////////////////////////////////////
// Company: DigilentInc
// Engineer: Arthur Brown
//
// Create Date: 09/22/2016 09:58:43 AM
// Module Name: SpiCtrl
// Project Name: OLED Demo
// Description: SPI Controller. Sends a data byte on start flag high, asserts ready high when not busy.
//
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
//
//////////////////////////////////////////////////////////////////////////////////


module SpiCtrl (
    input        clk,
    input        send_start,
    input  [7:0] send_data,
    output       send_ready,
    output       CS,
    output       SDO,
    output       SCLK
);
    localparam  Idle   = 0,
                Send   = 1,
                HoldCS = 2,
                Hold   = 3;
    localparam  COUNTER_MID = 4,
                COUNTER_MAX = 9,
                SCLK_DUTY = 5;
    reg [2:0]   state = Idle;
    reg [7:0]   shift_register=0;
    reg [3:0]   shift_counter=0;
    wire        clk_divided;
    reg [4:0]   counter=0;
    reg         temp_sdo;

    assign SCLK = (counter < SCLK_DUTY) | CS;
    assign SDO = temp_sdo | CS | (state == HoldCS ? 1'b1 : 1'b0);
    assign CS = (state != Send && state != HoldCS) ? 1'b1 : 1'b0;
    assign send_ready = (state == Idle && send_start == 1'b0) ? 1'b1 : 1'b0;

    always@(posedge clk)
        case (state)
        Idle: begin
            if (send_start == 1'b1)
                state <= Send;
        end
        Send: begin
            if (shift_counter == 8 && counter == COUNTER_MID) begin
                state <= HoldCS;
            end
        end
        HoldCS: begin
            if (shift_counter == 4'd3)
                state <= Hold;
        end
        Hold: begin
            if (send_start == 1'b0)
                state <= Idle;
        end
        endcase
    always@(posedge clk)
        if (state == Send && ~(counter == COUNTER_MID && shift_counter == 8)) begin
            if (counter == COUNTER_MAX)
                counter <= 0;
            else
                counter <= counter + 1'b1;
        end else
            counter <= 'b0;
    always@(posedge clk)
        if (state == Idle) begin
            shift_counter <= 'b0;
            shift_register <= send_data;
            temp_sdo <= 1'b1;
        end
        else if (state == Send) begin
            if (counter == COUNTER_MID) begin
//                falling <= 1'b1;
                temp_sdo <= shift_register[7];
                shift_register <= {shift_register[6:0], 1'b0};
                if (shift_counter == 4'b1000)
                    shift_counter <= 'b0;
                else
                    shift_counter <= shift_counter + 1'b1;
            end
//            end else if (clk_divided <= 1'b1)
//                falling <= 1'b0;
        end
        else if (state == HoldCS) begin
            shift_counter <= shift_counter + 1'b1;
        end
endmodule
