module usb_fs_tx (
  // A 48MHz clock is required to receive USB data at 12MHz
  // it's simpler to juse use 48MHz everywhere
  input clk_48mhz,
  input reset,

  // bit strobe from rx to align with senders clock
  input bit_strobe,

  // output enable to take ownership of bus and data out
  output reg oe = 0,
  output reg dp = 0,
  output reg dn = 0,

  // pulse to initiate new packet transmission
  input pkt_start,
  output pkt_end,

  // pid to send
  input [3:0] pid,

  // tx logic pulls data until there is nothing available
  input tx_data_avail,  
  output reg tx_data_get = 0,
  input [7:0] tx_data
);
  wire clk = clk_48mhz;

  // save packet parameters at pkt_start
  reg [3:0] pidq = 0;

  always @(posedge clk) begin
    if (pkt_start) begin
      pidq <= pid;
    end
  end

  reg [7:0] data_shift_reg = 0;
  reg [7:0] oe_shift_reg = 0;
  reg [7:0] se0_shift_reg = 0;


  wire serial_tx_data = data_shift_reg[0];
  wire serial_tx_oe = oe_shift_reg[0];
  wire serial_tx_se0 = se0_shift_reg[0];


  // serialize sync, pid, data payload, and crc16
  reg byte_strobe = 0;
  reg [2:0] bit_count = 0;

  reg [4:0] bit_history_q = 0;
  wire [5:0] bit_history = {serial_tx_data, bit_history_q};
  wire bitstuff = bit_history == 6'b111111;
  reg bitstuff_q = 0;
  reg bitstuff_qq = 0;
  reg bitstuff_qqq = 0;
  reg bitstuff_qqqq = 0;


  always @(posedge clk) begin
    bitstuff_q <= bitstuff;
    bitstuff_qq <= bitstuff_q;
    bitstuff_qqq <= bitstuff_qq;
    bitstuff_qqqq <= bitstuff_qqq;
  end

  assign pkt_end = bit_strobe && se0_shift_reg[1:0] == 2'b01;

  reg data_payload = 0;

  reg [31:0] pkt_state = 0;
  localparam IDLE = 0;
  localparam SYNC = 1;
  localparam PID = 2;
  localparam DATA_OR_CRC16_0 = 3;
  localparam CRC16_1 = 4;
  localparam EOP = 5;

  reg [15:0] crc16 = 0;

  always @(posedge clk) begin
    case (pkt_state)
      IDLE : begin
        if (pkt_start) begin
          pkt_state <= SYNC;
        end
      end

      SYNC : begin
        if (byte_strobe) begin
          pkt_state <= PID;
          data_shift_reg <= 8'b10000000;
          oe_shift_reg <= 8'b11111111;
          se0_shift_reg <= 8'b00000000;
        end
      end

      PID : begin
        if (byte_strobe) begin
          if (pidq[1:0] == 2'b11) begin
            pkt_state <= DATA_OR_CRC16_0;
          end else begin
            pkt_state <= EOP;
          end

          data_shift_reg <= {~pidq, pidq};
          oe_shift_reg <= 8'b11111111;
          se0_shift_reg <= 8'b00000000;
        end
      end

      DATA_OR_CRC16_0 : begin
        if (byte_strobe) begin
          if (tx_data_avail) begin
            pkt_state <= DATA_OR_CRC16_0;
            data_payload <= 1;
            tx_data_get <= 1;
            data_shift_reg <= tx_data;
            oe_shift_reg <= 8'b11111111;
            se0_shift_reg <= 8'b00000000;
          end else begin
            pkt_state <= CRC16_1;
            data_payload <= 0;
            tx_data_get <= 0;
            data_shift_reg <= ~{crc16[8], crc16[9], crc16[10], crc16[11], crc16[12], crc16[13], crc16[14], crc16[15]};
            oe_shift_reg <= 8'b11111111;
            se0_shift_reg <= 8'b00000000;
          end
        end else begin
          tx_data_get <= 0; 
        end
      end

      CRC16_1 : begin
        if (byte_strobe) begin
          pkt_state <= EOP;
          data_shift_reg <= ~{crc16[0], crc16[1], crc16[2], crc16[3], crc16[4], crc16[5], crc16[6], crc16[7]};
          oe_shift_reg <= 8'b11111111;
          se0_shift_reg <= 8'b00000000;
        end
      end

      EOP : begin
        if (byte_strobe) begin
          pkt_state <= IDLE;
          oe_shift_reg <= 8'b00000111;
          se0_shift_reg <= 8'b00000111;
        end
      end
    endcase

    if (bit_strobe && !bitstuff) begin
      byte_strobe <= (bit_count == 3'b000);
    end else begin
      byte_strobe <= 0;
    end

    if (pkt_start) begin
      bit_count <= 1;
      bit_history_q <= 0;

    end else if (bit_strobe) begin
      // bitstuff
      if (bitstuff /* && !serial_tx_se0*/) begin
        bit_history_q <= bit_history[5:1];
        data_shift_reg[0] <= 0;

      // normal deserialize
      end else begin
        bit_count <= bit_count + 1;

        data_shift_reg <= (data_shift_reg >> 1);
        oe_shift_reg <= (oe_shift_reg >> 1);
        se0_shift_reg <= (se0_shift_reg >> 1);

        bit_history_q <= bit_history[5:1];
      end
    end
  end



  // calculate crc16
  wire crc16_invert = serial_tx_data ^ crc16[15];  

  always @(posedge clk) begin
    if (pkt_start) begin
      crc16 <= 16'b1111111111111111;
    end

    if (bit_strobe && data_payload && !bitstuff_qqqq && !pkt_start) begin
      crc16[15] <= crc16[14] ^ crc16_invert;
      crc16[14] <= crc16[13];
      crc16[13] <= crc16[12];
      crc16[12] <= crc16[11];
      crc16[11] <= crc16[10];
      crc16[10] <= crc16[9];
      crc16[9] <= crc16[8];
      crc16[8] <= crc16[7];
      crc16[7] <= crc16[6];
      crc16[6] <= crc16[5];
      crc16[5] <= crc16[4];
      crc16[4] <= crc16[3];
      crc16[3] <= crc16[2];
      crc16[2] <= crc16[1] ^ crc16_invert;
      crc16[1] <= crc16[0];
      crc16[0] <= crc16_invert;
    end
  end

  reg [2:0] dp_eop = 0;


  // nrzi and differential driving
  always @(posedge clk) begin
    if (pkt_start) begin
      // J
      dp <= 1;
      dn <= 0;
      
      dp_eop <= 3'b100;

    end else if (bit_strobe) begin
      oe <= serial_tx_oe;

      if (serial_tx_se0) begin
        dp <= dp_eop[0];
        dn <= 0;

        dp_eop <= dp_eop >> 1;

      end else if (serial_tx_data) begin
        // value should stay the same, do nothing

      end else begin
        dp <= !dp;
        dn <= !dn;
      end
    end
  end 

endmodule
