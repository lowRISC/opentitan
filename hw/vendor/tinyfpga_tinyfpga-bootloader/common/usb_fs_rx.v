module usb_fs_rx (
  // A 48MHz clock is required to recover the clock from the incoming data. 
  input clk_48mhz,
  input reset,

  // USB data+ and data- lines.
  input dp,
  input dn,

  // pulse on every bit transition.
  output bit_strobe,

  // Pulse on beginning of new packet.
  output pkt_start,

  // Pulse on end of current packet.
  output pkt_end,

  // Most recent packet decoded.
  output [3:0] pid,
  output reg [6:0] addr = 0,
  output reg [3:0] endp = 0,
  output reg [10:0] frame_num = 0,

  // Pulse on valid data on rx_data.
  output rx_data_put,
  output [7:0] rx_data,

  // Most recent packet passes PID and CRC checks
  output valid_packet
);
  wire clk = clk_48mhz;

  ////////////////////////////////////////////////////////////////////////////////
  ////////////////////////////////////////////////////////////////////////////////
  ////////
  //////// usb receive path
  ////////
  ////////////////////////////////////////////////////////////////////////////////
  ////////////////////////////////////////////////////////////////////////////////

  
  ////////////////////////////////////////////////////////////////////////////////
  // double flop for metastability
  /*
    all asynchronous inputs into the RTL need to be double-flopped to protect 
    against metastable scenarios.  if the RTL clock samples an asynchronous signal
    at the same time the signal is transitioning the result is undefined.  flopping
    the signal twice ensures it will be either 1 or 0 and nothing in between.
  */

  reg [3:0] dpair_q = 0;

  always @(posedge clk) begin
      dpair_q[3:0] <= {dpair_q[1:0], dp, dn};
  end


  ////////////////////////////////////////////////////////////////////////////////
  // line state recovery state machine
  /*
    the recieve path doesn't currently use a differential reciever.  because of
    this there is a chance that one of the differential pairs will appear to have
    changed to the new state while the other is still in the old state.  the 
    following state machine detects transitions and waits an extra sampling clock
    before decoding the state on the differential pair.  this transition period 
    will only ever last for one clock as long as there is no noise on the line.
    if there is enough noise on the line then the data may be corrupted and the
    packet will fail the data integrity checks.
  */

  reg [2:0] line_state = 0;
  localparam  DT = 3'b100;
  localparam  DJ = 3'b010;
  localparam  DK = 3'b001;
  localparam SE0 = 3'b000;
  localparam SE1 = 3'b011;

  wire [1:0] dpair = dpair_q[3:2];

  always @(posedge clk) begin
      case (line_state)
          // if we are in a transition state, then we can sample the pair and 
          // move to the next corresponding line state
          DT : begin
              case (dpair)
                  2'b10 : line_state <= DJ;
                  2'b01 : line_state <= DK;
                  2'b00 : line_state <= SE0;
                  2'b11 : line_state <= SE1;
              endcase
          end

          // if we are in a valid line state and the value of the pair changes,
          // then we need to move to the transition state
          DJ  : if (dpair != 2'b10) line_state <= DT;
          DK  : if (dpair != 2'b01) line_state <= DT;
          SE0 : if (dpair != 2'b00) line_state <= DT;
          SE1 : if (dpair != 2'b11) line_state <= DT;        

          // if we are in an invalid state we should move to the transition state
          default : line_state <= DT;
      endcase
  end


  ////////////////////////////////////////////////////////////////////////////////
  // clock recovery
  /*
    the DT state from the line state recovery state machine is used to align to 
    transmit clock.  the line state is sampled in the middle of the bit time.

    example of signal relationships
    -------------------------------
    line_state        DT  DJ  DJ  DJ  DT  DK  DK  DK  DK  DK  DK  DT  DJ  DJ  DJ
    line_state_valid  ________----____________----____________----________----____
    bit_phase         0   0   1   2   3   0   1   2   3   0   1   2   0   1   2
  */

  reg [1:0] bit_phase = 0;

  wire line_state_valid = (bit_phase == 1);
  assign bit_strobe = (bit_phase == 2);

  always @(posedge clk) begin
      // keep track of phase within each bit
      if (line_state == DT) begin
          bit_phase <= 0;

      end else begin
          bit_phase <= bit_phase + 1;
      end
  end


  ////////////////////////////////////////////////////////////////////////////////
  // packet detection 
  /*
    usb uses a sync to denote the beginning of a packet and two single-ended-0 to
    denote the end of a packet.  this state machine recognizes the beginning and
    end of packets for subsequent layers to process.
  */
  reg [5:0] line_history = 0;
  reg packet_valid = 0;
  reg next_packet_valid;
  wire packet_start = next_packet_valid && !packet_valid;
  wire packet_end = !next_packet_valid && packet_valid;

  always @* begin
    if (line_state_valid) begin
      // check for packet start: KJKJKK
      if (!packet_valid && line_history[5:0] == 6'b100101) begin
        next_packet_valid <= 1;
      end
 
      // check for packet end: SE0 SE0
      else if (packet_valid && line_history[3:0] == 4'b0000) begin
        next_packet_valid <= 0;

      end else begin
        next_packet_valid <= packet_valid;
      end
    end else begin
      next_packet_valid <= packet_valid;
    end
  end

  always @(posedge clk) begin
    if (reset) begin
      line_history <= 6'b101010;
      packet_valid <= 0;
    end else begin
      // keep a history of the last two states on the line
      if (line_state_valid) begin
        line_history[5:0] <= {line_history[3:0], line_state[1:0]};
      end
    end
    packet_valid <= next_packet_valid;
  end


  ////////////////////////////////////////////////////////////////////////////////
  // NRZI decode
  /*
    in order to ensure there are enough bit transitions for a receiver to recover
    the clock usb uses NRZI encoding.

    https://en.wikipedia.org/wiki/Non-return-to-zero
  */
  reg dvalid_raw;
  reg din;

  always @* begin
    case (line_history[3:0])
      4'b0101 : din <= 1;
      4'b0110 : din <= 0;
      4'b1001 : din <= 0;
      4'b1010 : din <= 1;
      default : din <= 0;
    endcase
 
    if (packet_valid && line_state_valid) begin
      case (line_history[3:0])
        4'b0101 : dvalid_raw <= 1;
        4'b0110 : dvalid_raw <= 1;
        4'b1001 : dvalid_raw <= 1;
        4'b1010 : dvalid_raw <= 1;
        default : dvalid_raw <= 0;
      endcase
    end else begin
      dvalid_raw <= 0;
    end
  end

  reg [5:0] bitstuff_history = 0;

  always @(posedge clk) begin
    if (reset || packet_end) begin
      bitstuff_history <= 6'b000000;
    end else begin
      if (dvalid_raw) begin
        bitstuff_history <= {bitstuff_history[4:0], din};
      end
    end  
  end

  assign dvalid = dvalid_raw && !(bitstuff_history == 6'b111111);


  ////////////////////////////////////////////////////////////////////////////////
  // save and check pid
  /*
    shift in the entire 8-bit pid with an additional 9th bit used as a sentinal.
  */

  reg [8:0] full_pid = 0;
  wire pid_valid = full_pid[4:1] == ~full_pid[8:5];
  wire pid_complete = full_pid[0];

  always @(posedge clk) begin
    if (packet_start) begin
      full_pid <= 9'b100000000;
    end

    if (dvalid && !pid_complete) begin
        full_pid <= {din, full_pid[8:1]};
    end
  end


  ////////////////////////////////////////////////////////////////////////////////
  // check crc5
  reg [4:0] crc5 = 0;
  wire crc5_valid = crc5 == 5'b01100;
  wire crc5_invert = din ^ crc5[4];
  always @(posedge clk) begin
    if (packet_start) begin
      crc5 <= 5'b11111;
    end

    if (dvalid && pid_complete) begin
      crc5[4] <= crc5[3];
      crc5[3] <= crc5[2];
      crc5[2] <= crc5[1] ^ crc5_invert;
      crc5[1] <= crc5[0];
      crc5[0] <= crc5_invert;
    end
  end


  ////////////////////////////////////////////////////////////////////////////////
  // check crc16
  reg [15:0] crc16 = 0;
  wire crc16_valid = crc16 == 16'b1000000000001101;
  wire crc16_invert = din ^ crc16[15];  

  always @(posedge clk) begin
    if (packet_start) begin
      crc16 <= 16'b1111111111111111;
    end

    if (dvalid && pid_complete) begin
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


  ////////////////////////////////////////////////////////////////////////////////
  // output control signals
  wire pkt_is_token = full_pid[2:1] == 2'b01;
  wire pkt_is_data = full_pid[2:1] == 2'b11;
  wire pkt_is_handshake = full_pid[2:1] == 2'b10;


  // TODO: need to check for data packet babble
  // TODO: do i need to check for bitstuff error?
  assign valid_packet = pid_valid && (
    (pkt_is_handshake) || 
    (pkt_is_data && crc16_valid) ||
    (pkt_is_token && crc5_valid)
  );
  

  reg [11:0] token_payload = 0;
  wire token_payload_done = token_payload[0];

  always @(posedge clk) begin
    if (packet_start) begin
      token_payload <= 12'b100000000000;
    end

    if (dvalid && pid_complete && pkt_is_token && !token_payload_done) begin
      token_payload <= {din, token_payload[11:1]};
    end
  end

  always @(posedge clk) begin
    if (token_payload_done && pkt_is_token) begin
      addr <= token_payload[7:1];
      endp <= token_payload[11:8];
      frame_num <= token_payload[11:1];
    end
  end

  assign pkt_start = packet_start;
  assign pkt_end = packet_end; 
  assign pid = full_pid[4:1]; 
  //assign addr = token_payload[7:1];
  //assign endp = token_payload[11:8];
  //assign frame_num = token_payload[11:1];
  

  ////////////////////////////////////////////////////////////////////////////////
  // deserialize and output data
  //assign rx_data_put = dvalid && pid_complete && pkt_is_data;
  reg [8:0] rx_data_buffer = 0;
  wire rx_data_buffer_full = rx_data_buffer[0];
  assign rx_data_put = rx_data_buffer_full;
  assign rx_data = rx_data_buffer[8:1];

  always @(posedge clk) begin
    if (packet_start || rx_data_buffer_full) begin
      rx_data_buffer <= 9'b100000000;
    end

    if (dvalid && pid_complete && pkt_is_data) begin
        rx_data_buffer <= {din, rx_data_buffer[8:1]};
    end
  end

endmodule // usb_fs_rx
