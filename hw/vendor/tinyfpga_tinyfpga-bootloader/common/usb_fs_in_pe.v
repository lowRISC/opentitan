// The IN Protocol Engine sends data to the host.
module usb_fs_in_pe #(
  parameter NUM_IN_EPS = 11,
  parameter MAX_IN_PACKET_SIZE = 32
) (
  input clk, 
  input reset, 
  input [NUM_IN_EPS-1:0] reset_ep, 
  input [6:0] dev_addr,


  ////////////////////
  // endpoint interface 
  ////////////////////
  output reg [NUM_IN_EPS-1:0] in_ep_data_free = 0,
  input [NUM_IN_EPS-1:0] in_ep_data_put,
  input [7:0] in_ep_data,
  input [NUM_IN_EPS-1:0] in_ep_data_done,
  input [NUM_IN_EPS-1:0] in_ep_stall,
  output reg [NUM_IN_EPS-1:0] in_ep_acked = 0,


  ////////////////////
  // rx path 
  ////////////////////

  // Strobed on reception of packet.
  input rx_pkt_start,
  input rx_pkt_end,
  input rx_pkt_valid,

  // Most recent packet received.
  input [3:0] rx_pid,
  input [6:0] rx_addr,
  input [3:0] rx_endp,
  input [10:0] rx_frame_num,


  ////////////////////
  // tx path 
  ////////////////////

  // Strobe to send new packet.
  output reg tx_pkt_start = 0,
  input tx_pkt_end,


  // Packet type to send
  output reg [3:0] tx_pid = 0,

  // Data payload to send if any
  output tx_data_avail,
  input tx_data_get,
  output reg [7:0] tx_data
);

  ////////////////////////////////////////////////////////////////////////////////
  // endpoint state machine
  ////////////////////////////////////////////////////////////////////////////////
  reg [1:0] ep_state [NUM_IN_EPS - 1:0];
  reg [1:0] ep_state_next [NUM_IN_EPS - 1:0];

  // latched on valid IN token
  reg [3:0] current_endp = 0;

  wire [1:0] current_ep_state = ep_state[current_endp][1:0];

  localparam READY_FOR_PKT = 0;
  localparam PUTTING_PKT = 1;
  localparam GETTING_PKT = 2;
  localparam STALL = 3;




  ////////////////////////////////////////////////////////////////////////////////
  // in transfer state machine
  ////////////////////////////////////////////////////////////////////////////////
  localparam IDLE = 0;
  localparam RCVD_IN = 1;
  localparam SEND_DATA = 2; 
  localparam WAIT_ACK = 3; 
  
  reg [1:0] in_xfr_state = IDLE;
  reg [1:0] in_xfr_state_next;


  reg in_xfr_start = 0;
  reg in_xfr_end = 0;


  // data toggle state
  reg [NUM_IN_EPS - 1:0] data_toggle = 0;

  // endpoint data buffer
  reg [7:0] in_data_buffer [(MAX_IN_PACKET_SIZE * NUM_IN_EPS) - 1:0];
  reg [5:0] ep_put_addr [NUM_IN_EPS - 1:0];
  reg [5:0] ep_get_addr [NUM_IN_EPS - 1:0];  

  integer i = 0;
  initial begin
    for (i = 0; i < NUM_IN_EPS; i = i + 1) begin
      ep_put_addr[i] = 0;
      ep_get_addr[i] = 0;
      ep_state[i] = 0;
    end
  end

  reg [3:0] in_ep_num = 0;

  wire [8:0] buffer_put_addr = {in_ep_num[3:0], ep_put_addr[in_ep_num][4:0]};
  wire [8:0] buffer_get_addr = {current_endp[3:0], ep_get_addr[current_endp][4:0]};
  
  // endpoint data packet buffer has a data packet ready to send
  reg [NUM_IN_EPS - 1:0] endp_ready_to_send = 0;

  // endpoint has some space free in its buffer
  reg [NUM_IN_EPS - 1:0] endp_free = 0;


  wire token_received = 
    rx_pkt_end &&
    rx_pkt_valid &&
    rx_pid[1:0] == 2'b01 &&
    rx_addr == dev_addr &&
    rx_endp < NUM_IN_EPS;

  wire setup_token_received =
    token_received &&
    rx_pid[3:2] == 2'b11;

  wire in_token_received =
    token_received &&
    rx_pid[3:2] == 2'b10;

  wire ack_received =
    rx_pkt_end &&
    rx_pkt_valid &&
    rx_pid == 4'b0010;

  wire more_data_to_send = 
    ep_get_addr[current_endp][5:0] < ep_put_addr[current_endp][5:0]; 

  wire [5:0] current_ep_get_addr = ep_get_addr[current_endp][5:0];
  wire [5:0] current_ep_put_addr = ep_put_addr[current_endp][5:0];



  
  wire tx_data_avail_i =
    in_xfr_state == SEND_DATA &&
    more_data_to_send; 

  assign tx_data_avail = tx_data_avail_i;



  ////////////////////////////////////////////////////////////////////////////////
  // endpoint state machine
  ////////////////////////////////////////////////////////////////////////////////


  genvar ep_num;
  generate
    for (ep_num = 0; ep_num < NUM_IN_EPS; ep_num = ep_num + 1) begin
      always @* begin
        in_ep_acked[ep_num] <= 0;

        ep_state_next[ep_num] <= ep_state[ep_num];

        if (in_ep_stall[ep_num]) begin
          ep_state_next[ep_num] <= STALL;

        end else begin
          case (ep_state[ep_num])
            READY_FOR_PKT : begin
              ep_state_next[ep_num] <= PUTTING_PKT;
            end

            PUTTING_PKT : begin
              if (
                (
                  in_ep_data_done[ep_num] 
                ) || (
                  ep_put_addr[ep_num][5]
                )
              ) begin
                ep_state_next[ep_num] <= GETTING_PKT;

              end else begin
                ep_state_next[ep_num] <= PUTTING_PKT;
              end
            end

            GETTING_PKT : begin
              if (in_xfr_end && current_endp == ep_num) begin
                ep_state_next[ep_num] <= READY_FOR_PKT;
                in_ep_acked[ep_num] <= 1;
                
              end else begin
                ep_state_next[ep_num] <= GETTING_PKT;
              end
            end

            STALL : begin
              if (setup_token_received && rx_endp == ep_num) begin
                ep_state_next[ep_num] <= READY_FOR_PKT;

              end else begin
                ep_state_next[ep_num] <= STALL;
              end
            end

            default begin
              ep_state_next[ep_num] <= READY_FOR_PKT;
            end
          endcase
        end

        endp_free[ep_num] = !ep_put_addr[ep_num][5];
        in_ep_data_free[ep_num] = endp_free[ep_num] && ep_state[ep_num] == PUTTING_PKT;
      end

      always @(posedge clk) begin
        if (reset || reset_ep[ep_num]) begin
          ep_state[ep_num] <= READY_FOR_PKT;

        end else begin
          ep_state[ep_num] <= ep_state_next[ep_num];

          case (ep_state[ep_num])
            READY_FOR_PKT : begin
              ep_put_addr[ep_num][5:0] <= 0;
            end

            PUTTING_PKT : begin
              if (in_ep_data_put[ep_num]) begin
                ep_put_addr[ep_num][5:0] <= ep_put_addr[ep_num][5:0] + 1;
              end
            end

            GETTING_PKT : begin     
            end

            STALL : begin
            end
          endcase
        end
      end
    end
  endgenerate

  integer ep_num_decoder;
  always @* begin
    in_ep_num <= 0;

    for (ep_num_decoder = 0; ep_num_decoder < NUM_IN_EPS; ep_num_decoder = ep_num_decoder + 1) begin
      if (in_ep_data_put[ep_num_decoder]) begin
        in_ep_num <= ep_num_decoder; 
      end
    end
  end

  always @(posedge clk) begin
    case (ep_state[in_ep_num])
      PUTTING_PKT : begin
        if (in_ep_data_put[in_ep_num] && !ep_put_addr[in_ep_num][5]) begin
          in_data_buffer[buffer_put_addr] <= in_ep_data;
        end
      end
    endcase
  end


  ////////////////////////////////////////////////////////////////////////////////
  // in transfer state machine
  ////////////////////////////////////////////////////////////////////////////////

  reg rollback_in_xfr;

  always @* begin
    in_xfr_state_next <= in_xfr_state;
    in_xfr_start <= 0;
    in_xfr_end <= 0;
    tx_pkt_start <= 0;
    tx_pid <= 4'b0000;
    rollback_in_xfr <= 0;

    case (in_xfr_state)
      IDLE : begin
        rollback_in_xfr <= 1;

        if (in_token_received) begin
          in_xfr_state_next <= RCVD_IN;

        end else begin
          in_xfr_state_next <= IDLE;
        end 
      end


      RCVD_IN : begin
        tx_pkt_start <= 1;

        if (ep_state[current_endp] == STALL) begin
          in_xfr_state_next <= IDLE;
          tx_pid <= 4'b1110; // STALL

        end else if (ep_state[current_endp] == GETTING_PKT) begin
          in_xfr_state_next <= SEND_DATA;
          tx_pid <= {data_toggle[current_endp], 3'b011}; // DATA0/1
          in_xfr_start <= 1;

        end else begin
          in_xfr_state_next <= IDLE;
          tx_pid <= 4'b1010; // NAK
        end
      end


      SEND_DATA : begin
        if (!more_data_to_send) begin
          in_xfr_state_next <= WAIT_ACK;

        end else begin
          in_xfr_state_next <= SEND_DATA;
        end
      end

      WAIT_ACK : begin
        // FIXME: need to handle smash/timeout
        if (ack_received) begin
          in_xfr_state_next <= IDLE;
          in_xfr_end <= 1;

        end else if (in_token_received) begin
          in_xfr_state_next <= RCVD_IN;
          rollback_in_xfr <= 1;

        end else if (rx_pkt_end) begin
          in_xfr_state_next <= IDLE;
          rollback_in_xfr <= 1;

        end else begin
          in_xfr_state_next <= WAIT_ACK;
        end
      end
    endcase
  end

  always @(posedge clk)
      tx_data <= in_data_buffer[buffer_get_addr];

  integer j;
  always @(posedge clk) begin
    if (reset) begin
      in_xfr_state <= IDLE;

    end else begin
      in_xfr_state <= in_xfr_state_next;

      if (setup_token_received) begin
        data_toggle[rx_endp] <= 1;
      end

      if (in_token_received) begin
        current_endp <= rx_endp;
      end

      if (rollback_in_xfr) begin
        ep_get_addr[current_endp][5:0] <= 0;
      end

      case (in_xfr_state)
        IDLE : begin
        end

        RCVD_IN : begin
        end

        SEND_DATA : begin
          if (tx_data_get && tx_data_avail_i) begin
            ep_get_addr[current_endp][5:0] <= ep_get_addr[current_endp][5:0] + 1;
          end
        end

        WAIT_ACK : begin
          if (ack_received) begin
            data_toggle[current_endp] <= !data_toggle[current_endp];
          end
        end
      endcase
    end

    for (j = 0; j < NUM_IN_EPS; j = j + 1) begin
      if (reset || reset_ep[j]) begin
        data_toggle[j] <= 0;
        ep_get_addr[j][5:0] <= 0;
      end
    end
  end

endmodule