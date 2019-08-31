// The OUT Protocol Engine receives data from the host.
module usb_fs_out_pe #(
  parameter NUM_OUT_EPS = 1,
  parameter MAX_OUT_PACKET_SIZE = 32
) (
  input clk,
  input reset,
  input [NUM_OUT_EPS-1:0] reset_ep, 
  input [6:0] dev_addr,

  ////////////////////
  // endpoint interface 
  ////////////////////
  output [NUM_OUT_EPS-1:0] out_ep_data_avail,
  output reg [NUM_OUT_EPS-1:0] out_ep_setup = 0,
  input [NUM_OUT_EPS-1:0] out_ep_data_get,
  output reg [7:0] out_ep_data,
  input [NUM_OUT_EPS-1:0] out_ep_stall,
  output reg [NUM_OUT_EPS-1:0] out_ep_acked = 0,


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

  // rx_data is pushed into endpoint controller.
  input rx_data_put,
  input [7:0] rx_data,


  ////////////////////
  // tx path 
  ////////////////////

  // Strobe to send new packet.
  output reg tx_pkt_start = 0,
  input tx_pkt_end,
  output reg [3:0] tx_pid = 0
);
  ////////////////////////////////////////////////////////////////////////////////
  // endpoint state machine
  ////////////////////////////////////////////////////////////////////////////////
  localparam READY_FOR_PKT = 0;
  localparam PUTTING_PKT = 1;
  localparam GETTING_PKT = 2;
  localparam STALL = 3;
  
  reg [1:0] ep_state [NUM_OUT_EPS - 1:0];
  reg [1:0] ep_state_next [NUM_OUT_EPS - 1:0];


  ////////////////////////////////////////////////////////////////////////////////
  // out transfer state machine
  ////////////////////////////////////////////////////////////////////////////////
  localparam IDLE = 0;
  localparam RCVD_OUT = 1;
  localparam RCVD_DATA_START = 2; 
  localparam RCVD_DATA_END = 3; 
  
  reg [1:0] out_xfr_state = IDLE;
  reg [1:0] out_xfr_state_next;

  reg out_xfr_start = 0;
  reg new_pkt_end = 0;
  reg rollback_data = 0;


  reg [3:0] out_ep_num = 0;
  

  reg [NUM_OUT_EPS - 1:0] out_ep_data_avail_i = 0;
  reg [NUM_OUT_EPS - 1:0] out_ep_data_avail_j = 0;

  // set when the endpoint buffer is unable to receive the out transfer
  reg nak_out_transfer = 0;

  // data toggle state
  reg [NUM_OUT_EPS - 1:0] data_toggle = 0;

  // latched on valid OUT/SETUP token
  reg [3:0] current_endp = 0;
  wire [1:0] current_ep_state = ep_state[current_endp];

  // endpoint data buffer
  reg [7:0] out_data_buffer [(MAX_OUT_PACKET_SIZE * NUM_OUT_EPS) - 1:0];

  // current get_addr when outputting a packet from the buffer
  reg [5:0] ep_get_addr [NUM_OUT_EPS - 1:0];
  reg [5:0] ep_get_addr_next [NUM_OUT_EPS - 1:0];
  

  // endpoint put_addrs when inputting a packet into the buffer
  reg [5:0] ep_put_addr [NUM_OUT_EPS - 1:0];

  // total buffer put addr, uses endpoint number and that endpoints current
  // put address
  wire [8:0] buffer_put_addr = {current_endp[3:0], ep_put_addr[current_endp][4:0]};
  wire [8:0] buffer_get_addr = {out_ep_num[3:0], ep_get_addr[out_ep_num][4:0]};

  wire token_received = 
    rx_pkt_end &&
    rx_pkt_valid &&
    rx_pid[1:0] == 2'b01 &&
    rx_addr == dev_addr &&
    rx_endp < NUM_OUT_EPS;

  wire out_token_received =
    token_received &&
    rx_pid[3:2] == 2'b00;

  wire setup_token_received =
    token_received &&
    rx_pid[3:2] == 2'b11;

  wire invalid_packet_received =
    rx_pkt_end &&
    !rx_pkt_valid;

  wire data_packet_received =
    rx_pkt_end &&
    rx_pkt_valid &&
    rx_pid[2:0] == 3'b011;

  wire non_data_packet_received =
    rx_pkt_end &&
    rx_pkt_valid &&
    rx_pid[2:0] != 3'b011;

  //reg last_data_toggle = 0;

  wire bad_data_toggle =
    data_packet_received &&
    rx_pid[3] != data_toggle[rx_endp];

    //last_data_toggle == data_toggle[current_endp];

  ////////////////////////////////////////////////////////////////////////////////
  // endpoint state machine
  ////////////////////////////////////////////////////////////////////////////////

  genvar ep_num;
  generate
    for (ep_num = 0; ep_num < NUM_OUT_EPS; ep_num = ep_num + 1) begin
      always @* begin

        ep_state_next[ep_num] <= ep_state[ep_num];

        if (out_ep_stall[ep_num]) begin
          ep_state_next[ep_num] <= STALL;

        end else begin
          case (ep_state[ep_num])
            READY_FOR_PKT : begin
              if (out_xfr_start && rx_endp == ep_num) begin
                ep_state_next[ep_num] <= PUTTING_PKT;

              end else begin
                ep_state_next[ep_num] <= READY_FOR_PKT;
              end
            end

            PUTTING_PKT : begin
              if (new_pkt_end && current_endp == ep_num) begin
                ep_state_next[ep_num] <= GETTING_PKT;

              end else if (rollback_data && current_endp == ep_num) begin
                ep_state_next[ep_num] <= READY_FOR_PKT;

              end else begin
                ep_state_next[ep_num] <= PUTTING_PKT;
              end
            end

            GETTING_PKT : begin

              if (ep_get_addr[ep_num][5:0] >= (ep_put_addr[ep_num][5:0] - 2)) begin
                ep_state_next[ep_num] <= READY_FOR_PKT;

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

        if (ep_state_next[ep_num][1:0] == READY_FOR_PKT) begin
          ep_get_addr_next[ep_num][5:0] <= 0;
        end else if (ep_state_next[ep_num][1:0] == GETTING_PKT && out_ep_data_get[ep_num]) begin
          ep_get_addr_next[ep_num][5:0] <= ep_get_addr[ep_num][5:0] + 1;
        end else begin
          ep_get_addr_next[ep_num][5:0] <= ep_get_addr[ep_num][5:0];
        end
      end

      always @(posedge clk) begin
        if (reset || reset_ep[ep_num]) begin
          ep_state[ep_num] <= READY_FOR_PKT;
        end else begin
          ep_state[ep_num] <= ep_state_next[ep_num];
        end

        ep_get_addr[ep_num][5:0] <= ep_get_addr_next[ep_num][5:0];
      end
      

      assign out_ep_data_avail[ep_num] = 
        (ep_get_addr[ep_num][5:0] < (ep_put_addr[ep_num][5:0] - 2)) && 
        (ep_state[ep_num][1:0] == GETTING_PKT);



    end
  endgenerate

  integer i;
  always @(posedge clk) begin
    if (reset) begin
      out_ep_setup <= 0;

    end else begin
      if (setup_token_received) begin
        out_ep_setup[rx_endp] <= 1;
      end else if (out_token_received) begin
        out_ep_setup[rx_endp] <= 0;
      end
    end

    for (i = 0; i < NUM_OUT_EPS; i = i + 1) begin
      if (reset_ep[i]) begin
        out_ep_setup[i] <= 0;
      end
    end
  end

  always @(posedge clk) out_ep_data <= out_data_buffer[buffer_get_addr][7:0];

  integer ep_num_decoder;
  always @* begin
    out_ep_num <= 0;

    for (ep_num_decoder = 0; ep_num_decoder < NUM_OUT_EPS; ep_num_decoder = ep_num_decoder + 1) begin
      if (out_ep_data_get[ep_num_decoder]) begin
        out_ep_num <= ep_num_decoder; 
      end
    end
  end

  ////////////////////////////////////////////////////////////////////////////////
  // out transfer state machine
  ////////////////////////////////////////////////////////////////////////////////

  always @* begin
    out_ep_acked <= 0;
    out_xfr_start <= 0;
    out_xfr_state_next <= out_xfr_state;
    tx_pkt_start <= 0;
    tx_pid <= 0;
    new_pkt_end <= 0;
    rollback_data <= 0;

    case (out_xfr_state)
      IDLE : begin
        if (out_token_received || setup_token_received) begin
          out_xfr_state_next <= RCVD_OUT;
          out_xfr_start <= 1;

        end else begin
          out_xfr_state_next <= IDLE;
        end
      end

      RCVD_OUT : begin
        if (rx_pkt_start) begin
          out_xfr_state_next <= RCVD_DATA_START;

        end else begin
          out_xfr_state_next <= RCVD_OUT;
        end
      end

      RCVD_DATA_START : begin
        if (bad_data_toggle) begin
          out_xfr_state_next <= IDLE;
          rollback_data <= 1;
          tx_pkt_start <= 1;
          tx_pid <= 4'b0010; // ACK

        end else if (invalid_packet_received || non_data_packet_received) begin
          out_xfr_state_next <= IDLE;
          rollback_data <= 1;

        end else if (data_packet_received) begin
          out_xfr_state_next <= RCVD_DATA_END;

        end else begin
          out_xfr_state_next <= RCVD_DATA_START;
        end
      end

      RCVD_DATA_END : begin
        out_xfr_state_next <= IDLE;
        tx_pkt_start <= 1;

        if (ep_state[current_endp] == STALL) begin
          tx_pid <= 4'b1110; // STALL

        end else if (nak_out_transfer) begin
          tx_pid <= 4'b1010; // NAK
          rollback_data <= 1;

        end else begin
          tx_pid <= 4'b0010; // ACK
          new_pkt_end <= 1;
          out_ep_acked[current_endp] <= 1;

        //end else begin
        //  tx_pid <= 4'b0010; // ACK
        //  rollback_data <= 1;
        end
      end

      default begin
        out_xfr_state_next <= IDLE;
      end
    endcase
  end

  wire current_ep_busy =
    (ep_state[current_endp] == GETTING_PKT) || 
    (ep_state[current_endp] == READY_FOR_PKT);

  integer j;
  always @(posedge clk) begin
    if (reset) begin
      out_xfr_state <= IDLE;
    end else begin
      out_xfr_state <= out_xfr_state_next;

      if (out_xfr_start) begin
        current_endp <= rx_endp;
        //last_data_toggle <= setup_token_received ? 0 : data_toggle[rx_endp];
      end

      if (new_pkt_end) begin
        data_toggle[current_endp] <= !data_toggle[current_endp];
      end

      if (setup_token_received) begin
        data_toggle[rx_endp] <= 0;
      end

      case (out_xfr_state)
        IDLE : begin
        end

        RCVD_OUT : begin
          if (current_ep_busy) begin
            nak_out_transfer <= 1;
          end else begin
            nak_out_transfer <= 0;
            ep_put_addr[current_endp][5:0] <= 0;
          end
        end

        RCVD_DATA_START : begin
          if (!nak_out_transfer && rx_data_put && !ep_put_addr[current_endp][5]) begin
            out_data_buffer[buffer_put_addr][7:0] <= rx_data;
          end
          
          if (!nak_out_transfer && rx_data_put) begin
            ep_put_addr[current_endp][5:0] <= ep_put_addr[current_endp][5:0] + 1;

          end
        end

        RCVD_DATA_END : begin
        end
      endcase
    end

    for (j = 0; j < NUM_OUT_EPS; j = j + 1) begin
      if (reset || reset_ep[j]) begin
        data_toggle[j] <= 0;
        ep_put_addr[j][5:0] <= 0;
      end
    end
  end

endmodule