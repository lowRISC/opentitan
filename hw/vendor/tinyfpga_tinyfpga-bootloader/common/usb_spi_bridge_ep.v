module usb_spi_bridge_ep (
  input clk,
  input reset,


  ////////////////////
  // out endpoint interface 
  ////////////////////
  output out_ep_req,
  input out_ep_grant,
  input out_ep_data_avail,
  input out_ep_setup,
  output out_ep_data_get,
  input [7:0] out_ep_data,
  output out_ep_stall,
  input out_ep_acked,


  ////////////////////
  // in endpoint interface 
  ////////////////////
  output reg in_ep_req = 0,
  input in_ep_grant,
  input in_ep_data_free,
  output reg in_ep_data_put = 0,
  output [7:0] in_ep_data,
  output reg in_ep_data_done = 0,
  output in_ep_stall,
  input in_ep_acked,


  ////////////////////
  // spi interface 
  ////////////////////
  output reg spi_cs_b = 0,
  output reg spi_sck = 0,
  output spi_mosi,
  input spi_miso,

  
  ////////////////////
  // warm boot interface
  ////////////////////
  output reg boot_to_user_design = 0
);


  assign out_ep_stall = 1'b0;
  assign in_ep_stall = 1'b0;

  wire spi_byte_out_xfr_ready = out_ep_grant && out_ep_data_avail;
  wire spi_byte_in_xfr_ready = in_ep_grant && in_ep_data_free;

  reg [15:0] data_out_length = 0;
  reg [15:0] data_in_length = 0;

  reg [8:0] spi_out_data = 0;
  reg [8:0] spi_in_data = 0;


  ////////////////////////////////////////////////////////////////////////////////
  // command sequencer
  ////////////////////////////////////////////////////////////////////////////////
  reg [3:0] cmd_state = 0;
  reg [3:0] cmd_state_next = 0;

  localparam CMD_IDLE = 0;
  localparam CMD_PRE = 1;
  localparam CMD_OP_BOOT = 2;

  //localparam CMD_OP_XFR = 3;
  localparam CMD_SAVE_DOL_LO = 3;
  localparam CMD_SAVE_DOL_HI = 4;
  localparam CMD_SAVE_DIL_LO = 5;
  localparam CMD_SAVE_DIL_HI = 6;
  localparam CMD_DO_OUT = 7;
  localparam CMD_DO_IN = 9;

  reg get_cmd_out_data = 0;
  reg get_cmd_out_data_q = 0;
  reg spi_has_more_in_bytes = 0;
  reg spi_has_more_out_bytes = 0;
  reg spi_start_new_xfr = 0;


  ////////////////////////////////////////////////////////////////////////////////
  // spi protocol engine
  ////////////////////////////////////////////////////////////////////////////////
  reg [2:0] spi_state = 0;
  reg [2:0] spi_state_next = 0;
  
  localparam SPI_IDLE = 0;
  localparam SPI_START = 1;
  localparam SPI_SEND_BIT = 2;
  localparam SPI_GET_BIT = 3;
  localparam SPI_END = 4;

  reg spi_send_bit = 0;
  reg spi_get_bit = 0;
  reg get_spi_out_data = 0;
  reg put_spi_in_data = 0;
  reg reset_spi_bit_counter = 0;
  reg update_spi_byte_counters = 0;

  reg [3:0] spi_bit_counter = 0;

  reg spi_put_last_in_byte = 0;
  ////////////////////////////////////////////////////////////////////////////////
  // other glue logic
  ////////////////////////////////////////////////////////////////////////////////
  assign out_ep_req = out_ep_data_avail;
  assign out_ep_data_get = (get_spi_out_data || get_cmd_out_data) && out_ep_grant; 
  
  reg in_ep_req_i = 0;
  always @(posedge clk) in_ep_req_i <= (spi_has_more_in_bytes || spi_put_last_in_byte) && in_ep_data_free;
  always @(posedge clk) in_ep_req <= in_ep_req_i;
  always @(posedge clk) in_ep_data_put <= put_spi_in_data;
  assign in_ep_data = spi_in_data[7:0];

  assign spi_mosi = spi_out_data[8];

  wire spi_byte_done = spi_bit_counter == 4'h7;

  reg in_ep_data_done_i = 0;
  reg in_ep_data_done_q = 0;
  always @(posedge clk) in_ep_data_done_q <= in_ep_data_done_i;
  always @(posedge clk) in_ep_data_done <= in_ep_data_done_q;

  wire out_data_ready = out_ep_grant && out_ep_data_avail; 
  reg out_data_valid = 0;
  always @(posedge clk) out_data_valid <= out_data_ready;

  reg spi_dir_transition = 0;

  ////////////////////////////////////////////////////////////////////////////////
  // command sequencer
  ////////////////////////////////////////////////////////////////////////////////
  always @* begin
    get_cmd_out_data <= 1'b0;
    boot_to_user_design <= 1'b0;
    spi_put_last_in_byte <= 1'b0;
    spi_has_more_in_bytes <= 1'b0;
    spi_dir_transition <= 1'b0;
    spi_has_more_out_bytes <= 1'b0;
    in_ep_data_done_i <= 1'b0;
    spi_start_new_xfr <= 1'b0;

    case (cmd_state)
      CMD_IDLE : begin
        get_cmd_out_data <= out_data_ready;
        if (out_data_valid && out_ep_data == 8'h0) begin
          cmd_state_next <= CMD_OP_BOOT;

        end else if (out_data_valid && out_ep_data == 8'h1) begin  
          cmd_state_next <= CMD_SAVE_DOL_LO;    
  
        end else begin
          cmd_state_next <= CMD_IDLE;
        end
      end

      CMD_OP_BOOT : begin
        cmd_state_next <= CMD_OP_BOOT;
        boot_to_user_design <= 1'b1;
      end

      CMD_SAVE_DOL_LO : begin
        get_cmd_out_data <= out_data_ready;
        if (out_data_valid) begin   
          cmd_state_next <= CMD_SAVE_DOL_HI;     
  
        end else begin
          cmd_state_next <= CMD_SAVE_DOL_LO;
        end
      end

      CMD_SAVE_DOL_HI : begin
        get_cmd_out_data <= out_data_ready;
        if (out_data_valid) begin   
          cmd_state_next <= CMD_SAVE_DIL_LO;     
  
        end else begin
          cmd_state_next <= CMD_SAVE_DOL_HI;
        end
      end

      CMD_SAVE_DIL_LO : begin
        get_cmd_out_data <= out_data_ready;
        if (out_data_valid) begin   
          cmd_state_next <= CMD_SAVE_DIL_HI;     
  
        end else begin
          cmd_state_next <= CMD_SAVE_DIL_LO;
        end
      end

      
      CMD_SAVE_DIL_HI : begin
        if (out_data_valid) begin   
          cmd_state_next <= CMD_DO_OUT; 
          spi_start_new_xfr <= 1'b1;
  
        end else begin
          get_cmd_out_data <= out_data_ready;
          cmd_state_next <= CMD_SAVE_DIL_HI;
        end
      end
      

      CMD_DO_OUT : begin
        if (data_out_length == 16'h0) begin
          if (data_in_length == 16'h0) begin
            cmd_state_next <= CMD_IDLE;
          end else begin
            cmd_state_next <= CMD_DO_IN;
            spi_dir_transition <= 1'b1;
          end

        end else begin
          cmd_state_next <= CMD_DO_OUT;
          spi_has_more_out_bytes <= 1'b1;
        end
      end

      CMD_DO_IN : begin
        if (data_in_length == 0) begin
          cmd_state_next <= CMD_IDLE;
          spi_put_last_in_byte <= 1'b1;
          in_ep_data_done_i <= 1'b1;

        end else begin
          cmd_state_next <= CMD_DO_IN;
          spi_has_more_in_bytes <= 1'b1;
        end
      end

      default begin
        cmd_state_next <= CMD_IDLE;
      end
    endcase
  end

  always @(posedge clk) begin
    cmd_state <= cmd_state_next;
    get_cmd_out_data_q <= get_cmd_out_data;
    
    if (get_cmd_out_data_q) begin
      case (cmd_state)
        CMD_SAVE_DOL_LO : data_out_length[7:0] <= out_ep_data;
        CMD_SAVE_DOL_HI : data_out_length[15:8] <= out_ep_data;
        CMD_SAVE_DIL_LO : data_in_length[7:0] <= out_ep_data;
        CMD_SAVE_DIL_HI : data_in_length[15:8] <= out_ep_data;
      endcase
    end

    if (update_spi_byte_counters) begin
      case (cmd_state)
        CMD_DO_OUT : data_out_length <= data_out_length - 16'h1;
        CMD_DO_IN : data_in_length <= data_in_length - 16'h1;
      endcase
    end

  end

  ////////////////////////////////////////////////////////////////////////////////
  // spi protocol engine
  ////////////////////////////////////////////////////////////////////////////////
  always @* begin
    spi_send_bit <= 1'b0;
    spi_get_bit <= 1'b0;
    get_spi_out_data <= 1'b0;
    put_spi_in_data <= 1'b0;
    reset_spi_bit_counter <= 1'b0;
    update_spi_byte_counters <= 1'b0;

    case (spi_state)
      SPI_IDLE : begin
        spi_cs_b <= 1'b1;
        spi_sck <= 1'b1;

        if (spi_start_new_xfr) begin
          spi_state_next <= SPI_END;
          reset_spi_bit_counter <= 1'b1;

        end else begin
          spi_state_next <= SPI_IDLE;
        end
      end

      SPI_START : begin
        spi_cs_b <= 1'b0;
        spi_sck <= 1'b1;

        if (spi_has_more_out_bytes) begin
          get_spi_out_data <= 1'b1;
          spi_state_next <= SPI_SEND_BIT;
          
        end else if (spi_has_more_in_bytes || spi_dir_transition) begin
          spi_state_next <= SPI_SEND_BIT;

        end else begin
          spi_state_next <= SPI_START;
        end
      end

      SPI_SEND_BIT : begin
        spi_cs_b <= 1'b0;
        spi_sck <= 1'b1;
        spi_send_bit <= 1'b1;

        spi_state_next <= SPI_GET_BIT;
      end


      SPI_GET_BIT : begin
        spi_cs_b <= 1'b0;
        spi_sck <= 1'b0;
        spi_get_bit <= 1'b1;

        if (spi_byte_done) begin
          update_spi_byte_counters <= 1'b1;
          spi_state_next <= SPI_END;

        end else begin
          spi_state_next <= SPI_SEND_BIT;
        end
      end

      SPI_END : begin
        spi_cs_b <= 1'b0;
        spi_sck <= 1'b1;
        reset_spi_bit_counter <= 1'b1;

        if (spi_has_more_out_bytes) begin
          if (spi_byte_out_xfr_ready) begin
	    spi_state_next <= SPI_START;
          end else begin
	    spi_state_next <= SPI_END;
          end

        end else if (spi_dir_transition) begin
          spi_state_next <= SPI_START;

        end else if (spi_has_more_in_bytes) begin
          if (spi_byte_in_xfr_ready) begin
            put_spi_in_data <= 1'b1;
            spi_state_next <= SPI_START;
          end else begin
            spi_state_next <= SPI_END;
          end

        end else if (spi_put_last_in_byte) begin
          if (spi_byte_in_xfr_ready) begin
            put_spi_in_data <= 1'b1;
            spi_state_next <= SPI_IDLE;
          end else begin
            spi_state_next <= SPI_END;
          end

        end else begin
          spi_state_next <= SPI_IDLE;
        end
      end

      default begin
        spi_cs_b <= 1'b1;
        spi_sck <= 1'b1;
        spi_state_next <= SPI_IDLE;
      end
    endcase    
  end

  reg get_spi_out_data_q = 0;
  always @(posedge clk) get_spi_out_data_q <= get_spi_out_data;

  reg spi_get_bit_q = 0;
  always @(posedge clk) spi_get_bit_q <= spi_get_bit;
  always @(posedge clk) begin
    spi_state <= spi_state_next;

    if (spi_get_bit_q) begin
      spi_in_data <= {spi_in_data[7:0], spi_miso};
      spi_bit_counter <= spi_bit_counter + 4'h1;
    end
    
    if (reset_spi_bit_counter) begin
      spi_bit_counter <= 4'h0;
    end

    if (spi_send_bit) begin
      if (get_spi_out_data_q) begin
        spi_out_data <= {out_ep_data[7:0], 1'b0};
      end else begin
        spi_out_data <= {spi_out_data[7:0], 1'b0};
      end
    end else if (get_spi_out_data_q) begin
      spi_out_data <= out_ep_data;
    end
  end 
endmodule