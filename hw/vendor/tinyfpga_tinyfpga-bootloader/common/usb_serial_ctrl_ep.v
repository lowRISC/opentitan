module usb_serial_ctrl_ep (
  input clk,
  input reset,
  output [6:0] dev_addr,

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
  output in_ep_req,
  input in_ep_grant,
  input in_ep_data_free,
  output in_ep_data_put,
  output reg [7:0] in_ep_data = 0,
  output in_ep_data_done,
  output reg in_ep_stall,
  input in_ep_acked
);
  

  localparam IDLE = 0;
  localparam SETUP = 1;
  localparam DATA_IN = 2;
  localparam DATA_OUT = 3;
  localparam STATUS_IN = 4;
  localparam STATUS_OUT = 5;
  
  reg [5:0] ctrl_xfr_state = IDLE;
  reg [5:0] ctrl_xfr_state_next;
 
 
 
  reg setup_stage_end = 0;
  reg data_stage_end = 0;
  reg status_stage_end = 0;
  reg send_zero_length_data_pkt = 0;



  // the default control endpoint gets assigned the device address
  reg [6:0] dev_addr_i = 0;
  assign dev_addr = dev_addr_i;

  assign out_ep_req = out_ep_data_avail;
  assign out_ep_data_get = out_ep_data_avail;
  reg out_ep_data_valid = 0;
  always @(posedge clk) out_ep_data_valid <= out_ep_data_avail && out_ep_grant;

  // need to record the setup data
  reg [3:0] setup_data_addr = 0;
  reg [9:0] raw_setup_data [7:0];

  wire [7:0] bmRequestType = raw_setup_data[0];
  wire [7:0] bRequest = raw_setup_data[1];
  wire [15:0] wValue = {raw_setup_data[3][7:0], raw_setup_data[2][7:0]};
  wire [15:0] wIndex = {raw_setup_data[5][7:0], raw_setup_data[4][7:0]};
  wire [15:0] wLength = {raw_setup_data[7][7:0], raw_setup_data[6][7:0]};

  // keep track of new out data start and end
  wire pkt_start;
  wire pkt_end;

  rising_edge_detector detect_pkt_start (
    .clk(clk),
    .in(out_ep_data_avail),
    .out(pkt_start)
  );

  falling_edge_detector detect_pkt_end (
    .clk(clk),
    .in(out_ep_data_avail),
    .out(pkt_end)
  );

  assign out_ep_stall = 1'b0;

  wire setup_pkt_start = pkt_start && out_ep_setup;

  wire has_data_stage = wLength != 16'b0000000000000000;

  wire out_data_stage;
  assign out_data_stage = has_data_stage && !bmRequestType[7];

  wire in_data_stage;
  assign in_data_stage = has_data_stage && bmRequestType[7];

  reg [7:0] bytes_sent = 0;
  reg [6:0] rom_length = 0;

  wire all_data_sent = 
    (bytes_sent >= rom_length) ||
    (bytes_sent >= wLength);

  wire more_data_to_send =
    !all_data_sent;

  wire in_data_transfer_done;

  rising_edge_detector detect_in_data_transfer_done (
    .clk(clk),
    .in(all_data_sent),
    .out(in_data_transfer_done)
  );

  assign in_ep_data_done = (in_data_transfer_done && ctrl_xfr_state == DATA_IN) || send_zero_length_data_pkt;

  assign in_ep_req = ctrl_xfr_state == DATA_IN && more_data_to_send;
  assign in_ep_data_put = ctrl_xfr_state == DATA_IN && more_data_to_send && in_ep_data_free;


  reg [6:0] rom_addr = 0;

  reg save_dev_addr = 0;
  reg [6:0] new_dev_addr = 0;

  ////////////////////////////////////////////////////////////////////////////////
  // control transfer state machine
  ////////////////////////////////////////////////////////////////////////////////


  always @* begin
    setup_stage_end <= 0;
    data_stage_end <= 0;
    status_stage_end <= 0;
    send_zero_length_data_pkt <= 0;

    case (ctrl_xfr_state)
      IDLE : begin
        if (setup_pkt_start) begin
          ctrl_xfr_state_next <= SETUP;
        end else begin
          ctrl_xfr_state_next <= IDLE;
        end
      end

      SETUP : begin
        if (pkt_end) begin
          setup_stage_end <= 1;

          if (in_data_stage) begin
            ctrl_xfr_state_next <= DATA_IN;

          end else if (out_data_stage) begin
            ctrl_xfr_state_next <= DATA_OUT;

          end else begin
            ctrl_xfr_state_next <= STATUS_IN;
            send_zero_length_data_pkt <= 1;
          end

        end else begin
          ctrl_xfr_state_next <= SETUP;
        end
      end

      DATA_IN : begin
	if (in_ep_stall) begin
          ctrl_xfr_state_next <= IDLE;
          data_stage_end <= 1;
          status_stage_end <= 1;

	end else if (in_ep_acked && all_data_sent) begin
          ctrl_xfr_state_next <= STATUS_OUT;
          data_stage_end <= 1;

        end else begin
          ctrl_xfr_state_next <= DATA_IN;
        end
      end

      DATA_OUT : begin
        if (out_ep_acked) begin
          ctrl_xfr_state_next <= STATUS_IN;
          send_zero_length_data_pkt <= 1;
          data_stage_end <= 1;
          
        end else begin
          ctrl_xfr_state_next <= DATA_OUT;
        end
      end

      STATUS_IN : begin
        if (in_ep_acked) begin
          ctrl_xfr_state_next <= IDLE;
          status_stage_end <= 1;
          
        end else begin
          ctrl_xfr_state_next <= STATUS_IN;
        end
      end

      STATUS_OUT: begin
        if (out_ep_acked) begin
          ctrl_xfr_state_next <= IDLE;
          status_stage_end <= 1;
          
        end else begin
          ctrl_xfr_state_next <= STATUS_OUT;
        end
      end

      default begin
        ctrl_xfr_state_next <= IDLE;
      end
    endcase
  end

  always @(posedge clk) begin
    if (reset) begin
      ctrl_xfr_state <= IDLE;
    end else begin
      ctrl_xfr_state <= ctrl_xfr_state_next;
    end
  end

  always @(posedge clk) begin
    in_ep_stall <= 0;

    if (out_ep_setup && out_ep_data_valid) begin
      raw_setup_data[setup_data_addr] <= out_ep_data;
      setup_data_addr <= setup_data_addr + 1;
    end

    if (setup_stage_end) begin
      case (bRequest)
        'h06 : begin
          // GET_DESCRIPTOR
          case (wValue[15:8]) 
            1 : begin
              // DEVICE
              rom_addr    <= 'h00; 
              rom_length  <= 'h12;
            end 

            2 : begin
              // CONFIGURATION
              rom_addr    <= 'h12; 
              rom_length  <= 'h43;
            end 
            
            6 : begin
              // DEVICE_QUALIFIER
              in_ep_stall <= 1;
              rom_addr   <= 'h00;
              rom_length <= 'h00;
            end
            
          endcase
        end

        'h05 : begin
          // SET_ADDRESS
          rom_addr   <= 'h00;
          rom_length <= 'h00;

          // we need to save the address after the status stage ends
          // this is because the status stage token will still be using
          // the old device address
          save_dev_addr <= 1;
          new_dev_addr <= wValue[6:0]; 
        end

        'h09 : begin
          // SET_CONFIGURATION
          rom_addr   <= 'h00;
          rom_length <= 'h00;
        end

        'h20 : begin
          // SET_LINE_CODING
          rom_addr   <= 'h00;
          rom_length <= 'h00;
        end

        'h21 : begin
          // GET_LINE_CODING
          rom_addr   <= 'h55;
          rom_length <= 'h07;
        end

        'h22 : begin
          // SET_CONTROL_LINE_STATE
          rom_addr   <= 'h00;
          rom_length <= 'h00;
        end

        'h23 : begin
          // SEND_BREAK
          rom_addr   <= 'h00;
          rom_length <= 'h00;
        end

        default begin
          rom_addr   <= 'h00;
          rom_length <= 'h00;
        end
      endcase
    end

    if (ctrl_xfr_state == DATA_IN && more_data_to_send && in_ep_grant && in_ep_data_free) begin
      rom_addr <= rom_addr + 1;
      bytes_sent <= bytes_sent + 1;
    end

    if (status_stage_end) begin
      setup_data_addr <= 0;      
      bytes_sent <= 0;
      rom_addr <= 0;
      rom_length <= 0;

      if (save_dev_addr) begin
        save_dev_addr <= 0;
        dev_addr_i <= new_dev_addr; 
      end 
    end

    if (reset) begin
      dev_addr_i <= 0;
      setup_data_addr <= 0;
      save_dev_addr <= 0;
    end
  end


  `define CDC_ACM_ENDPOINT 2 
  `define CDC_RX_ENDPOINT 1
  `define CDC_TX_ENDPOINT 1
	

  always @* begin
    case (rom_addr)
      // device descriptor
      'h000 : in_ep_data <= 18; // bLength
      'h001 : in_ep_data <= 1; // bDescriptorType
      'h002 : in_ep_data <= 'h00; // bcdUSB[0]
      'h003 : in_ep_data <= 'h02; // bcdUSB[1]
      'h004 : in_ep_data <= 'h02; // bDeviceClass (Communications Device Class)
      'h005 : in_ep_data <= 'h00; // bDeviceSubClass (Abstract Control Model)
      'h006 : in_ep_data <= 'h00; // bDeviceProtocol (No class specific protocol required)
      'h007 : in_ep_data <= 32; // bMaxPacketSize0

      'h008 : in_ep_data <= 'h50; // idVendor[0] http://wiki.openmoko.org/wiki/USB_Product_IDs
      'h009 : in_ep_data <= 'h1d; // idVendor[1]
      'h00A : in_ep_data <= 'h30; // idProduct[0]
      'h00B : in_ep_data <= 'h61; // idProduct[1]
      
      'h00C : in_ep_data <= 0; // bcdDevice[0]
      'h00D : in_ep_data <= 0; // bcdDevice[1]
      'h00E : in_ep_data <= 0; // iManufacturer
      'h00F : in_ep_data <= 0; // iProduct
      'h010 : in_ep_data <= 0; // iSerialNumber
      'h011 : in_ep_data <= 1; // bNumConfigurations

      // configuration descriptor
      'h012 : in_ep_data <= 9; // bLength
      'h013 : in_ep_data <= 2; // bDescriptorType
      'h014 : in_ep_data <= (9+9+5+5+4+5+7+9+7+7); // wTotalLength[0] 
      'h015 : in_ep_data <= 0; // wTotalLength[1]
      'h016 : in_ep_data <= 2; // bNumInterfaces
      'h017 : in_ep_data <= 1; // bConfigurationValue
      'h018 : in_ep_data <= 0; // iConfiguration
      'h019 : in_ep_data <= 'hC0; // bmAttributes
      'h01A : in_ep_data <= 50; // bMaxPower
      
      // interface descriptor, USB spec 9.6.5, page 267-269, Table 9-12
      'h01B : in_ep_data <= 9; // bLength
      'h01C : in_ep_data <= 4; // bDescriptorType
      'h01D : in_ep_data <= 0; // bInterfaceNumber
      'h01E : in_ep_data <= 0; // bAlternateSetting
      'h01F : in_ep_data <= 1; // bNumEndpoints
      'h020 : in_ep_data <= 2; // bInterfaceClass (Communications Device Class)
      'h021 : in_ep_data <= 2; // bInterfaceSubClass (Abstract Control Model)
      'h022 : in_ep_data <= 1; // bInterfaceProtocol (AT Commands: V.250 etc)
      'h023 : in_ep_data <= 0; // iInterface

      // CDC Header Functional Descriptor, CDC Spec 5.2.3.1, Table 26
      'h024 : in_ep_data <= 5;					// bFunctionLength
	    'h025 : in_ep_data <= 'h24;					// bDescriptorType
	    'h026 : in_ep_data <= 'h00;					// bDescriptorSubtype
	    'h027 : in_ep_data <= 'h10; 
      'h028 : in_ep_data <= 'h01;				// bcdCDC

	    // Call Management Functional Descriptor, CDC Spec 5.2.3.2, Table 27
	    'h029 : in_ep_data <= 5;					// bFunctionLength
	    'h02A : in_ep_data <= 'h24;					// bDescriptorType
	    'h02B : in_ep_data <= 'h01;					// bDescriptorSubtype
	    'h02C : in_ep_data <= 'h00;					// bmCapabilities
	    'h02D : in_ep_data <= 1;					// bDataInterface

	    // Abstract Control Management Functional Descriptor, CDC Spec 5.2.3.3, Table 28
	    'h02E : in_ep_data <= 4;					// bFunctionLength
	    'h02F : in_ep_data <= 'h24;					// bDescriptorType
	    'h030 : in_ep_data <= 'h02;					// bDescriptorSubtype
	    'h031 : in_ep_data <= 'h06;					// bmCapabilities

	    // Union Functional Descriptor, CDC Spec 5.2.3.8, Table 33
    	'h032 : in_ep_data <= 5;					// bFunctionLength
    	'h033 : in_ep_data <= 'h24;					// bDescriptorType
    	'h034 : in_ep_data <= 'h06;					// bDescriptorSubtype
    	'h035 : in_ep_data <= 0;					// bMasterInterface
    	'h036 : in_ep_data <= 1;					// bSlaveInterface0

    	// endpoint descriptor, USB spec 9.6.6, page 269-271, Table 9-13
    	'h037 : in_ep_data <= 7;					// bLength
    	'h038 : in_ep_data <= 5;					// bDescriptorType
    	'h039 : in_ep_data <= `CDC_ACM_ENDPOINT | 'h80;		// bEndpointAddress
    	'h03A : in_ep_data <= 'h03;					// bmAttributes (0x03=intr)
    	'h03B : in_ep_data <= 8;     // wMaxPacketSize[0]
      'h03C : in_ep_data <= 0;			// wMaxPacketSize[1]
    	'h03D : in_ep_data <= 64;					// bInterval

    	// interface descriptor, USB spec 9.6.5, page 267-269, Table 9-12
    	'h03E : in_ep_data <= 9;					// bLength
    	'h03F : in_ep_data <= 4;					// bDescriptorType
    	'h040 : in_ep_data <= 1;					// bInterfaceNumber
    	'h041 : in_ep_data <= 0;					// bAlternateSetting
    	'h042 : in_ep_data <= 2;					// bNumEndpoints
    	'h043 : in_ep_data <= 'h0A;					// bInterfaceClass
    	'h044 : in_ep_data <= 'h00;					// bInterfaceSubClass
    	'h045 : in_ep_data <= 'h00;					// bInterfaceProtocol
    	'h046 : in_ep_data <= 0;					// iInterface

    	// endpoint descriptor, USB spec 9.6.6, page 269-271, Table 9-13
    	'h047 : in_ep_data <= 7;					// bLength
    	'h048 : in_ep_data <= 5;					// bDescriptorType
    	'h049 : in_ep_data <= `CDC_RX_ENDPOINT;			// bEndpointAddress
    	'h04A : in_ep_data <= 'h02;					// bmAttributes (0x02=bulk)
    	'h04B : in_ep_data <= 32; // wMaxPacketSize[0]
      'h04C : in_ep_data <= 0;				// wMaxPacketSize[1]
    	'h04D : in_ep_data <= 0;					// bInterval

    	// endpoint descriptor, USB spec 9.6.6, page 269-271, Table 9-13
    	'h04E : in_ep_data <= 7;					// bLength
    	'h04F : in_ep_data <= 5;					// bDescriptorType
    	'h050 : in_ep_data <= `CDC_TX_ENDPOINT | 'h80;			// bEndpointAddress
    	'h051 : in_ep_data <= 'h02;					// bmAttributes (0x02=bulk)

    	'h052 : in_ep_data <= 32; // wMaxPacketSize[0]
      'h053 : in_ep_data <= 0;				// wMaxPacketSize[1]
    	'h054 : in_ep_data <= 0;				// bInterval

      // LINE_CODING
      'h055 : in_ep_data <= 'h80; // dwDTERate[0]
      'h056 : in_ep_data <= 'h25; // dwDTERate[1]
      'h057 : in_ep_data <= 'h00; // dwDTERate[2]
      'h058 : in_ep_data <= 'h00; // dwDTERate[3]
      'h059 : in_ep_data <= 1; // bCharFormat (1 stop bit)
      'h05A : in_ep_data <= 0; // bParityType (None)
      'h05B : in_ep_data <= 8; // bDataBits (8 bits)

      default begin
        in_ep_data <= 0;
      end
    endcase
  end

endmodule
