// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class usbdev_env_cov extends cip_base_env_cov #(.CFG_T(usbdev_env_cfg));
  `uvm_component_utils(usbdev_env_cov)

  // All of the Packet IDentifiers that the DUT should expect to see from the USB host controller.
  covergroup pids_to_dut_cg with function sample(pid_type_e pid);
    cp_pid: coverpoint pid {
      bins sof   = {PidTypeSofToken};
      bins setup = {PidTypeSetupToken};
      bins out   = {PidTypeOutToken};
      bins in    = {PidTypeInToken};
      bins data0 = {PidTypeData0};
      bins data1 = {PidTypeData1};
      bins ack   = {PidTypeAck};
      bins nak   = {PidTypeNak};
      // Not directly relevant to USBDEV function, but we must appropriately ignore it and the
      // ensuing Low Speed traffic.
      bins pre   = {PidTypePre};
    }
  endgroup

  // All of the PIDs that the DUT sends to the host in response.
  covergroup pids_from_dut_cg with function sample(pid_type_e pid);
    cp_pid: coverpoint pid {
      bins data0 = {PidTypeData0};
      bins data1 = {PidTypeData1};
      bins ack   = {PidTypeAck};
      bins nak   = {PidTypeNak};
      bins stall = {PidTypeStall};
    }
  endgroup

  covergroup framenum_rx_cg with function sample(bit [10:0] frame);
    cp_frame: coverpoint frame {
      bins zero = {0};
      bins one  = {1};
      bins range_2_to_15 = {[2:15]};
      bins range_16_to_127 = {[16:127]};
      bins range_128_to_1023 = {[128:1023]};
      bins range_1024_to_2046 = {[1024:2046]};
      bins max  = {2047};
    }
  endgroup

  covergroup crc16_cg with function sample(bit dir_in, bit [15:0] crc16);
    cp_crc16: coverpoint crc16 {
      // Contrive a packet that results in all 1s.
      bins all_ones = {65535};
      // At least one of these shall have been encountered, because the presence of six consecutive
      // ones necessitates bit stuffing.
      bins six_ones = {63, 126, 252, 504, 1008, 2016, 4032, 8064, 16128, 32256};
    }
    cp_dir: coverpoint dir_in;

    cr_crc16_X_dir: cross
      cp_crc16,
      cp_dir;
  endgroup

  covergroup crc5_cg with function sample(bit dir_in, bit [4:0] crc5);
    cp_crc5: coverpoint crc5 {
      bins trailing_zero = {15};
      bins leading_zero = {30};
      bins all_ones = {31};
    }
    cp_dir: coverpoint dir_in;

    cr_crc5_X_dir: cross
      cp_crc5,
      cp_dir;
  endgroup

  covergroup address_cg with function sample(bit [6:0] address, bit [4:0] endp);
    // In the address field, which is 7 bits, there could be three 1 bits from the
    // OUT PID: LSB 1000_0111 MSB
    // So the problem addresses would be xxxx111b and 1111110b
    // Endpoint numbers such 0111 and 0011 are more likely to cause issues
    cp_address: coverpoint address {
      bins zero = {0};  // The default address, used before the device has been configured.
      bins one  = {1};
      bins seven = {7};
      bins range_2_to_14 = {[2:14]};
      bins fifteen = {15};
      bins range_16_to_126 = {[16:126]};
      bins range_127 = {127};
    }
    cp_endp: coverpoint endp {
      bins three = {3};
      bins seven = {7};
    }

    cr_address_X_endp: cross
      cp_address,
      cp_endp;
  endgroup

  covergroup ep_out_cfg_cg with function sample(pid_type_e pid, bit out_enable, bit rxenable_setup,
                                                bit rxenable_out, bit set_nak_out, bit out_stall,
                                                bit out_iso);
    cp_pid: coverpoint pid {
      bins pkt_types[] = {PidTypeSetupToken, PidTypeOutToken};
      // The USB device shall ignore all packets commencing with a Pre PID because these are
      // Low Speed traffic intended for other devices on the bus.
      bins ignore_pre[] = {PidTypePre};
    }

    // Each endpoint has a lot of configuration options and whilst not all permutations are
    // entirely meaningful, there is a risk that some internal logic within the USB device may
    // not be fully qualified with all of the relevant configuration bits.
    //
    // OUT side configuration bits (Host sending data to Device).
    cp_out_enable:     coverpoint out_enable;
    cp_rxenable_setup: coverpoint rxenable_setup;
    cp_rxenable_out:   coverpoint rxenable_out;
    cp_set_nak_out:    coverpoint set_nak_out;
    cp_out_iso:        coverpoint out_iso;
    cp_out_stall:      coverpoint out_stall;

    cr_pid_x_epconfig: cross
      cp_pid,
      cp_out_enable,
      cp_rxenable_setup,
      cp_rxenable_out,
      cp_set_nak_out,
      cp_out_iso,
      cp_out_stall;
  endgroup

  covergroup ep_in_cfg_cg with function sample(pid_type_e pid,
                                               bit in_enable, bit in_stall, bit in_iso);
    cp_pid: coverpoint pid {
      bins pkt_types[] = {PidTypeInToken};
      // The USB device shall ignore all packets commencing with a Pre PID because these are
      // Low Speed traffic intended for other devices on the bus.
      bins ignore_pre[] = {PidTypePre};
    }

    // IN side configuration bits (Host retrieving data from Device).
    cp_in_enable:      coverpoint in_enable;
    cp_in_iso:         coverpoint in_iso;
    cp_in_stall:       coverpoint in_stall;

    cr_pid_x_epconfig: cross
      cp_pid,
      cp_in_enable,
      cp_in_iso,
      cp_in_stall;
  endgroup

  covergroup fifo_lvl_cg with function sample(pid_type_e pid, bit [2:0] avsetup_lvl,
                                              bit [3:0] avout_lvl, bit [3:0] rx_lvl);
    // Buffer is plucked from AV SETUP or AV OUT FIFO according to PID.
    cp_avsetup: coverpoint avsetup_lvl {
      bins empty = {0};
      bins solo  = {1};
      bins full  = {AvSetupFIFODepth};
    }
    cp_avout: coverpoint avout_lvl {
      bins empty = {0};
      bins solo  = {1};
      bins full  = {AvOutFIFODepth};
    }
    // Buffer is placed in RX FIFO, if there is space available.
    cp_rx: coverpoint rx_lvl {
      bins empty = {0};
      bins solo  = {RxFIFODepth-1};  // Single slot available, should be reserved for SETUP
      bins full  = {RxFIFODepth};
    }
    cp_pid: coverpoint pid {
      bins setup = {PidTypeSetupToken};
      bins out   = {PidTypeOutToken};
    }

    cr_fifo_X_pid: cross
      cp_avsetup,
      cp_avout,
      cp_rx,
      cp_pid;
  endgroup

  covergroup data_pkt_cg with function sample(bit dir_in, bit [6:0] pkt_len);
    // Packets are read/written from/to memory as 32-bit quantities.
    cp_pkt_len: coverpoint pkt_len {
      // Zero-length packets have special significance to Message Pipes, and are _not_ zero
      // bytes on the wire.
      bins zero  = {0};
      // Awkward lengths are those which fall just shy, align with, or just exceed word boundaries.
      bins one   = {1};
      bins three = {3};
      bins four  = {4};
      bins five  = {5};
      // Plus those where the additional bytes of the CRC16 cause the total byte count to near or
      // exceed 64.
      bins max_len_m3 = {MaxPktSizeByte-3};
      bins max_len_m2 = {MaxPktSizeByte-2};
      bins max_len_m1 = {MaxPktSizeByte-1};
      bins max_len    = {MaxPktSizeByte};
    }
    // Directions
    cp_dir: coverpoint dir_in;

    cr_pktlen_X_dir: cross
      cp_pkt_len,
      cp_dir;
  endgroup

  covergroup data_tog_endp_cg with function sample(pid_type_e pid, bit dir_in, bit [3:0] endp);
    cp_pid: coverpoint pid {
      bins data0 = {PidTypeData0};
      bins data1 = {PidTypeData1};
      bins ack = {PidTypeAck};
      bins nak = {PidTypeNak};
    }
    cp_dir: coverpoint dir_in;  // 'dir_in' is set to indicate IN
    cp_endp: coverpoint endp {
      // Device supports only 12 endpoints.
      bins endpoints[] = {[0:NEndpoints-1]};
    }

    cr_pid_X_dir_X_endp: cross
      cp_pid,
      cp_dir,
      cp_endp;
  endgroup

  covergroup pid_type_endp_cg with function sample(pid_type_e pid, bit [3:0] endp);
    cp_pid: coverpoint pid {
      bins pkt_types[] = {PidTypeSetupToken, PidTypeOutToken, PidTypeInToken};
    }
    cp_endp: coverpoint endp {
      bins endpoints[] = {[0:NEndpoints-1]};
      // Device should ignore all packets to unimplemented endpoints.
      bins invalid_ep[] = {[NEndpoints:15]};
    }

    cr_pid_X_endp: cross
      cp_pid,
      cp_endp;
  endgroup

  function new(string name, uvm_component parent);
    super.new(name, parent);
    pids_to_dut_cg = new();
    pids_from_dut_cg = new();
    framenum_rx_cg = new();
    crc16_cg = new();
    crc5_cg = new();
    address_cg = new();
    ep_out_cfg_cg = new();
    ep_in_cfg_cg = new();
    fifo_lvl_cg = new();
    data_pkt_cg = new();
    data_tog_endp_cg = new();
    pid_type_endp_cg = new();
  endfunction : new

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    // [or instantiate covergroups here]
    // Please instantiate sticky_intr_cov array of objects for all interrupts that are sticky
    // See cip_base_env_cov for details
  endfunction

endclass
