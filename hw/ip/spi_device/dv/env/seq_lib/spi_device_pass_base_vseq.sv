// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Passthrough base sequence
class spi_device_pass_base_vseq extends spi_device_base_vseq;
  `uvm_object_utils(spi_device_pass_base_vseq)
  `uvm_object_new

  // Task for adding cmd info
  virtual task config_all_cmd_infos();
    spi_flash_cmd_info info = spi_flash_cmd_info::type_id::create("info");
    // Configure the first 11 commands which are fixed
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes == 0 &&
      info.op_code == READ_STATUS_1 &&
      info.num_lanes == 1 &&
      info.write_command == 0;)
    add_cmd_info(info, 0);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes == 0 &&
      info.op_code == READ_STATUS_2;
      info.num_lanes == 1 &&
      info.write_command == 0;)
    add_cmd_info(info, 1);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes == 0 &&
      info.op_code == READ_STATUS_3 &&
      info.num_lanes == 1 &&
      info.write_command == 0;)
    add_cmd_info(info, 2);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes == 0 &&
      info.op_code == READ_JEDEC &&
      info.num_lanes == 1 &&
      info.write_command == 0;)
    add_cmd_info(info, 3);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes == 0 &&
      info.op_code == READ_SFDP;
      info.num_lanes == 1 &&
      info.write_command == 0;)
    add_cmd_info(info, 4);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes > 0 &&
      info.op_code == READ_NORMAL &&
      info.num_lanes == 1 &&
      info.write_command == 0;)
    add_cmd_info(info, 5);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes > 0 &&
      info.op_code == READ_FAST &&
      info.num_lanes == 1 &&
      info.write_command == 0;)
    add_cmd_info(info, 6);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes > 0 &&
      info.op_code == READ_DUAL &&
      info.write_command == 0 &&
      info.num_lanes == 2;)
    add_cmd_info(info, 7);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes > 0 &&
      info.op_code == READ_QUAD &&
      info.write_command == 0 &&
      info.num_lanes == 4;)
    add_cmd_info(info, 8);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes > 0 &&
      info.op_code == READ_DUALIO &&
      info.write_command == 0 &&
      info.num_lanes == 2;)
    add_cmd_info(info, 9);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes > 0 &&
      info.op_code == READ_QUADIO &&
      info.write_command == 0 &&
      info.num_lanes == 4;)
    add_cmd_info(info, 10);
    for (int i = 11; i < 24; i++) begin
      info = spi_flash_cmd_info::type_id::create("info");
      `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
        foreach (cfg.m_spi_agent_cfg.cmd_infos[j]) {info.op_code != j;})
      add_cmd_info(info, i);
    end
  endtask : config_all_cmd_infos

  // Task for flash or pass init
  virtual task spi_device_flash_pass_init(device_mode_e mode);
    bit use_addr_4b_enable; // Mode of config
    spi_device_init();
    `uvm_info(`gfn, "Initialize flash/passthrough mode", UVM_MEDIUM)
    `DV_CHECK_STD_RANDOMIZE_FATAL(use_addr_4b_enable)
    // TODO, fixed config for now
    cfg.m_spi_agent_cfg.sck_polarity[0] = 0;
    cfg.m_spi_agent_cfg.sck_phase[0] = 0;
    cfg.spi_device_agent_cfg.sck_polarity[0] = 0;
    cfg.spi_device_agent_cfg.sck_phase[0] = 0;

    // bit dir is only supported in fw mode. Need to be 0 for other modes
    cfg.m_spi_agent_cfg.host_bit_dir = 0;
    cfg.m_spi_agent_cfg.device_bit_dir = 0;
    cfg.spi_device_agent_cfg.host_bit_dir = 0;
    cfg.spi_device_agent_cfg.device_bit_dir = 0;

    cfg.m_spi_agent_cfg.num_bytes_per_trans_in_mon = 1;
    cfg.spi_device_agent_cfg.num_bytes_per_trans_in_mon = 1;
    cfg.m_spi_agent_cfg.is_flash_mode = 1;
    cfg.spi_device_agent_cfg.is_flash_mode = 1;
    // since tx/rx order are not used in flash mode, randomize them
    `DV_CHECK_RANDOMIZE_FATAL(ral.cfg.tx_order)
    `DV_CHECK_RANDOMIZE_FATAL(ral.cfg.rx_order)
    ral.cfg.addr_4b_en.set(use_addr_4b_enable);
    ral.cfg.cpol.set(1'b0);
    ral.cfg.cpha.set(1'b0);
    csr_update(.csr(ral.cfg)); // TODO check if randomization possible
    // Set the passthrough or flash mode mode
    `DV_CHECK(mode inside {FlashMode, PassthroughMode});
    if (mode == FlashMode) begin
      ral.control.mode.set(FlashMode);
    end
    if (mode == PassthroughMode) begin
      ral.control.mode.set(PassthroughMode);
    end
    csr_update(.csr(ral.control));
    config_all_cmd_infos();

    spi_device_flash_auto_rsp_nonblocking();
    randomize_mem();
  endtask : spi_device_flash_pass_init

  // Task for configuring enable/disable of command opcode
  virtual task cfg_cmd_filter(bit not_enable, bit [7:0] cmd);
    bit [7:0] cmd_position;
    bit [7:0] cmd_offset;
    // Calculate filter bit position
    cmd_position = cmd / 32;
    cmd_offset = cmd % 32;
    ral.cmd_filter[cmd_position].filter[cmd_offset].set(not_enable);
    csr_update(.csr(ral.cmd_filter[cmd_position]));
  endtask : cfg_cmd_filter

  // Task for keeping opcode integrity regardless of rx_order config
  virtual task order_cmd_bits(bit [7:0] pass_cmd, bit[23:0] pass_addr, ref bit [31:0] addr_cmd);
    bit rx_order;
    csr_rd(.ptr(ral.cfg.rx_order), .value(rx_order));
    if (rx_order == 0) begin
      pass_cmd = {<<1{pass_cmd}};
      pass_addr = {<<1{pass_addr}};
      addr_cmd = {pass_addr, pass_cmd};
    end else begin
      addr_cmd = {pass_addr, pass_cmd};
    end
  endtask : order_cmd_bits

  // Task for preparing memory buffer for read commands
  virtual task randomize_mem();
    bit [31:0] buffer_data [1024];
    `DV_CHECK_STD_RANDOMIZE_FATAL(buffer_data)
    // Prepare Buffer
    for (int i = 0; i < 1024; i++) begin // Fill buffer with random data
      mem_wr(.ptr(ral.buffer), .offset(i), .data(buffer_data[i]));
    end
  endtask : randomize_mem

  // Task for configuring cmd info slot
  virtual task add_cmd_info(spi_flash_cmd_info info, bit [4:0] idx);
    bit [3:0] lanes_en;
    addr_mode_e addr_size;
    cfg.m_spi_agent_cfg.add_cmd_info(info);
    cfg.spi_device_agent_cfg.add_cmd_info(info);

    `uvm_info(`gfn, $sformatf("Add this cmd_info \n%s", info.sprint()), UVM_MEDIUM)
    case (info.num_lanes)
      1 : lanes_en = 4'h2;
      2 : lanes_en = 4'h3;
      4 : lanes_en = 4'hF;
      default : `uvm_fatal(`gfn, $sformatf("Unsupported lanes num 0x%0h", info.num_lanes))
    endcase
    case (info.addr_bytes)
      0: addr_size = AddrDisabled;
      3: addr_size = Addr3B;
      4: addr_size = Addr4B;
      default : `uvm_fatal(`gfn, $sformatf("Unsupported addr bytes 0x%0h", info.addr_bytes))
    endcase
    ral.cmd_info[idx].addr_mode.set(addr_size);
    // if addr_size is aligned with addr_4b_en, we could use AddrCfg instead of Addr4B/Addr3B
    if (`gmv(ral.cfg.addr_4b_en) == 1 && addr_size == Addr4B ||
         `gmv(ral.cfg.addr_4b_en) == 0 && addr_size == Addr3B) begin
        if ($urandom_range(0, 1)) addr_size = AddrCfg;
    end
    ral.cmd_info[idx].addr_mode.set(addr_size);

    ral.cmd_info[idx].valid.set(1'b1); // Enable this OPCODE
    ral.cmd_info[idx].opcode.set(info.op_code);// Read Dual
    ral.cmd_info[idx].payload_en.set(lanes_en);
    ral.cmd_info[idx].payload_dir.set(!info.write_command);
    ral.cmd_info[idx].mbyte_en.set(info.num_lanes > 1);
    ral.cmd_info[idx].addr_swap_en.set(info.addr_swap);
    ral.cmd_info[idx].payload_swap_en.set(info.data_swap);
    csr_update(.csr(ral.cmd_info[idx]));
  endtask : add_cmd_info

endclass : spi_device_pass_base_vseq
