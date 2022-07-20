// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Passthrough base sequence
class spi_device_pass_base_vseq extends spi_device_base_vseq;
  // only enable this in 1-2 tests
  bit allow_set_cmd_info_invalid;
  bit allow_use_invalid_opcode;

  // knob to enable testing addr/payload swap
  bit allow_addr_swap;
  bit allow_payload_swap;
  int addr_payload_swap_pct = 30;

  bit allow_intercept;

  bit [7:0] valid_opcode_q[$];

  `uvm_object_utils(spi_device_pass_base_vseq)
  `uvm_object_new

  // Task for adding cmd info
  virtual task config_all_cmd_infos();
    spi_flash_cmd_info info = spi_flash_cmd_info::type_id::create("info");

    // clean up previous configure cmd_infos
    cfg.spi_host_agent_cfg.cmd_infos.delete();
    cfg.spi_device_agent_cfg.cmd_infos.delete();

    // Configure the first 11 commands which are fixed
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes == 0 &&
      info.opcode == READ_STATUS_1 &&
      info.num_lanes == 1 &&
      info.dummy_cycles == 0 &&
      info.write_command == 0;)
    add_cmd_info(info, 0);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes == 0 &&
      info.opcode == READ_STATUS_2;
      info.num_lanes == 1 &&
      info.dummy_cycles == 0 &&
      info.write_command == 0;)
    add_cmd_info(info, 1);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes == 0 &&
      info.opcode == READ_STATUS_3 &&
      info.num_lanes == 1 &&
      info.dummy_cycles == 0 &&
      info.write_command == 0;)
    add_cmd_info(info, 2);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes == 0 &&
      info.opcode == READ_JEDEC &&
      info.num_lanes == 1 &&
      info.dummy_cycles == 0 &&
      info.write_command == 0;)
    add_cmd_info(info, 3);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes == 0 &&
      info.opcode == READ_SFDP;
      info.num_lanes == 1 &&
      info.write_command == 0;)
    add_cmd_info(info, 4);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes > 0 &&
      info.opcode == READ_NORMAL &&
      info.num_lanes == 1 &&
      info.write_command == 0;)
    add_cmd_info(info, 5);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes > 0 &&
      info.opcode == READ_FAST &&
      info.num_lanes == 1 &&
      info.write_command == 0;)
    add_cmd_info(info, 6);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes > 0 &&
      info.opcode == READ_DUAL &&
      info.write_command == 0 &&
      info.num_lanes == 2;)
    add_cmd_info(info, 7);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes > 0 &&
      info.opcode == READ_QUAD &&
      info.write_command == 0 &&
      info.num_lanes == 4;)
    add_cmd_info(info, 8);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes > 0 &&
      info.opcode == READ_DUALIO &&
      info.write_command == 0 &&
      info.num_lanes == 2;)
    add_cmd_info(info, 9);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_bytes > 0 &&
      info.opcode == READ_QUADIO &&
      info.write_command == 0 &&
      info.num_lanes == 4;)
    add_cmd_info(info, 10);
    for (int i = 11; i < 24; i++) begin
      info = spi_flash_cmd_info::type_id::create("info");
      `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
        foreach (cfg.spi_host_agent_cfg.cmd_infos[j]) {info.opcode != j;})
      add_cmd_info(info, i);
    end

    valid_opcode_q = cfg.spi_host_agent_cfg.cmd_infos.find_index() with ('1);
  endtask : config_all_cmd_infos

  // Task for flash or pass init
  virtual task spi_device_flash_pass_init(device_mode_e mode);
    bit use_addr_4b_enable; // Mode of config
    spi_device_init();
    `uvm_info(`gfn, "Initialize flash/passthrough mode", UVM_MEDIUM)
    `DV_CHECK_STD_RANDOMIZE_FATAL(use_addr_4b_enable)
    // TODO, fixed config for now
    cfg.spi_host_agent_cfg.sck_polarity[0] = 0;
    cfg.spi_host_agent_cfg.sck_phase[0] = 0;
    cfg.spi_device_agent_cfg.sck_polarity[0] = 0;
    cfg.spi_device_agent_cfg.sck_phase[0] = 0;

    // bit dir is only supported in fw mode. Need to be 0 for other modes
    cfg.spi_host_agent_cfg.host_bit_dir = 0;
    cfg.spi_host_agent_cfg.device_bit_dir = 0;
    cfg.spi_device_agent_cfg.host_bit_dir = 0;
    cfg.spi_device_agent_cfg.device_bit_dir = 0;

    cfg.spi_host_agent_cfg.num_bytes_per_trans_in_mon = 1;
    cfg.spi_device_agent_cfg.num_bytes_per_trans_in_mon = 1;
    cfg.spi_host_agent_cfg.is_flash_mode = 1;
    cfg.spi_device_agent_cfg.is_flash_mode = 1;
    ral.cfg.tx_order.set(cfg.spi_host_agent_cfg.host_bit_dir);
    ral.cfg.rx_order.set(cfg.spi_host_agent_cfg.device_bit_dir);
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

    // addr/payload swap settting
    `DV_CHECK_RANDOMIZE_FATAL(ral.addr_swap_mask)
    csr_update(.csr(ral.addr_swap_mask));
    `DV_CHECK_RANDOMIZE_FATAL(ral.addr_swap_data)
    csr_update(.csr(ral.addr_swap_data));
    `DV_CHECK_RANDOMIZE_FATAL(ral.payload_swap_mask)
    csr_update(.csr(ral.payload_swap_mask));
    `DV_CHECK_RANDOMIZE_FATAL(ral.payload_swap_data)
    csr_update(.csr(ral.payload_swap_data));

    // configure intercept_en
    if (allow_intercept) begin
      // TODO, only support status intercept
      `DV_CHECK_RANDOMIZE_FATAL(ral.intercept_en.status)
      csr_update(ral.intercept_en);
    end
    config_all_cmd_infos();

    spi_device_flash_auto_rsp_nonblocking();
    randomize_mem();
    randomize_all_cmd_filters();
  endtask : spi_device_flash_pass_init

  // Task for configuring enable/disable of command opcode
  virtual task cfg_cmd_filter(bit not_enable, bit [7:0] cmd);
    bit [7:0] cmd_index;
    bit [7:0] cmd_offset;
    // Calculate filter bit position
    cmd_index = get_cmd_filter_index(cmd);
    cmd_offset = get_cmd_filter_offset(cmd);
    ral.cmd_filter[cmd_index].filter[cmd_offset].set(not_enable);
    csr_update(.csr(ral.cmd_filter[cmd_index]));
  endtask : cfg_cmd_filter

  virtual task randomize_all_cmd_filters();
    foreach (ral.cmd_filter[idx]) begin
      `DV_CHECK_RANDOMIZE_FATAL(ral.cmd_filter[idx])
      csr_update(.csr(ral.cmd_filter[idx]));
    end
  endtask : randomize_all_cmd_filters

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
    bit valid;
    bit swap;

    if (allow_set_cmd_info_invalid) valid = $urandom_range(0, 1);
    else valid = 1;

    if (valid) begin
      cfg.spi_host_agent_cfg.add_cmd_info(info);
      cfg.spi_device_agent_cfg.add_cmd_info(info);
    end

    `uvm_info(`gfn, $sformatf("Add this cmd_info \n%s", info.sprint()), UVM_MEDIUM)
    case (info.num_lanes)
      1 : lanes_en = info.write_command ? 4'h1 : 4'h2;
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
    // if addr_size is aligned with addr_4b_en, we could use AddrCfg instead of Addr4B/Addr3B
    if (`gmv(ral.cfg.addr_4b_en) == 1 && addr_size == Addr4B ||
         `gmv(ral.cfg.addr_4b_en) == 0 && addr_size == Addr3B) begin
        if ($urandom_range(0, 1)) addr_size = AddrCfg;
    end
    ral.cmd_info[idx].addr_mode.set(addr_size);

    ral.cmd_info[idx].valid.set(valid); // Enable this OPCODE
    ral.cmd_info[idx].opcode.set(info.opcode);// Read Dual
    ral.cmd_info[idx].payload_en.set(lanes_en);
    ral.cmd_info[idx].payload_dir.set(!info.write_command);

    // set dummy cycles
    if (info.dummy_cycles > 0) begin
      ral.cmd_info[idx].dummy_en.set(1);
      ral.cmd_info[idx].dummy_size.set(info.dummy_cycles - 1);
    end else begin
      ral.cmd_info[idx].dummy_en.set(0);
      `DV_CHECK_RANDOMIZE_FATAL(ral.cmd_info[idx].dummy_size)
    end

    if (allow_addr_swap) begin
      swap = $urandom_range(0, 99) < addr_payload_swap_pct;
    end else begin
      swap = 0;
    end
    ral.cmd_info[idx].addr_swap_en.set(swap);

    // only write and single mode allows payload swap
    if (allow_payload_swap && info.write_command && info.num_lanes == 1) begin
      swap = $urandom_range(0, 99) < addr_payload_swap_pct;
    end else begin
      swap = 0;
    end
    ral.cmd_info[idx].payload_swap_en.set(swap);
    csr_update(.csr(ral.cmd_info[idx]));
  endtask : add_cmd_info

  virtual function bit [7:0] get_rand_opcode();
    bit valid_op;
    bit [7:0] op;

    if (allow_use_invalid_opcode) begin
        `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(valid_op,
            valid_op dist {1 :/ 4, 0 :/ 1};)
    end else begin
      valid_op = 1;
    end
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(op,
        if (valid_op) {
          op inside {valid_opcode_q};
        } else {
          !(op inside {valid_opcode_q});
        })
    return op;
  endfunction

  function int get_rand_payload_size();
    uint size;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(size,
        size dist {
           [0:5]    :/ 2,
           128      :/ 1,
           256      :/ 2, // typical value for a flash page size
           512      :/ 1,
           [6:1000] :/ 1};)
    return size;
  endfunction

  virtual task random_write_flash_status();
    `DV_CHECK_RANDOMIZE_FATAL(ral.flash_status)
    `uvm_info(`gfn, $sformatf("program flash_status: 0x%0h", ral.flash_status.get()), UVM_MEDIUM)
    csr_update(.csr(ral.flash_status));

    cfg.clk_rst_vif.wait_clks(10);
  endtask
endclass : spi_device_pass_base_vseq
