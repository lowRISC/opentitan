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
  int addr_payload_swap_pct = 50;

  bit allow_intercept;
  bit allow_upload;

  bit allow_write_enable_disable;
  bit allow_addr_cfg_cmd;

  // mailbox knobs
  int cfg_mailbox_en_pct = 70;
  int intercept_mailbox_en_pct = 70;
  // we can only hold one payload, set it busy to avoid payload is overwritten before read out.
  // TODO, set this for all vseq, since uploading another payload with clearing busy bit isn't a
  // correct use case.
  bit always_set_busy_when_upload_contain_payload = 1;

  // knob to control read_buffer_update thread
  bit stop_forever_read_buffer_update;
  bit read_buffer_update_ongoing;
  int read_last_read_addr_pct = 20;

  rand device_mode_e device_mode;

  // overide this to enable other modes
  constraint device_mode_c {
    device_mode == PassthroughMode;
  }

  bit [7:0] valid_opcode_q[$];
  rand bit valid_op;
  rand bit [7:0] opcode;
  constraint opcode_c {
    solve valid_op before opcode;
    if (allow_use_invalid_opcode) {
      valid_op dist {1 :/ 4, 0 :/ 1};
    } else {
      valid_op == 1;
    }

    if (valid_op && valid_opcode_q.size > 0) {
      opcode inside {valid_opcode_q};
    } else {
      !(opcode inside {valid_opcode_q});
    }
  }
  // the start addr and payload size matter to the read command
  // for program or other cmd, addr and payload size don't matter,
  // but we could still use this constraint for them
  bit [31:0] mbx_start_addr;
  bit [31:0] mbx_end_addr;
  rand bit [31:0] read_start_addr;
  rand bit [31:0] read_end_addr;
  rand uint payload_size;
  rand read_addr_size_type_e read_addr_size_type;
  bit mailbox_en;

  int large_payload_weight = 2;
  constraint payload_size_c {
    payload_size dist {
        [0:5]    :/ 2,
        128      :/ 1,
        256      :/ 2, // typical value for a flash page size
        512      :/ 1,
        [6:3000] :/ large_payload_weight};
  }

  constraint read_addr_size_type_c {
    solve read_start_addr, payload_size before read_end_addr;
    read_start_addr + payload_size == read_end_addr;

    if (read_addr_size_type == ReadAddrWithinMailbox) {
      read_start_addr inside {[mbx_start_addr:mbx_end_addr]} &&
      read_end_addr inside {[mbx_start_addr:mbx_end_addr]};
    } else if (read_addr_size_type == ReadAddrCrossIntoMailbox) {
      read_start_addr inside {[mbx_start_addr:mbx_end_addr]} && read_end_addr > mbx_end_addr;
    } else if (read_addr_size_type == ReadAddrCrossOutOfMailbox) {
      read_start_addr < mbx_start_addr && read_end_addr inside {[mbx_start_addr:mbx_end_addr]};
    } else if (read_addr_size_type == ReadAddrCrossAllMailbox) {
      read_start_addr < mbx_start_addr && read_end_addr > mbx_end_addr;
    } else { // ReadAddrOutsideMailbox
      // both start and end addr are less than mbx_start_addr
      (read_start_addr < mbx_start_addr &&
       (read_start_addr + payload_size) < mbx_start_addr) ||
      // read end addr is bigger than mbx_end_addr. And not cross all 1s boundary, or
      // read end addr is less than mbx_start_addr if crossing boundary
      (read_start_addr > mbx_end_addr &&
       (read_start_addr + payload_size <= {32{1'b1}} || read_end_addr < mbx_start_addr));
    }

    // make this distribute evenly
    read_addr_size_type dist {
        ReadAddrWithinMailbox     :/ 1,
        ReadAddrCrossIntoMailbox  :/ 1,
        ReadAddrCrossOutOfMailbox :/ 1,
        ReadAddrCrossAllMailbox   :/ 1,
        ReadAddrOutsideMailbox    :/ 1};
  }

  constraint addr_size_and_device_mode_c {
    solve device_mode before read_addr_size_type;
    if (device_mode == FlashMode) {
      // flash mode doesn't support mailbox boundary crossing.
      read_addr_size_type inside {ReadAddrWithinMailbox, ReadAddrOutsideMailbox};
      // this is read buffer
      if ((!mailbox_en || read_addr_size_type == ReadAddrOutsideMailbox) &&
          opcode inside {READ_CMD_LIST}) {
        read_start_addr == cfg.next_read_buffer_addr;
      }
    }
  }

  rand bit [9:0] read_threshold_val;
  constraint read_threshold_val_c {
    read_threshold_val dist {
        0         :/ 1,
        [1:4]     :/ 1,
        [5:'h3fe] :/ 3,
        'h3ff     :/ 1};
  }
  `uvm_object_utils(spi_device_pass_base_vseq)
  `uvm_object_new

  task pre_start();
    super.pre_start();
    spi_device_flash_auto_rsp_nonblocking();
  endtask

  function void randomize_op_addr_size();
    mbx_start_addr = cfg.get_mbx_base_addr();
    mbx_end_addr   = mbx_start_addr + MAILBOX_BUFFER_SIZE;
    mailbox_en = `gmv(ral.cfg.mailbox_en);
    `DV_CHECK_FATAL(this.randomize(opcode, valid_op,
      read_start_addr, read_end_addr, payload_size, read_addr_size_type))
  endfunction

  // Task for adding cmd info
  virtual task config_all_cmd_infos();
    spi_flash_cmd_info info = spi_flash_cmd_info::type_id::create("info");

    // clean up previous configure cmd_infos
    cfg.spi_host_agent_cfg.cmd_infos.delete();
    cfg.spi_device_agent_cfg.cmd_infos.delete();

    // Configure the first 11 commands which are fixed
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_mode == SpiFlashAddrDisabled &&
      info.opcode == READ_STATUS_1 &&
      info.num_lanes == 1 &&
      info.dummy_cycles == 0 &&
      info.write_command == 0;)
    // don't allow invalid the read_status if upload is used.
    // Otherwise, upstream SPI can't read the busy bit
    if (allow_upload) add_cmd_info(.info(info), .idx(0), .allow_invalid(0));
    else              add_cmd_info(.info(info), .idx(0)); // use default value for allow_invalid

    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_mode == SpiFlashAddrDisabled &&
      info.opcode == READ_STATUS_2;
      info.num_lanes == 1 &&
      info.dummy_cycles == 0 &&
      info.write_command == 0;)
    add_cmd_info(info, 1);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_mode == SpiFlashAddrDisabled &&
      info.opcode == READ_STATUS_3 &&
      info.num_lanes == 1 &&
      info.dummy_cycles == 0 &&
      info.write_command == 0;)
    add_cmd_info(info, 2);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_mode == SpiFlashAddrDisabled &&
      info.opcode == READ_JEDEC &&
      info.num_lanes == 1 &&
      info.dummy_cycles == 0 &&
      info.write_command == 0;)
    add_cmd_info(info, 3);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_mode == SpiFlashAddr3b &&
      info.opcode == READ_SFDP;
      info.num_lanes == 1 &&
      info.write_command == 0;)
    add_cmd_info(info, 4);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_mode != SpiFlashAddrDisabled &&
      info.opcode == READ_NORMAL &&
      info.num_lanes == 1 &&
      info.write_command == 0;)
    add_cmd_info(info, 5);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_mode != SpiFlashAddrDisabled &&
      info.opcode == READ_FAST &&
      info.num_lanes == 1 &&
      info.write_command == 0;)
    add_cmd_info(info, 6);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_mode != SpiFlashAddrDisabled &&
      info.opcode == READ_DUAL &&
      info.write_command == 0 &&
      info.num_lanes == 2;)
    add_cmd_info(info, 7);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_mode != SpiFlashAddrDisabled &&
      info.opcode == READ_QUAD &&
      info.write_command == 0 &&
      info.num_lanes == 4;)
    add_cmd_info(info, 8);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_mode != SpiFlashAddrDisabled &&
      info.opcode == READ_DUALIO &&
      info.write_command == 0 &&
      info.num_lanes == 2;)
    add_cmd_info(info, 9);
    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      info.addr_mode != SpiFlashAddrDisabled &&
      info.opcode == READ_QUADIO &&
      info.write_command == 0 &&
      info.num_lanes == 4;)
    add_cmd_info(info, 10);


    if (allow_write_enable_disable) begin
      bit valid;
      randomize_cfg_cmd_info(info, WREN, valid);
      ral.cmd_info_wren.valid.set(valid);
      if (valid) ral.cmd_info_wren.opcode.set(info.opcode);
      else       `DV_CHECK_RANDOMIZE_FATAL(ral.cmd_info_wren.opcode)
      csr_update(ral.cmd_info_wren);

      randomize_cfg_cmd_info(info, WRDI, valid);
      ral.cmd_info_wrdi.valid.set(valid);
      if (valid) ral.cmd_info_wrdi.opcode.set(info.opcode);
      else       `DV_CHECK_RANDOMIZE_FATAL(ral.cmd_info_wrdi.opcode)
      csr_update(ral.cmd_info_wrdi);
    end

    if (allow_addr_cfg_cmd) begin
      bit valid;
      randomize_cfg_cmd_info(info, EN4B, valid);
      ral.cmd_info_en4b.valid.set(valid);
      if (valid) ral.cmd_info_en4b.opcode.set(info.opcode);
      else       `DV_CHECK_RANDOMIZE_FATAL(ral.cmd_info_en4b.opcode)
      csr_update(ral.cmd_info_en4b);

      randomize_cfg_cmd_info(info, EX4B, valid);
      ral.cmd_info_ex4b.valid.set(valid);
      if (valid) ral.cmd_info_ex4b.opcode.set(info.opcode);
      else       `DV_CHECK_RANDOMIZE_FATAL(ral.cmd_info_ex4b.opcode)
      csr_update(ral.cmd_info_ex4b);
    end

    for (int i = 11; i < 24; i++) begin
      info = spi_flash_cmd_info::type_id::create("info");
      `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
        foreach (cfg.spi_host_agent_cfg.cmd_infos[j]) {info.opcode != j;})
      add_cmd_info(info, i);
    end

    valid_opcode_q = cfg.spi_host_agent_cfg.cmd_infos.find_index() with ('1);
  endtask : config_all_cmd_infos

  // Task for configuring 4 special cmd info slot - wren, wrdi, en4b, ex4b.
  // use ref as info is re-created in the function
  virtual function void randomize_cfg_cmd_info(ref spi_flash_cmd_info info,
                                               input bit [7:0] opcode,
                                               output bit valid);
    if (allow_set_cmd_info_invalid) valid = $urandom_range(0, 1);
    else valid = 1;

    if (!valid) return;

    info = spi_flash_cmd_info::type_id::create("info");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(info,
      opcode == local::opcode;
      // no addr, no payload
      addr_mode == SpiFlashAddrDisabled;
      num_lanes == 0;
      write_command == 0;
    )

    cfg.spi_host_agent_cfg.add_cmd_info(info);
    cfg.spi_device_agent_cfg.add_cmd_info(info);
    `uvm_info(`gfn, $sformatf("Add this cfg cmd_info \n%s", info.sprint()), UVM_MEDIUM)
  endfunction

  // Task for flash or pass init
  virtual task spi_device_flash_pass_init();
    bit enable;
    bit [1:0] sck_polarity_phase;

    spi_clk_init();
    `uvm_info(`gfn, "Initialize flash/passthrough mode", UVM_MEDIUM)

    // avoid updating these CSRs at the same time as tpm_init
    cfg.spi_cfg_sema.get();

    if (`gmv(ral.tpm_cfg.en)) begin
      sck_polarity_phase = 0;
    end else begin
      // flash mode only supports these 2 values.
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(sck_polarity_phase,
          // TODO (#16339), add back 'b11 once this issue is fixed
          sck_polarity_phase inside {0};)
    end
    cfg.spi_host_agent_cfg.sck_polarity[0] = sck_polarity_phase[0];
    cfg.spi_host_agent_cfg.sck_phase[0] = sck_polarity_phase[1];
    cfg.spi_device_agent_cfg.sck_polarity[0] = sck_polarity_phase[0];
    cfg.spi_device_agent_cfg.sck_phase[0] = sck_polarity_phase[1];

    ral.cfg.cpol.set(sck_polarity_phase[0]);
    ral.cfg.cpha.set(sck_polarity_phase[1]);

    // bit dir is only supported in fw mode. Need to be 0 for other modes
    cfg.spi_host_agent_cfg.host_bit_dir = 0;
    cfg.spi_host_agent_cfg.device_bit_dir = 0;
    cfg.spi_device_agent_cfg.host_bit_dir = 0;
    cfg.spi_device_agent_cfg.device_bit_dir = 0;

    ral.cfg.tx_order.set(cfg.spi_host_agent_cfg.host_bit_dir);
    ral.cfg.rx_order.set(cfg.spi_host_agent_cfg.device_bit_dir);

    if (cfg.do_addr_4b_cfg) begin
      `DV_CHECK_RANDOMIZE_FATAL(ral.cfg.addr_4b_en)
      cfg.spi_host_agent_cfg.flash_addr_4b_en = ral.cfg.addr_4b_en.get();
      cfg.spi_device_agent_cfg.flash_addr_4b_en = ral.cfg.addr_4b_en.get();
      cfg.do_addr_4b_cfg = 0;
    end

    `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.mailbox_addr.addr,
        // the 4th byte needs to be 0 if the cmd only contains 3 bytes address
        // constrain this byte 50% to be 0.
        value[31:24] dist {0 :/ 1, [1:$] :/ 1};

        // configure mailbox base address to very big so avoid read buffer overlaps with mailbox
        // which isn't allowed in flash mode.
        // 4th byte address may be off. In order to simplify the addr/size constraint for flash mode
        // as they needs to either in mailbox region or start from the last read buffer address.
        device_mode == FlashMode -> value[31:24] == 0 && value[23:22] > 1;
        )
    csr_update(ral.mailbox_addr);
    enable = $urandom_range(0, 99) < cfg_mailbox_en_pct;
    ral.cfg.mailbox_en.set(enable);

    csr_update(.csr(ral.cfg));
    cfg.spi_cfg_sema.put();

    // Set the passthrough or flash mode mode
    `DV_CHECK(device_mode inside {FlashMode, PassthroughMode});
    ral.control.mode.set(device_mode);
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
      `DV_CHECK_RANDOMIZE_FATAL(ral.intercept_en.jedec)
      `DV_CHECK_RANDOMIZE_FATAL(ral.intercept_en.sfdp)
      enable = $urandom_range(0, 99) < intercept_mailbox_en_pct;
      ral.intercept_en.mbx.set(enable);
      csr_update(ral.intercept_en);
    end

    // if upload is enabled, need to enable status intercept, so that host side
    // can know if spi_device is busy or not
    if (allow_upload && (`gmv(ral.intercept_en.status) == 0)) begin
      ral.intercept_en.status.set(1);
      csr_update(ral.intercept_en);
    end

    // randomize jedec
    `DV_CHECK_RANDOMIZE_FATAL(ral.jedec_cc.cc)
    `DV_CHECK_RANDOMIZE_WITH_FATAL(ral.jedec_cc.num_cc,
                                   value dist {0 :/ 2, [1:254] :/ 2, 255 :/ 1};)
    csr_update(.csr(ral.jedec_cc));
    `DV_CHECK_RANDOMIZE_FATAL(ral.jedec_id)
    csr_update(.csr(ral.jedec_id));

    // disable watermark event
    ral.read_threshold.set(read_threshold_val);
    csr_update(ral.read_threshold);

    config_all_cmd_infos();

    random_write_spi_mem(.start_addr(0), .end_addr(SRAM_SIZE - 1));
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

  // Task for configuring cmd info slot
  virtual task add_cmd_info(spi_flash_cmd_info info, bit [4:0] idx,
                            bit allow_invalid = allow_set_cmd_info_invalid);
    bit [3:0] lanes_en;
    bit valid;
    bit swap;

    if (allow_invalid) valid = $urandom_range(0, 1);
    else valid = 1;

    if (valid) begin
      cfg.spi_host_agent_cfg.add_cmd_info(info);
      cfg.spi_device_agent_cfg.add_cmd_info(info);
    end

    `uvm_info(`gfn, $sformatf("Add this cmd_info \n%s", info.sprint()), UVM_MEDIUM)
    case (info.num_lanes)
      0: lanes_en = 0;
      1: lanes_en = info.write_command ? 4'h1 : 4'h2;
      2: lanes_en = 4'h3;
      4: lanes_en = 4'hF;
      default : `uvm_fatal(`gfn, $sformatf("Unsupported lanes num 0x%0h", info.num_lanes))
    endcase

    ral.cmd_info[idx].addr_mode.set(info.addr_mode);
    ral.cmd_info[idx].valid.set(valid); // Enable this OPCODE
    ral.cmd_info[idx].opcode.set(info.opcode);
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
      if (swap) `uvm_info(`gfn, $sformatf("addr_swap is set for opcode 0x%0x", info.opcode),
                          UVM_MEDIUM)
    end else begin
      swap = 0;
    end
    ral.cmd_info[idx].addr_swap_en.set(swap);

    // only write and single mode allows payload swap
    if (allow_payload_swap && info.write_command && info.num_lanes == 1) begin
      swap = $urandom_range(0, 99) < addr_payload_swap_pct;
      if (swap) `uvm_info(`gfn, $sformatf("payload_swap is set for opcode 0x%0x", info.opcode),
                          UVM_MEDIUM)
    end else begin
      swap = 0;
    end
    ral.cmd_info[idx].payload_swap_en.set(swap);

    // configure upload
    // first 11 cmd doesn't support upload
    if (idx >= NUM_INTERNAL_PROCESSED_CMD && allow_upload) begin
      // upload only applies to program or no data
      if (ral.cmd_info[idx].payload_en.get() == 0 ||
          ral.cmd_info[idx].payload_dir.get() == PayloadIn) begin
        `DV_CHECK_RANDOMIZE_FATAL(ral.cmd_info[idx].upload)
      end else begin
        ral.cmd_info[idx].upload.set(0);
      end
    end

    // set busy enabled, when this flas is set and cmd is updated with payload
    if (always_set_busy_when_upload_contain_payload && ral.cmd_info[idx].upload.get()
       && (ral.cmd_info[idx].payload_en.get() == 0 ||
           ral.cmd_info[idx].payload_dir.get() == PayloadIn)) begin
      ral.cmd_info[idx].busy.set(1);
    end else begin
      `DV_CHECK_RANDOMIZE_FATAL(ral.cmd_info[idx].busy)
    end
    csr_update(.csr(ral.cmd_info[idx]));
  endtask : add_cmd_info

  // transfer in command including opcode, address and payload
  // if byte_addr_q is empty, the host_seq will use a random addr
  virtual task spi_host_xfer_flash_item(bit [7:0] op, uint payload_size,
                                        bit [31:0] addr, bit wait_on_busy = 1);
    spi_host_flash_seq m_spi_host_seq;
    bit [7:0] byte_addr_q[$];
    `uvm_create_on(m_spi_host_seq, p_sequencer.spi_sequencer_h)

    if (op inside {READ_CMD_LIST} && cfg.spi_host_agent_cfg.is_opcode_supported(op)) begin
      int num_addr_bytes = cfg.spi_host_agent_cfg.get_num_addr_byte(op);
      if (num_addr_bytes > 0) begin
        if (num_addr_bytes == 4) begin
          byte_addr_q.push_back(addr[31:24]);
        end
        // push the lower 3 bytes address
        byte_addr_q = {byte_addr_q, addr[23:16], addr[15:8], addr[7:0]};
      end
    end

    `DV_CHECK_RANDOMIZE_WITH_FATAL(m_spi_host_seq,
                                   opcode == op;
                                   address_q.size() == byte_addr_q.size();
                                   foreach (byte_addr_q[i]) address_q[i] == byte_addr_q[i];
                                   payload_q.size() == payload_size;
                                   read_size == payload_size;)
    `uvm_send(m_spi_host_seq)

    if (op == `gmv(ral.cmd_info_en4b.opcode) && `gmv(ral.cmd_info_en4b.valid)) begin
      cfg.spi_device_agent_cfg.flash_addr_4b_en = 1;
      cfg.spi_host_agent_cfg.flash_addr_4b_en   = 1;
    end else if (op == `gmv(ral.cmd_info_ex4b.opcode) && `gmv(ral.cmd_info_ex4b.valid)) begin
      cfg.spi_device_agent_cfg.flash_addr_4b_en = 0;
      cfg.spi_host_agent_cfg.flash_addr_4b_en   = 0;
    end

    if (cfg.is_read_buffer_cmd(m_spi_host_seq.rsp)) begin
      cfg.next_read_buffer_addr = convert_addr_from_byte_queue(m_spi_host_seq.rsp.address_q) +
                             m_spi_host_seq.rsp.payload_q.size();

      `uvm_info(`gfn, $sformatf("Updated next_read_buffer_addr: 0x%0x", cfg.next_read_buffer_addr),
                UVM_MEDIUM)
    end

    if ($urandom_range(0, 99) < allow_dummy_trans_pct) begin
      spi_host_xfer_dummy_item();
    end
    // randomly read last_read_addr for scb to check
    if ($urandom_range(0, 99) < read_last_read_addr_pct) begin
      bit [TL_DW-1:0] rdata;

      // This is synced from the other clock domain. It takes around 3-4 cycles.
      cfg.clk_rst_vif.wait_clks(5);
      csr_rd(.ptr(ral.last_read_addr), .value(rdata));
    end

    if (wait_on_busy) begin
      spi_device_reg_cmd_info cmd_info = cfg.get_cmd_info_reg_by_opcode(op);
      if (cmd_info != null && `gmv(cmd_info.upload) && `gmv(cmd_info.busy)) begin
        spi_host_wait_on_busy();
      end
    end
  endtask

  virtual task random_access_flash_status(bit write = $urandom_range(0, 1),
                                          bit busy  = $urandom_range(0, 1),
                                          bit wel   = $urandom_range(0, 1),
                                          bit [21:0] other_status = $urandom());
    if (write) begin
      bit [23:0] status_val = {other_status, wel, busy};
      csr_wr(.ptr(ral.flash_status), .value(status_val));
      `uvm_info(`gfn, $sformatf("program flash_status: 0x%0h", ral.flash_status.get()), UVM_MEDIUM)

      cfg.clk_rst_vif.wait_clks(10);
    end else begin
      bit[TL_DW-1:0] val;
      csr_rd(ral.flash_status, val);
    end
  endtask

  virtual task get_flash_status_busy(output bit busy);
    uvm_reg_data_t rdata;
    csr_rd(ral.flash_status, rdata);
    busy = get_field_val(ral.flash_status.busy, rdata);
    `uvm_info(`gfn, $sformatf("read complete, flash_status: %x", rdata), UVM_HIGH)
  endtask

  virtual task clear_flash_busy_bit();
    bit busy;
    uint wait_txn_count = 1;
    `uvm_info(`gfn, "Clearing flash busy bit", UVM_MEDIUM)
    // Check if there is any ongoing SPI transaction
    if (!cfg.spi_host_agent_cfg.vif.csb[FW_FLASH_CSB_ID]) begin
      wait_txn_count++;
    end
    // clear busy bit
    ral.flash_status.busy.set(0);
    csr_update(ral.flash_status);
    // The intent here is to check the flash_status after csr_wr and then read the register
    // after end of SPI transaction (since flash_status gets update after CSB is deasserted)
    // Wait for end of SPI transaction
    repeat (wait_txn_count) begin
      @(posedge cfg.spi_host_agent_cfg.vif.csb[FW_FLASH_CSB_ID]);
      `uvm_info(`gfn, "Detected end of SPI transaction", UVM_HIGH)
    end
    // Wait for 5 cycles after deassertion of CSB to allow for flash_status to get updated
    cfg.clk_rst_vif.wait_clks(5);
    get_flash_status_busy(busy);
    // If busy bit is not cleared, check once more else raise an error
    if (busy) begin
      get_flash_status_busy(busy);
      `DV_CHECK_EQ(busy, 0, "flash_status.busy == 1 expected to be 0")
    end
    `uvm_info(`gfn, "Cleared flash busy bit", UVM_MEDIUM)
  endtask

  // check if 3 upload fifo (cmd, addr, payload) are empty. If so, read all of them
  // if busy is set, clear it
  virtual task read_upload_fifos();
    bit [TL_DW-1:0] intr_state_val, status_val, status2_val;
    int cmdfifo_depth_val, addrfifo_depth_val, payload_depth_val;
    int payload_base_offset;
    bit busy_val;
    bit intr_cmdfifo, intr_payload, intr_overflow;

    csr_rd(ral.intr_state, intr_state_val);
    intr_cmdfifo = get_field_val(ral.intr_state.upload_cmdfifo_not_empty, intr_state_val);
    intr_payload = get_field_val(ral.intr_state.upload_payload_not_empty, intr_state_val);
    intr_overflow = get_field_val(ral.intr_state.upload_payload_overflow, intr_state_val);
    if (intr_cmdfifo == 0 && intr_payload == 0) return;

    // read these status after interrupts occur, so that scb doesn't need to model it
    // cycle accurately
    csr_rd(ral.upload_status, status_val);
    csr_rd(ral.upload_status2, status2_val);
    cmdfifo_depth_val = get_field_val(ral.upload_status.cmdfifo_depth, status_val);
    addrfifo_depth_val = get_field_val(ral.upload_status.addrfifo_depth, status_val);
    payload_depth_val = get_field_val(ral.upload_status2.payload_depth, status2_val);


    // clear interrupt before reading out data, so that if new event comes, won't be missed.
    intr_state_val = 0;
    if (intr_cmdfifo) intr_state_val[CmdFifoNotEmpty] = 1;
    if (intr_payload) intr_state_val[PayloadNotEmpty] = 1;
    if (intr_overflow) intr_state_val[PayloadOverflow] = 1;
    // Wait for register access to complete
    while(ral.intr_state.is_busy()) begin
      cfg.clk_rst_vif.wait_clks(1);
    end
    csr_wr(ral.intr_state, intr_state_val);

    if (intr_cmdfifo) `DV_CHECK_GT(cmdfifo_depth_val, 0)
    for (int i = 0; i < cmdfifo_depth_val; i++) begin
      bit [TL_DW-1:0] val;
      csr_rd(ral.upload_cmdfifo, val);
      `uvm_info(`gfn, $sformatf("read upload_cmdfifo: idx: %0d, data: 0x%0x", i, val), UVM_MEDIUM)
    end

    for (int i = 0; i < addrfifo_depth_val; i++) begin
      bit [TL_DW-1:0] val;
      csr_rd(ral.upload_addrfifo, val);
      `uvm_info(`gfn, $sformatf("read upload_addrfifo: idx: %0d, data: 0x%0x", i, val), UVM_MEDIUM)
    end

    if (intr_payload) `DV_CHECK_GT(payload_depth_val, 0)
    if (payload_depth_val > PAYLOAD_FIFO_SIZE) payload_depth_val = PAYLOAD_FIFO_SIZE;

    // need to shift by 2 for the offset used at mem_rd
    payload_base_offset = (READ_BUFFER_SIZE + MAILBOX_BUFFER_SIZE + SFDP_SIZE) / 4;
    payload_depth_val = payload_depth_val / 4;
    for (int i = 0; i < payload_depth_val; i++) begin
      bit [TL_DW-1:0] val;
      int offset = i + payload_base_offset;
      mem_rd(.ptr(ral.buffer), .offset(offset), .data(val));
      `uvm_info(`gfn, $sformatf("read upload_payloadfifo: idx: %0d, data: 0x%0x", i, val),
                UVM_MEDIUM)
    end

    // clear busy bit
    csr_rd(ral.flash_status.busy, busy_val);
    if (busy_val == 1) clear_flash_busy_bit();
  endtask : read_upload_fifos

  virtual task upload_fifo_read_seq();
    int upload_read_dly;
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(upload_read_dly,
        upload_read_dly dist {
            [0:10]      :/ 1,
            [11:100]    :/ 2,
            [101:1000]  :/ 2,
            [1000:5000] :/ 1};)
    cfg.clk_rst_vif.wait_clks(upload_read_dly);
    read_upload_fifos();
  endtask : upload_fifo_read_seq

  task post_start();
    super.post_start();
    // read flash_status for check
    random_access_flash_status(.write(0));

    // stop the read buffer thread and allow it to complete gracefully
    if (read_buffer_update_ongoing) begin
      stop_forever_read_buffer_update = 1;
      `DV_WAIT(!read_buffer_update_ongoing)
    end
  endtask

  virtual task read_and_check_4b_en();
    cfg.clk_rst_vif.wait_clks(10);
    // avoid accessing this CSR at the same time as tpm_init
    cfg.spi_cfg_sema.get();
    csr_rd_check(.ptr(ral.cfg.addr_4b_en),
                 .compare_value(cfg.spi_device_agent_cfg.flash_addr_4b_en));
    cfg.spi_cfg_sema.put();
  endtask

  virtual task random_write_spi_mem(int start_addr, int end_addr, string msg_region = "mem",
                                    bit zero_delay_write = $urandom_range(0, 1));
    if (zero_delay_write) begin
      cfg.m_tl_agent_cfg.a_valid_delay_max = 0;
      cfg.m_tl_agent_cfg.d_ready_delay_max = 0;
    end
    for (int i = start_addr / 4; i <= end_addr / 4; i++) begin
      bit [TL_DW-1:0] data = $urandom();
      mem_wr(.ptr(ral.buffer), .offset(i), .data(data), .blocking(!zero_delay_write));
      `uvm_info(`gfn, $sformatf("write %s offset 0x%0x: 0x%0x", msg_region, i << 2, data),
                UVM_MEDIUM)
    end
    wait_no_outstanding_access();
    if (zero_delay_write) begin
      cfg.m_tl_agent_cfg.a_valid_delay_max = 10;
      cfg.m_tl_agent_cfg.d_ready_delay_max = 10;
    end
  endtask : random_write_spi_mem

  // read buffer can be divided into 2 half by flip events
  // |____________half0___________|____________half1___________|
  // |                          flip                         flip
  // once SW receives an interrupt, update the previous 1k region, so that it won't affect ongoing
  // SPI read
  virtual task forever_read_buffer_update_nonblocking();
    bit [TL_AW-1:0] start_addr;
    bit [TL_AW-1:0] end_addr;
    fork
      begin
        read_buffer_update_ongoing = 1;
        while (!stop_forever_read_buffer_update) begin
          bit [TL_DW-1:0] intr_state_val;
          bit is_flip;
          bit is_watermark;
          // use zero_delay write, otherwise, spi may read faster than SW write
          bit zero_delay_write = 1;

          cfg.clk_rst_vif.wait_clks($urandom_range(10, 200));

          csr_rd(ral.intr_state, intr_state_val);
          is_flip = get_field_val(ral.intr_state.readbuf_flip, intr_state_val);
          is_watermark = get_field_val(ral.intr_state.readbuf_watermark, intr_state_val);

          // clear flip and watermark event before updating mem
          // if clear too late, scb is hard to handle as the interrupt may happen again
          intr_state_val = 0;
          if (is_flip)      intr_state_val[ReadbufFlip] = 1;
          if (is_watermark) intr_state_val[ReadbufWatermark] = 1;

          if (!is_flip && !is_watermark) continue;
          // Wait for register access to complete
          while(ral.intr_state.is_busy()) begin
            cfg.clk_rst_vif.wait_clks(1);
          end
          csr_wr(ral.intr_state, intr_state_val);

          if (is_flip) begin
            start_addr = cfg.read_buffer_ptr % READ_BUFFER_SIZE;
            end_addr = (start_addr + READ_BUFFER_HALF_SIZE);

            `uvm_info(`gfn, $sformatf("Updating mem from 0x%0x:0x%0x due to flip event",
                            start_addr, end_addr - 1), UVM_MEDIUM)
            random_write_spi_mem(start_addr, end_addr - 1, "read buffer", zero_delay_write);
            cfg.read_buffer_ptr = end_addr;
          end
        end
        read_buffer_update_ongoing = 0;
      end
    join_none
  endtask : forever_read_buffer_update_nonblocking
endclass : spi_device_pass_base_vseq
