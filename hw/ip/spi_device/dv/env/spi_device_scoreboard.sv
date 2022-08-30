// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_device_scoreboard extends cip_base_scoreboard #(.CFG_T (spi_device_env_cfg),
                                                          .RAL_T (spi_device_reg_block),
                                                          .COV_T (spi_device_env_cov));
  `uvm_component_utils(spi_device_scoreboard)

  localparam int FLASH_STATUS_UPDATE_DLY_AFTER_CSB_DEASSERT = 3;
  typedef enum int {
    NoInternalProcess,
    InternalProcessStatus,
    InternalProcessJedec,
    InternalProcessSfdp,
    InternalProcessReadCmd,
    // cmd like write enable/disable, enter/exit 4B addr
    InternalProcessCfgCmd,
    UploadCmd
  } internal_process_cmd_e;

  // TLM fifos to pick up the packets
  uvm_tlm_analysis_fifo #(spi_item) upstream_spi_host_fifo;
  uvm_tlm_analysis_fifo #(spi_item) upstream_spi_device_fifo;
  // connect with req_analysis_port where it receives item when opcode and address are received
  uvm_tlm_analysis_fifo #(spi_item) upstream_spi_req_fifo;
  uvm_tlm_analysis_fifo #(spi_item) downstream_spi_host_fifo;

  // mem model to save expected value
  local mem_model tx_mem;
  local mem_model rx_mem;
  local uint tx_rptr_exp;
  local uint rx_wptr_exp;
  local mem_model spi_mem;

  // when interrupt is triggered, it may take a few cycles before it's reflected in a TL read
  local bit [NumSpiDevIntr-1:0] intr_trigger_pending;

  // tx/rx async fifo, size is 2 words
  local bit [31:0] tx_word_q[$];
  local bit [31:0] rx_word_q[$];

  // for passthrough
  spi_item spi_passthrough_downstream_q[$];

  // for upload
  bit [7:0] upload_cmd_q[$];
  bit [31:0] upload_addr_q[$];

  // for read buffer
  // once triggered, it won't be triggered again until it flips
  bit read_buffer_watermark_triggered;

  flash_status_t flash_status_q[$];
  flash_status_t flash_status_settle_q[$];
  // this queue contains the previous value of flash_status
  // it's ok the readback value matches to either this one or the mirror value
  // after a flash_status access, delete this queue as the uncertain window is only a few cycles
  flash_status_t flash_status_tl_pre_val_q[$];

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    upstream_spi_host_fifo = new("upstream_spi_host_fifo", this);
    upstream_spi_device_fifo = new("upstream_spi_device_fifo", this);
    upstream_spi_req_fifo = new("upstream_spi_req_fifo", this);
    downstream_spi_host_fifo = new("downstream_spi_host_fifo", this);
    tx_mem = mem_model#()::type_id::create("tx_mem", this);
    rx_mem = mem_model#()::type_id::create("rx_mem", this);

    `DV_CHECK_FATAL(exp_mem.exists(RAL_T::type_name))
    spi_mem = exp_mem[RAL_T::type_name];
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_upstream_spi_host_fifo();
      process_upstream_spi_device_fifo();
      process_downstream_spi_fifo();
      process_read_buffer_cmd();
      forever_latch_flash_status();
    join_none
  endtask

  // extract spi items sent from host
  virtual task process_upstream_spi_host_fifo();
    spi_item item;
    forever begin
      bit is_status, is_jedec, is_sfdp, is_mbx_read;
      bit update_wel, wel_val;
      upstream_spi_host_fifo.get(item);
      `uvm_info(`gfn, $sformatf("upstream received host spi item:\n%0s", item.sprint()),
                UVM_MEDIUM)
      case (`gmv(ral.control.mode))
        GenericMode: begin
          `DV_CHECK_EQ(item.item_type, SpiTransNormal)
          receive_spi_rx_data({item.data[3], item.data[2], item.data[1], item.data[0]});
        end
        FlashMode, PassthroughMode: begin
          internal_process_cmd_e cmd_type;
          bit is_intercepted;
          bit set_busy;
          `DV_CHECK_EQ(item.item_type, SpiFlashTrans)

          // read buffer is handled at `process_read_buffer_cmd`
          if (!cfg.is_read_buffer_cmd(item)) begin
            // downstream item should be in the queue at the same time, add small delay
            #1ps;
            cmd_type = triage_flash_cmd(item.opcode, set_busy);
            `uvm_info(`gfn, $sformatf("Triage flash cmd: %s, set_busy: %0d", cmd_type, set_busy),
                      UVM_MEDIUM)

            is_intercepted = 1;
            case (cmd_type)
              NoInternalProcess: begin
                is_intercepted = 0;
              end
              InternalProcessStatus: begin
                check_internal_processed_read_status(item);
              end
              InternalProcessJedec: begin
                check_internal_processed_read_jedec(item);
              end
              InternalProcessSfdp: begin
                check_internal_processed_read_sfdp(item);
              end
              InternalProcessReadCmd: begin
                spi_item downstream_item;
                if (is_opcode_passthrough(item.opcode)) begin
                  `DV_CHECK_EQ_FATAL(spi_passthrough_downstream_q.size, 1)
                  downstream_item = spi_passthrough_downstream_q[0];
                end
                check_read_cmd_data_for_non_read_buffer(item, downstream_item);
              end
              InternalProcessCfgCmd: begin
                if (`GET_OPCODE_VALID_AND_MATCH(cmd_info_en4b, item.opcode)) begin
                  void'(ral.cfg.addr_4b_en.predict(.value(1), .kind(UVM_PREDICT_WRITE)));
                  `uvm_info(`gfn, "Enable 4b addr due to cmd EN4B", UVM_MEDIUM)
                end else if (`GET_OPCODE_VALID_AND_MATCH(cmd_info_ex4b, item.opcode)) begin
                  void'(ral.cfg.addr_4b_en.predict(.value(0), .kind(UVM_PREDICT_WRITE)));
                  `uvm_info(`gfn, "Disable 4b addr due to cmd EX4B", UVM_MEDIUM)
                end else if (`GET_OPCODE_VALID_AND_MATCH(cmd_info_wren, item.opcode)) begin
                  update_wel = 1;
                  wel_val = 1;
                end else if (`GET_OPCODE_VALID_AND_MATCH(cmd_info_wrdi, item.opcode)) begin
                  update_wel = 1;
                  wel_val = 0;
                end else begin
                  `uvm_fatal(`gfn, $sformatf("shouldn't enter here, opcode 0x%0x", item.opcode))
                end
              end
              UploadCmd: begin
                process_upload_cmd(item);
              end
              default: `uvm_fatal(`gfn, "can't get here")
            endcase

            // if busy, passthrough is blocked
            if (is_opcode_passthrough(item.opcode) && !`gmv(ral.flash_status.busy)) begin
              compare_passthru_item(.upstream_item(item), .is_intercepted(is_intercepted));
            end
          end // if (!cfg.is_read_buffer_cmd(item))

          latch_flash_status(set_busy, update_wel, wel_val);
        end
        default: `uvm_fatal(`gfn, $sformatf("Unexpected mode: %0d", `gmv(ral.control.mode)))
      endcase // case (`gmv(ral.control.mode))
    end // forever
  endtask

  // update flash_status to the value of the last item
  virtual function void latch_flash_status(bit set_busy, bit update_wel, bit wel_val);
    fork begin
      bit[TL_DW-1:0] rdata;
      flash_status_t pre_flash_status_val = `gmv(ral.flash_status);
      flash_status_t cur_flash_status_val;
      bit match;

      // it takes 3-4 cycles to update the status after spi item completes
      // since we may have another thread to keep polling this csr, it's easier to predict it
      // and compare with the backdoor value, to make sure both align
      cfg.clk_rst_vif.wait_n_clks(FLASH_STATUS_UPDATE_DLY_AFTER_CSB_DEASSERT + 1);
      flash_status_tl_pre_val_q.delete();

      if (flash_status_settle_q.size != 0) begin
        `DV_CHECK_LE(flash_status_settle_q.size, 1)
        void'(ral.flash_status.predict(.value(flash_status_settle_q[0]),
                                       .kind(UVM_PREDICT_WRITE)));
        `uvm_info(`gfn, $sformatf("flash_status updated to: 0x%0h", `gmv(ral.flash_status)),
                  UVM_MEDIUM)
        flash_status_settle_q.delete();
      end
      if (set_busy) begin
        void'(ral.flash_status.busy.predict(.value(1), .kind(UVM_PREDICT_READ)));
        `uvm_info(`gfn, "busy bit is set due to upload command", UVM_MEDIUM)
      end

      cur_flash_status_val = `gmv(ral.flash_status);
      if (update_wel && wel_val != cur_flash_status_val.wel) begin
        cur_flash_status_val.wel = wel_val;
        void'(ral.flash_status.predict(.value(cur_flash_status_val), .kind(UVM_PREDICT_READ)));
        `uvm_info(`gfn, $sformatf("update wel to %0d due to wren/wrdi command", wel_val),
                  UVM_MEDIUM)
      end
      // if sw updates this csr around the end of the spi item, it's hard to predict if the value
      // is accepted or not. So do a backdoor check, it's ok if the rdata matchs to predict value
      // or any value in the flash_status_q
      csr_rd(.ptr(ral.flash_status), .value(rdata), .backdoor(1));

      if (rdata == `gmv(ral.flash_status)) match = 1;

      if (!match) begin
        `DV_CHECK_LE(flash_status_q.size, 1)
        while (flash_status_q.size > 0) begin
          bit[TL_DW-1:0] predict_val = flash_status_q.pop_front();
          if (predict_val == rdata) begin
            match = 1;
            void'(ral.flash_status.predict(.value(predict_val), .kind(UVM_PREDICT_READ)));
            `uvm_info(`gfn, $sformatf("found match, flash_status updated to: 0x%0h", predict_val),
                      UVM_MEDIUM)
            break;
          end
        end
      end

      if (!match) begin
        `uvm_error(`gfn,
                   $sformatf("flash_status mismatch, backdoor value: 0x%0x, exp: 0x%0x, or %p",
                   rdata, `gmv(ral.flash_status), flash_status_q))
      end

      // when this is just updated, TL interface may read back old value and it's ok, it will get
      // the new one in the next read
      if (pre_flash_status_val != `gmv(ral.flash_status)) begin
        flash_status_tl_pre_val_q.push_back(pre_flash_status_val);
      end
    end join_none
  endfunction

  // flash status can be set by SW, then it's updated when a spi transaction completes
  // If a flash status write occurs during spi transaction, not sure if it will be taken or not
  // latch the flash_status at the beginning of the transaction. If some write happens during
  // transaction, save to flash_status_q. it's ok that HW update status to any value in both Q.
  virtual task forever_latch_flash_status();
    forever begin
      @(negedge cfg.spi_host_agent_cfg.vif.csb);
      if (flash_status_q.size > 0) begin
        flash_status_settle_q.delete();
        flash_status_settle_q.push_back(flash_status_q[$]);
        flash_status_q.delete();
      end
    end
  endtask

  // this only triages post-process cmd. read buffer cmd isn't handled here as it needs to be
  // processed during transaction.
  virtual function internal_process_cmd_e triage_flash_cmd(bit[7:0] opcode, output bit set_busy);
    internal_process_cmd_e cmd_type;
    bit is_status, is_jedec, is_sfdp;
    bit is_passthru = `gmv(ral.control.mode) == PassthroughMode;
    spi_device_reg_cmd_info reg_cmd_info = cfg.get_cmd_info_reg_by_opcode(opcode);

    set_busy = 0;
    if (reg_cmd_info != null && `gmv(reg_cmd_info.upload)) begin
      if (`gmv(reg_cmd_info.busy)) set_busy = 1;
      return UploadCmd;
    end

    is_status = opcode inside {READ_STATUS_1, READ_STATUS_2, READ_STATUS_3} &&
                cfg.is_internal_recog_cmd(opcode);
    if (is_passthru) is_status &= `gmv(ral.intercept_en.status);
    if (is_status) return InternalProcessStatus;

    is_jedec = opcode == READ_JEDEC && `gmv(ral.intercept_en.jedec) &&
              cfg.is_internal_recog_cmd(opcode);
    if (is_passthru) is_jedec &= `gmv(ral.intercept_en.jedec);
    if (is_jedec) return InternalProcessJedec;

    is_sfdp = opcode == READ_SFDP &&
              cfg.is_internal_recog_cmd(opcode);
    if (is_passthru) is_sfdp &= `gmv(ral.intercept_en.sfdp);
    if (is_sfdp) return InternalProcessSfdp;

    if (opcode inside {READ_CMD_LIST} && cfg.is_internal_recog_cmd(opcode)) begin
      return InternalProcessReadCmd;
    end

    if (cfg.is_internal_cfg_cmd(opcode)) return InternalProcessCfgCmd;

    return NoInternalProcess;
  endfunction

  virtual function bit is_opcode_passthrough(bit[7:0] opcode);
    int cmd_index = get_cmd_filter_index(opcode);
    int cmd_offset = get_cmd_filter_offset(opcode);
    bit filter = `gmv(ral.cmd_filter[cmd_index].filter[cmd_offset]);
    bit valid_cmd = cfg.spi_host_agent_cfg.is_opcode_supported(opcode);

    if (`gmv(ral.control.mode) != PassthroughMode) return 0;

    `uvm_info(`gfn, $sformatf("opcode filter: %0d, valid: %0d", filter, valid_cmd), UVM_MEDIUM)
    return !filter && valid_cmd;
  endfunction

  virtual function void check_internal_processed_read_status(spi_item item);
    int start_addr;
    bit [23:0] status = `gmv(ral.flash_status); // 3 bytes
    case (item.opcode)
      READ_STATUS_1: start_addr = 0;
      READ_STATUS_2: start_addr = 1;
      READ_STATUS_3: start_addr = 2;
      default: `uvm_error(`gfn, $sformatf("unexpected status opcode: 0x%0h", item.opcode))
    endcase
    foreach (item.payload_q[i]) begin
      // status has 3 bytes, if read OOB, it will wrap
      int offset = (start_addr + i) % 3;
      `DV_CHECK_CASE_EQ(item.payload_q[i], status[offset * 8 +: 8],
          $sformatf("status mismatch, offset %0d, act: 0x%0h, exp: 0x%0h",
              offset, item.payload_q[i], status[offset * 8 +: 8]))
    end
  endfunction

  virtual function void check_internal_processed_read_jedec(spi_item item);
    bit [7:0] exp_jedec_q[$];
    bit [15:0] id = `gmv(ral.jedec_id.id);
    bit [7:0]  mf = `gmv(ral.jedec_id.mf);

    repeat (`gmv(ral.jedec_cc.num_cc)) exp_jedec_q.push_back(`gmv(ral.jedec_cc.cc));

    exp_jedec_q.push_back(mf);
    exp_jedec_q.push_back(id[7:0]);
    exp_jedec_q.push_back(id[15:8]);

    foreach (item.payload_q[i]) begin
      if (i < exp_jedec_q.size) begin
        `DV_CHECK_CASE_EQ(item.payload_q[i], exp_jedec_q[i],
            $sformatf("act 0x%0x != exp 0x%0x, index: %0d", item.payload_q[i], exp_jedec_q[i], i))
      end else begin
        `DV_CHECK_CASE_EQ(item.payload_q[i], 0,
            $sformatf("act 0x%0x != exp 0x0, index: %0d (OOB)", item.payload_q[i], i))
      end
    end
  endfunction

  virtual function void check_internal_processed_read_sfdp(spi_item item);
    foreach (item.payload_q[i]) begin
      uvm_reg_addr_t addr, offset;

      // address should be 3 bytes, only the last byte is used
      `DV_CHECK_EQ(item.address_q.size, 3)
      offset = (item.address_q[2] + i) % SFDP_SIZE;

      compare_mem_byte(SFDP_START_ADDR, offset, item.payload_q[i], i, "SFDP");
    end
  endfunction

  virtual function void compare_mem_byte(bit [31:0] base_addr, bit [31:0] offset, bit[7:0] act_val,
                                         // these 2 inputs are for log only
                                         int payload_idx, string msg);
    bit [31:0] addr = get_converted_addr(base_addr + offset);
    `DV_CHECK(spi_mem.addr_exists(addr))
    spi_mem.compare_byte(addr, act_val);
      `uvm_info(`gfn, $sformatf(
                "%s compare idx: %0d, offset %0d, mem addr 0x%0x, act: 0x%0x, exp: 0x%0x",
                msg, payload_idx, offset, addr, act_val, spi_mem.read_byte(addr)), UVM_MEDIUM)
  endfunction

  // check read return data again exp_mem or downstream item
  // this doesn't handle read cmd falling in read buffer
  virtual function void check_read_cmd_data_for_non_read_buffer(spi_item up_item,
                                                                spi_item dn_item);
    bit [31:0] start_addr;
    // TODO, sample this for coverage
    read_addr_size_type_e read_addr_size_type;
    bit is_passthru = `gmv(ral.control.mode) == PassthroughMode;

    foreach (up_item.address_q[i]) begin
      if (i > 0) start_addr = start_addr << 8;
      start_addr[7:0] = up_item.address_q[i];
    end
    start_addr = convert_addr_from_byte_queue(up_item.address_q);

    if (dn_item != null) `DV_CHECK_EQ(up_item.payload_q.size, dn_item.payload_q.size)
    foreach (up_item.payload_q[i]) begin
      bit [31:0] cur_addr = start_addr + i;

      if (cfg.is_in_mailbox_region(cur_addr)) begin
        bit [31:0] offset = cur_addr % MAILBOX_BUFFER_SIZE;
        compare_mem_byte(MAILBOX_START_ADDR, offset, up_item.payload_q[i], i, "Mailbox");
      end else begin // out of mbx region
        string str;

        `DV_CHECK_EQ_FATAL(is_passthru, 1)
        if (dn_item != null) begin
          str = $sformatf("compare mbx data with downstread item. idx %0d, up: 0x%0x, dn: 0x%0x",
                          i, up_item.payload_q[i], dn_item.payload_q[i]);
          `DV_CHECK_CASE_EQ(up_item.payload_q[i], dn_item.payload_q[i], str)
        end else begin // cmd is filtered
          str = $sformatf("compare mbx data. idx %0d, value 0x%0x != z",
                          i, up_item.payload_q[i]);
          `DV_CHECK_CASE_EQ(up_item.payload_q[i], 8'dz, str)
        end

        `uvm_info(`gfn, str, UVM_MEDIUM)
      end
    end

    // TODO, sample read_addr_size_type for coverage
  endfunction

  virtual function void process_upload_cmd(spi_item item);
    bit [31:0] payload_start_addr = get_converted_addr(PAYLOAD_FIFO_START_ADDR);
    int payload_depth_exp;
    upload_cmd_q.push_back(item.opcode);
    intr_trigger_pending[CmdFifoNotEmpty] = 1;

    if (item.address_q.size > 0) begin
      bit[31:0] addr = convert_addr_from_byte_queue(item.address_q);
      upload_addr_q.push_back(addr);
    end

    foreach (item.payload_q[i]) begin
      uvm_reg_addr_t addr = payload_start_addr + (i % PAYLOAD_FIFO_SIZE);

      spi_mem.write_byte(addr, item.payload_q[i]);
      `uvm_info(`gfn, $sformatf("write upload payload idx %0d, mem addr 0x%0x, val: 0x%0x",
                i, addr, item.payload_q[i]), UVM_MEDIUM)
    end
    if (item.payload_q.size > 0) intr_trigger_pending[PayloadNotEmpty] = 1;

    update_cmdfifo_status();
    update_addrfifo_status();

    payload_depth_exp = item.payload_q.size > 256 ? 256 : item.payload_q.size;
    void'(ral.upload_status2.payload_depth.predict(.value(payload_depth_exp),
                                                   .kind(UVM_PREDICT_READ)));
    // if received payload is bigger than fifo size, payload_start_idx = payload size % fifo size.
    if (item.payload_q.size > PAYLOAD_FIFO_SIZE) begin
      int start_idx = item.payload_q.size % PAYLOAD_FIFO_SIZE;
      void'(ral.upload_status2.payload_start_idx.predict(.value(start_idx),
                                                         .kind(UVM_PREDICT_READ)));
    end else begin
      void'(ral.upload_status2.payload_start_idx.predict(.value(0), .kind(UVM_PREDICT_READ)));
    end
  endfunction

  virtual function void update_cmdfifo_status();
    void'(ral.upload_status.cmdfifo_depth.predict(.value(upload_cmd_q.size),
                                                  .kind(UVM_PREDICT_READ)));
    void'(ral.upload_status.cmdfifo_notempty.predict(.value(upload_cmd_q.size > 0),
                                                  .kind(UVM_PREDICT_READ)));
  endfunction

  virtual function void update_addrfifo_status();
    void'(ral.upload_status.addrfifo_depth.predict(.value(upload_addr_q.size),
                                                  .kind(UVM_PREDICT_READ)));
    void'(ral.upload_status.addrfifo_notempty.predict(.value(upload_addr_q.size > 0),
                                                  .kind(UVM_PREDICT_READ)));
  endfunction

  // convert offset to the mem address that is used to find the locaiton in exp_mem
  // lsb 2 bit will be kept
  virtual function bit [31:0] get_converted_addr(bit [31:0] offset);
    return ral.get_normalized_addr(offset) + offset[1:0];
  endfunction

  virtual function void handle_addr_payload_swap(spi_item item);
    spi_device_reg_cmd_info reg_cmd_info = cfg.get_cmd_info_reg_by_opcode(item.opcode);
    if (reg_cmd_info == null) return;

    if (`gmv(reg_cmd_info.addr_swap_en)) begin
      bit [TL_DW-1:0] mask = `gmv(ral.addr_swap_mask);
      bit [TL_DW-1:0] data = `gmv(ral.addr_swap_data);

      `uvm_info(`gfn, $sformatf("Swap addr for opcode: 0x%0h, mask/data: 0x%0h/0x%0h, old: %p",
          item.opcode, mask, data, item.address_q), UVM_MEDIUM)
      foreach (item.address_q[i]) begin
        // address_q[0] is the first collected address, but actual address is from MSB to LSB
        // (first one received is the last byte of the address)
        int addr_idx = item.address_q.size - i - 1;
        item.address_q[i] = (item.address_q[i] & ~mask[addr_idx*8 +: 8]) |
                            (data[addr_idx*8 +: 8] & mask[addr_idx*8 +: 8]);
      end
       `uvm_info(`gfn, $sformatf("New addr: %p", item.address_q), UVM_MEDIUM)
    end

    if (`gmv(reg_cmd_info.payload_swap_en)) begin
      bit [TL_DW-1:0] mask = `gmv(ral.payload_swap_mask);
      bit [TL_DW-1:0] data = `gmv(ral.payload_swap_data);
      // swap up to 4 bytes
      int swap_byte_num = item.payload_q.size > 4 ? 4 : item.payload_q.size;

      `uvm_info(`gfn, $sformatf("Swap addr for opcode: 0x%0h, mask/data: 0x%0h/0x%0h, old: %p",
          item.opcode, mask, data, item.payload_q[0:swap_byte_num]), UVM_MEDIUM)
      for (int i = 0; i < swap_byte_num; i++) begin
        item.payload_q[i] = (item.payload_q[i] & ~mask[i*8 +: 8]) |
                            (data[i*8 +: 8] & mask[i*8 +: 8]);
      end
      `uvm_info(`gfn, $sformatf("New payload: %p", item.payload_q[0:swap_byte_num]), UVM_MEDIUM)
    end
  endfunction

  virtual function void compare_passthru_item(spi_item upstream_item, bit is_intercepted);
    spi_item downstream_item;

    handle_addr_payload_swap(upstream_item);

    `DV_CHECK_EQ_FATAL(spi_passthrough_downstream_q.size, 1)
    downstream_item = spi_passthrough_downstream_q.pop_front();

    if (is_intercepted) begin
      // compare opcode and address. data is ignored as data is checked in
      // check_read_cmd_data_for_non_read_buffer
      `DV_CHECK_EQ(upstream_item.opcode, downstream_item.opcode)
      `DV_CHECK_EQ(upstream_item.address_q.size, downstream_item.address_q.size)
      foreach (upstream_item.address_q[i]) begin
        `DV_CHECK_EQ(upstream_item.address_q[i], downstream_item.address_q[i])
      end
    end else begin
      if (!downstream_item.compare(upstream_item)) begin
        `uvm_error(`gfn, $sformatf("Compare failed, downstream item:\n%s upstream item:\n%s",
              downstream_item.sprint(), upstream_item.sprint()))
      end
    end
  endfunction

  // extract spi items sent from device
  virtual task process_upstream_spi_device_fifo();
    spi_item item;
    forever begin
      upstream_spi_device_fifo.get(item);
      sendout_spi_tx_data({item.data[3], item.data[2], item.data[1], item.data[0]});
      `uvm_info(`gfn, $sformatf("upstream received device spi item:\n%0s", item.sprint()), UVM_HIGH)
    end
  endtask

  virtual task process_downstream_spi_fifo();
    spi_item downstream_item;
    spi_item upstream_item;
    forever begin
      downstream_spi_host_fifo.get(downstream_item);
      `uvm_info(`gfn, $sformatf("downstream received spi item:\n%0s", downstream_item.sprint()),
                UVM_MEDIUM)
      `DV_CHECK_EQ(`gmv(ral.control.mode), PassthroughMode)
      `DV_CHECK_EQ(spi_passthrough_downstream_q.size, 0)
      spi_passthrough_downstream_q.push_back(downstream_item);
    end
  endtask

  // read buffer cmd is handled separately as we can't wait until the item is completed.
  // while upstream reads the buffer, SW may prepare the data on the other side of the buffer.
  // when the item completes, the buffer may be overwritten with other data
  virtual task process_read_buffer_cmd();
    forever begin
      spi_item item;
      uint payload_idx;
      bit [31:0] start_addr, offset, read_buffer_addr;

      upstream_spi_req_fifo.get(item);
      if (!cfg.is_read_buffer_cmd(item)) continue;

      start_addr = convert_addr_from_byte_queue(item.address_q);
      `DV_SPINWAIT(
        while (1) begin
          wait (item.payload_q.size > payload_idx || item.mon_item_complete);
          if (item.payload_q.size > payload_idx) begin
            offset = (start_addr + payload_idx) % READ_BUFFER_SIZE;
            compare_mem_byte(READ_BUFFER_START_ADDR, offset, item.payload_q[payload_idx],
                             payload_idx, "Read buffer");
            read_buffer_addr = start_addr + payload_idx; // it's kept until reset
            payload_idx++; // clear to 0 when transaction is done
            predict_read_buffer_intr(read_buffer_addr + 1);
            `DV_CHECK_EQ(item.payload_q.size, payload_idx)
          end
          if (item.mon_item_complete) break;
        end
      )
      // only update when it has payload
      if (payload_idx > 0) begin
        `uvm_info(`gfn, $sformatf("Update last_read_addr to 0x%0x", read_buffer_addr), UVM_MEDIUM)
        void'(ral.last_read_addr.predict(.value(read_buffer_addr), .kind(UVM_PREDICT_READ)));
      end
    end
  endtask

  virtual function void predict_read_buffer_intr(int addr);
    int threshold = `gmv(ral.read_threshold);
    int offset = addr % READ_BUFFER_HALF_SIZE;

    if (offset >= threshold && threshold > 0 && !read_buffer_watermark_triggered) begin
      read_buffer_watermark_triggered = 1;
      intr_trigger_pending[ReadbufWatermark] = 1;
      `uvm_info(`gfn, $sformatf("read buffer watermark is triggered, addr: 0x%0x", addr),
                UVM_MEDIUM)
    end
    if (addr % READ_BUFFER_HALF_SIZE == 0) begin
      // after flip, WM can be triggered again
      read_buffer_watermark_triggered = 0;
      intr_trigger_pending[ReadbufFlip] = 1;
      `uvm_info(`gfn, $sformatf("read buffer flip is triggered, addr: 0x%0x", addr),
                UVM_MEDIUM)
    end
  endfunction

  // process_tl_access:this task processes incoming access into the IP over tl interface
  // this is already called in cip_base_scoreboard::process_tl_a/d_chan_fifo tasks
  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg csr;
    bit     do_read_check   = 1'b0; // TODO: fixme
    bit     write           = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end
    else if (csr_addr inside {[cfg.sram_start_addr:cfg.sram_end_addr]}) begin
      if (`gmv(ral.control.mode) == GenericMode) begin
        uint tx_base  = ral.txf_addr.base.get_mirrored_value();
        uint rx_base  = ral.rxf_addr.base.get_mirrored_value();
        uint tx_limit = ral.txf_addr.limit.get_mirrored_value();
        uint rx_limit = ral.rxf_addr.limit.get_mirrored_value();
        uint mem_addr = item.a_addr - cfg.sram_start_addr;
        tx_base[1:0] = 0;
        rx_base[1:0] = 0;
        if (mem_addr inside {[tx_base : tx_base + tx_limit]}) begin // TX address
          if (write && channel == AddrChannel) begin
            tx_mem.write(mem_addr - tx_base, item.a_data);
            `uvm_info(`gfn, $sformatf("write tx_mem addr 0x%0h, data: 0x%0h",
                                      mem_addr - tx_base, item.a_data), UVM_MEDIUM)
          end
        end else if (mem_addr inside {[rx_base : rx_base + rx_limit]}) begin // RX address
          if (!write && channel == DataChannel) begin //TODO UVM_ERROR unexpected write on RX mem
            uint            addr     = mem_addr - rx_base;
            bit [TL_DW-1:0] data_exp = rx_mem.read(addr);
            `DV_CHECK_EQ(item.d_data, data_exp, $sformatf("Compare SPI RX data, addr: 0x%0h", addr))
          end
        end else begin
          // TODO hit unlocated mem, sample coverage
        end
      end else begin
        if (!write) begin
          // cip_base_scoreboard compares the mem read only when the address exists
          // just need to ensure address exists here and mem check is done at process_mem_read
          `DV_CHECK(spi_mem.addr_exists(csr_addr))
        end
      end
      return;
    end
    else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // if incoming access is a write to a valid csr, then make updates right away
    // don't update flash_status predict value as it's updated at the end of spi transaction
    if (write && channel == AddrChannel && csr.get_name != "flash_status") begin
      void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
    end

    // process the csr req
    case (csr.get_name())
      "txf_ptr": begin
        if (write && channel == AddrChannel) begin
          update_tx_fifo_and_rptr();
        end
      end
      "rxf_ptr": begin
        if (write && channel == AddrChannel) begin
          update_rx_mem_fifo_and_wptr();
        end
      end
      "flash_status": begin
        if (write && channel == AddrChannel) begin
          // store the item in a queue as flash_status is updated at the end of spi transaction
          flash_status_q.push_back(item.a_data);
        end
        if (!write && channel == DataChannel) begin
          // it's ok to read back old value once.
          flash_status_t exp_val = `gmv(ral.flash_status);
          flash_status_t exp_data_q[$] = {flash_status_tl_pre_val_q, exp_val};
          `DV_CHECK(item.d_data inside {exp_data_q},
                    $sformatf("act (0x%0x) != exp %p", item.d_data, exp_data_q))
          flash_status_tl_pre_val_q.delete();
        end
        // check is done above and predict is done after spi item completes. can return now
        return;
      end
      "intr_state": begin
        if (!write && channel == DataChannel) begin
          bit [NumSpiDevIntr-1:0] intr_exp = `gmv(csr);
          foreach (intr_exp[i]) begin
            spi_device_intr_e intr = spi_device_intr_e'(i);
            // TODO, only test these interrupts for now
            if (!(i inside {ReadbufFlip, ReadbufWatermark,
                            CmdFifoNotEmpty, PayloadNotEmpty})) begin
              continue;
            end
            if (!intr_trigger_pending[i]) begin
              `DV_CHECK_EQ(item.d_data[i], intr_exp[i],
                           $sformatf("Compare %s mismatch, act (0x%0x) != exp %p",
                           intr.name, item.d_data[i], intr_exp[i]))
            end else begin
              // there is an interrupt pending, update interrupt to 1
              // skip the check, as either 0 or 1 is fine
              intr_exp[i] = 1;
              void'(csr.predict(.value(intr_exp), .kind(UVM_PREDICT_READ)));
              // clear pending interrupt
              intr_trigger_pending[i] = 0;
            end
          end // foreach (intr_exp[i])
          // skip updating predict value to d_data
          return;
        end // if (!write && channel == DataChannel)
        else if (write && channel == AddrChannel) begin
          bit [NumSpiDevIntr-1:0] intr_val = item.a_data;
          foreach (intr_val[i]) begin
            spi_device_intr_e intr = spi_device_intr_e'(i);
            if (intr_val[i]) begin
              `uvm_info(`gfn, $sformatf("Clear %s", intr.name), UVM_MEDIUM)
            end
          end
        end
      end
      "intr_test": begin
        if (write && channel == AddrChannel) begin
          bit [TL_DW-1:0] intr_en = ral.intr_enable.get_mirrored_value();
          bit [NumSpiDevIntr-1:0] intr_val;
          intr_val = `gmv(ral.intr_state) | item.a_data;
          if (cfg.en_cov) begin
            foreach (intr_val[i]) begin
              cov.intr_test_cg.sample(i, item.a_data[i], intr_en[i], intr_val[i]);
            end
          end
        end
      end
      "upload_cmdfifo": begin
        if (!write && channel == DataChannel) begin
          `DV_CHECK_GT(upload_cmd_q.size, 0)
          `DV_CHECK_EQ(item.d_data, upload_cmd_q.pop_front())
          update_cmdfifo_status();
        end
      end
      "upload_addrfifo": begin
        if (!write && channel == DataChannel) begin
          `DV_CHECK_GT(upload_addr_q.size, 0)
          `DV_CHECK_EQ(item.d_data, upload_addr_q.pop_front())
          update_addrfifo_status();
        end
      end
      "last_read_addr", "upload_status", "upload_status2": begin
        do_read_check = 1;
      end
      default: begin
        // TODO the other regs
      end
    endcase

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (!write && channel == DataChannel) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(item.d_data, `gmv(csr),
                    $sformatf("CSR %s compare mismatch act 0x%0x != exp 0x%0x",
                    csr.`gn, item.d_data, `gmv(csr)))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  // read data from mem then update tx fifo and tx_rptr
  virtual function void update_tx_fifo_and_rptr();
    uint filled_bytes = get_tx_sram_filled_bytes();
    // move data to fifo
    while (tx_word_q.size < 2 && filled_bytes >= SRAM_WORD_SIZE) begin
      tx_word_q.push_back(tx_mem.read(tx_rptr_exp[SRAM_MSB:0]));
      `uvm_info(`gfn, $sformatf("write tx_word_q rptr 0x%0h, data: 0x%0h",
                               tx_rptr_exp, tx_mem.read(tx_rptr_exp[SRAM_MSB:0])), UVM_MEDIUM)
      tx_rptr_exp = get_sram_new_ptr(.ptr(tx_rptr_exp),
                                     .increment(SRAM_WORD_SIZE),
                                     .sram_size_bytes(`GET_TX_ALLOCATED_SRAM_SIZE_BYTES));
      filled_bytes -= SRAM_WORD_SIZE;
    end
  endfunction

  // send out SPI data from tx_fifo and fetch more data from sram to fifo
  virtual function void sendout_spi_tx_data(bit [31:0] data_act);

    if (tx_word_q.size > 0) begin
      bit [31:0] data_exp     = tx_word_q.pop_front();
      if (cfg.spi_host_agent_cfg.bits_to_transfer == 7) begin
        if (cfg.spi_host_agent_cfg.device_bit_dir == 1)  begin
          data_exp[7] = 0;
        end else begin
          data_exp[0] = 0;
        end
      end
      `DV_CHECK_EQ(data_act, data_exp, "Compare SPI TX data")
      update_tx_fifo_and_rptr();
    end else begin // underflow
      // TODO coverage sample
      `uvm_info(`gfn, $sformatf("TX underflow data: 0x%0h", data_act), UVM_MEDIUM)
    end
  endfunction

  // when receive a spi rx data, save it in rx_fifo and then write to rx_mem
  // when rx_fifo is full (size=2) and no space in sram, drop it
  virtual function void receive_spi_rx_data(bit [TL_DW:0] data);
    if (get_rx_sram_space_bytes() >= SRAM_WORD_SIZE || rx_word_q.size < 2) begin
      rx_word_q.push_back(data);
      update_rx_mem_fifo_and_wptr();
    end
    else begin
      `uvm_info(`gfn, $sformatf("RX overflow data: 0x%0h ptr: 0x%0h", data, rx_wptr_exp),
                UVM_MEDIUM)
    end
  endfunction

  // Check if opcode is enabled and returns index of enabled opcode
  // Checks if there are duplicate enabled opcodes - not proper config
  // HW parses commands this way
  virtual function check_opcode_enable(bit [7:0] q_opcode, ref bit enable, ref bit [4:0] en_idx);
    enable = 0;
    en_idx = 24; // Larger than num of cmd_info if not enabled
    for (int i = 0; i<24; i++)  begin
      if (q_opcode == `gmv(ral.cmd_info[i].opcode) && `gmv(ral.cmd_info[i].valid) == 1) begin
        `DV_CHECK_EQ(enable, 0, "Each CMD_INFO slot should have unique opcode")
        enable = 1;
        en_idx = i;
      end
    end
  endfunction

  // Task that compares passthrough opcode and first 3B of address
  // TODO modify to check opcode, address and payload
  virtual function void compare_pass_opcode_addr(bit [31:0] data_act);
    bit enabled;
    bit [4:0] en_idx;
    bit [7:0] opcode = data_act[7:0];
    bit [4:0] cmd_index = opcode / 32;
    bit [4:0] cmd_offset = opcode % 32;
    bit [31:0] mask_swap = `gmv(ral.addr_swap_mask.mask);
    bit [31:0] data_swap = `gmv(ral.addr_swap_data.data);
    check_opcode_enable(opcode, enabled, en_idx);
    if (enabled && (`gmv(ral.cmd_filter[cmd_index].filter[cmd_offset]) == 0)) begin
      bit [31:0] data_exp     = rx_word_q.pop_front();
      if (`gmv(ral.cmd_info[en_idx].addr_swap_en) == 1) begin // Addr Swap enable
        for (int i = 0; i < 24; i++) begin // TODO add 4B Address Support
          if (mask_swap[i] == 1) begin
            data_exp[i+8] = data_swap[i];
          end
        end
      end
      `DV_CHECK_EQ(data_act, data_exp, "Compare PASSTHROUGH Data")
    end
  endfunction

  // update rx mem, fifo and wptr when receive a spi trans or when rptr is updated
  virtual function void update_rx_mem_fifo_and_wptr();
    uint space_bytes = get_rx_sram_space_bytes();
    // move from fifo to mem
    while (rx_word_q.size > 0 && space_bytes >= SRAM_WORD_SIZE) begin
      bit [TL_DW:0] data = rx_word_q.pop_front();
      rx_mem.write(rx_wptr_exp[SRAM_MSB:0], data);
      `uvm_info(`gfn, $sformatf("write rx_mem, addr 0x%0h, data: 0x%0h",
                                rx_wptr_exp, data), UVM_MEDIUM)
      rx_wptr_exp = get_sram_new_ptr(.ptr(rx_wptr_exp),
                                     .increment(SRAM_WORD_SIZE),
                                     .sram_size_bytes(`GET_RX_ALLOCATED_SRAM_SIZE_BYTES));
      space_bytes -= SRAM_WORD_SIZE;
    end
  endfunction

  virtual function uint get_tx_sram_filled_bytes();
    uint tx_wptr      = ral.txf_ptr.wptr.get_mirrored_value();
    uint filled_bytes = get_sram_filled_bytes(tx_wptr,
                                              tx_rptr_exp,
                                              `GET_TX_ALLOCATED_SRAM_SIZE_BYTES,
                                              {`gfn, "::get_tx_sram_filled_bytes"});
    return filled_bytes;
  endfunction

  virtual function uint get_rx_sram_space_bytes();
    uint rx_rptr     = ral.rxf_ptr.rptr.get_mirrored_value();
    uint space_bytes = get_sram_space_bytes(rx_wptr_exp,
                                            rx_rptr,
                                            `GET_RX_ALLOCATED_SRAM_SIZE_BYTES,
                                            {`gfn, "::get_rx_sram_space_bytes"});
    return space_bytes;
  endfunction

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    tx_rptr_exp = ral.txf_ptr.rptr.get_reset();
    rx_wptr_exp = ral.rxf_ptr.wptr.get_reset();
    intr_trigger_pending = ral.intr_state.get_reset();

    tx_word_q.delete();
    rx_word_q.delete();
    spi_passthrough_downstream_q.delete();
    flash_status_q.delete();
    flash_status_settle_q.delete();
    flash_status_tl_pre_val_q.delete();

    // used in seq
    cfg.next_read_buffer_addr = 0;
    cfg.read_buffer_ptr  = 0;

    read_buffer_watermark_triggered = 0;
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(spi_item, upstream_spi_host_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(spi_item, upstream_spi_device_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(spi_item, upstream_spi_req_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(spi_item, downstream_spi_host_fifo)
    `DV_CHECK_EQ(tx_word_q.size, 0)
    `DV_CHECK_EQ(rx_word_q.size, 0)
    `DV_CHECK_EQ(spi_passthrough_downstream_q.size, 0)
    `DV_CHECK_EQ(upload_cmd_q.size, 0)
    `DV_CHECK_EQ(upload_addr_q.size, 0)
    `DV_CHECK_EQ(flash_status_q.size, 0)
    `DV_CHECK_EQ(flash_status_settle_q.size, 0)
    `DV_CHECK_EQ(flash_status_tl_pre_val_q.size, 0)
  endfunction
endclass
