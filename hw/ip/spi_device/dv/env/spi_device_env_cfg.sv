// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class spi_device_env_cfg extends cip_base_env_cfg #(.RAL_T(spi_device_reg_block));
  rand spi_agent_cfg  spi_host_agent_cfg;
  rand spi_agent_cfg  spi_device_agent_cfg;
  bit [TL_AW-1:0]     sram_start_addr;
  bit [TL_AW-1:0]     sram_end_addr;

  // read buffer needs to be read with incremental address, otherwise, watermark/fip won't work
  // this needs to be kept across sequences and cleared when reset occurs. Only seq uses it.
  bit [TL_AW-1:0]     next_read_buffer_addr;
  // read_buffer_addr is updated after a transaction is done
  // this ptr is updated when a flip event occurs, so that we could know which part is
  // read by the SPI host, in order to update the other part
  bit [TL_AW-1:0]     read_buffer_ptr;

  // clock only needs to be configured once. flash and TPM sequences may start in parallel.
  // This prevents clk from being configured multiple times
  bit                 do_spi_clk_configure = 1;

  // can only configure the FW mem once after reset.
  bit                 do_spi_device_fw_mem_cfg = 1;

  // test may have 2 threads to configure spi_device for flash and TPM mode.
  // both may access the same csr `CFG`, have this to avoid accessing it at the same time.
  semaphore           spi_cfg_sema = new(1);

  // TODO(#15543) SW can only configure addr_4b after reset
  bit                 do_addr_4b_cfg;

  // when asserted this will reinitialise the scoreboard's memory models
  bit                 scb_clear_mems = 0;

  // in some sequence, both SW and HW may want to update this interrupt at the same time,
  // which is hard to handle in scb. In this case, disable the checker.
  // as long as all TPM requests can be read out and compared correctly, it's sufficient.
  bit                 en_check_tpm_not_empty_intr = 1;
  `uvm_object_utils_begin(spi_device_env_cfg)
    `uvm_field_object(spi_host_agent_cfg, UVM_DEFAULT)
    `uvm_field_object(spi_device_agent_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  function void scoreboard_clear_mems();
    scb_clear_mems = 1;
  endfunction

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    list_of_alerts = spi_device_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);
    // create spi agent config obj
    spi_host_agent_cfg = spi_agent_cfg::type_id::create("spi_host_agent_cfg");
    spi_device_agent_cfg = spi_agent_cfg::type_id::create("spi_device_agent_cfg");
    // set num_interrupts & num_alerts which will be used to create coverage and more
    num_interrupts = ral.intr_state.get_n_used_bits();

    sram_start_addr = ral.get_addr_from_offset(SRAM_OFFSET);
    sram_end_addr   = sram_start_addr + SRAM_SIZE - 1;

    // only support 1 outstanding TL item
    m_tl_agent_cfg.max_outstanding_req = 1;
  endfunction

  function spi_device_reg_cmd_info get_cmd_info_reg_by_opcode(bit [7:0] opcode);
    foreach (ral.cmd_info[i]) begin
      if (`gmv(ral.cmd_info[i].valid) == 1 && `gmv(ral.cmd_info[i].opcode) == opcode) begin
        return ral.cmd_info[i];
      end
    end
    return null;
  endfunction

  // Get mailbox base addr, the first 10 bits are 0
  function bit[31:0] get_mbx_base_addr();
    return `gmv(ral.mailbox_addr) >> 10 << 10;
  endfunction

  virtual function bit is_read_buffer_cmd(spi_item item);
    if (`gmv(ral.control.mode) != FlashMode ||
        spi_host_agent_cfg.spi_func_mode != SpiModeFlash ||
        !(item.opcode inside {READ_CMD_LIST}) ||
        !is_internal_recog_cmd(item.opcode)) begin
      return 0;
    end
    if (is_in_mailbox_region(convert_addr_from_byte_queue(item.address_q))) return 0;
    return 1;
  endfunction

  virtual function bit [31:0] is_in_mailbox_region(bit [31:0] addr);
    bit [31:0] mbx_base_addr = get_mbx_base_addr();
    bit is_passthru = `gmv(ral.control.mode) == PassthroughMode;
    bit mailbox_en;

    if (`gmv(ral.cfg.mailbox_en)) begin
      mailbox_en = 1;
      if (is_passthru) mailbox_en &= `gmv(ral.intercept_en.mbx);
    end
    if (addr inside {[mbx_base_addr: mbx_base_addr + MAILBOX_BUFFER_SIZE - 1]} && mailbox_en) begin
      return 1;
    end
    return 0;
  endfunction

  // if the cmd isn't in the first 11 slots, it won't be processed in spi_device
  // interception or returning data from spi mem won't occur. It can only passthru to downstream
  virtual function bit is_internal_recog_cmd(bit[7:0] opcode);
    for (int i = 0; i < NUM_INTERNAL_PROCESSED_CMD; i++) begin
      if (`GET_OPCODE_VALID_AND_MATCH(cmd_info[i], opcode)) return 1;
    end
    if (is_internal_cfg_cmd(opcode)) return 1;
    return 0;
  endfunction

  virtual function bit is_internal_cfg_cmd(bit[7:0] opcode);
    if (`GET_OPCODE_VALID_AND_MATCH(cmd_info_en4b, opcode) ||
        `GET_OPCODE_VALID_AND_MATCH(cmd_info_ex4b, opcode) ||
        `GET_OPCODE_VALID_AND_MATCH(cmd_info_wren, opcode) ||
        `GET_OPCODE_VALID_AND_MATCH(cmd_info_wrdi, opcode)) begin
      return 1;
    end
    return 0;
  endfunction

  // return 0/1 for active or inactive
  function automatic bit get_locality_active(byte index);
    byte access_val = `gmv(get_tpm_access_reg_field(index));
    return access_val[TPM_ACTIVE_LOCALITY_BIT_POS];
  endfunction

  function automatic uvm_reg_field get_tpm_access_reg_field(byte index);
    return ral.get_field_by_name($sformatf("access_%0d", index));
  endfunction
endclass
