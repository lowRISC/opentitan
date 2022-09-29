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

  `uvm_object_utils_begin(spi_device_env_cfg)
    `uvm_field_object(spi_host_agent_cfg, UVM_DEFAULT)
    `uvm_field_object(spi_device_agent_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

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

  function automatic void get_reg_val_in_byte_q(dv_base_reg csr, uint num_bytes,
                                                output bit [7:0] data_q[$]);
    bit [TL_DW-1:0] val = `gmv(csr);
    for (int i = 0; i < num_bytes; i++) data_q.push_back(val[8*i +: 8]);
  endfunction

  `define CREATE_TPM_CASE_STMT(TPM_NAME, CSR_NAME) \
    ``TPM_NAME``_OFFSET: begin \
      if (addr[1:0] >= ``TPM_NAME``_BYTE_SIZE) return 0; \
      get_reg_val_in_byte_q(ral.``CSR_NAME``, ``TPM_NAME``_BYTE_SIZE, reg_data_q); \
    end
  // return 1 and exp SPI return data if the TPM read value is directly from HW-returned registers
  function automatic bit is_hw_return_reg(bit [TPM_ADDR_WIDTH-1:0] addr,
                                          uint read_size,
                                          output bit [7:0] data_q[$]);
    bit [TPM_ADDR_WIDTH-1:0] base_addr = addr & TPM_BASE_ADDR_MASK;
    bit base_addr_match = (base_addr == TPM_BASE_ADDR);
    bit [TPM_LOCALITY_LSB_POS-1:0] aligned_offset;
    int locality;
    bit [7:0] reg_data_q[$], invalid_return_q[$];

    // CRB mode doesn't return directly from HW
    if (`gmv(ral.tpm_cfg.tpm_mode) == TpmCrbMode) return 0;
    // if chk isn't disabled, it needs to match the base addr
    if (!`gmv(ral.tpm_cfg.tpm_reg_chk_dis) && !base_addr_match) begin
      return 0;
    end

    locality = get_locality_from_addr(addr);

    for (int i = 0; i < read_size; i++) begin
      if (i < 4) invalid_return_q.push_back('hff);
      else       invalid_return_q.push_back(0);
    end
    // handle invalid locality
    if (locality >= MAX_TPM_LOCALITY) begin
      if (!`gmv(ral.tpm_cfg.tpm_reg_chk_dis) &&
          `gmv(ral.tpm_cfg.invalid_locality) &&
          base_addr_match) begin
        data_q = invalid_return_q;
        `uvm_info(`gfn, "return 'hff due to invalid locality", UVM_MEDIUM)
        return 1;
      end
      return 0;
    end

    aligned_offset = {addr[TPM_LOCALITY_LSB_POS-1:2], 2'd0};
    // if locality is inactive, return 'hff for TPM_STS
    if (!get_locality_active(locality) && aligned_offset == TPM_STS_OFFSET) begin
      data_q = invalid_return_q;
      `uvm_info(`gfn, "return 'hff due to reading TPM_STS on an inactive locality", UVM_MEDIUM)
      return 1;
    end

    case (aligned_offset)
      TPM_ACCESS_OFFSET: begin
        bit [7:0] reg_val;

        if (addr[1:0] >= TPM_ACCESS_BYTE_SIZE) return 0;
        reg_val = `gmv(get_tpm_access_reg_field(locality));
        reg_data_q.push_back(reg_val);
      end
      `CREATE_TPM_CASE_STMT(TPM_INT_ENABLE, tpm_int_enable)
      `CREATE_TPM_CASE_STMT(TPM_INT_VECTOR, tpm_int_vector)
      `CREATE_TPM_CASE_STMT(TPM_INT_STATUS, tpm_int_status)
      `CREATE_TPM_CASE_STMT(TPM_INTF_CAPABILITY, tpm_intf_capability)
      `CREATE_TPM_CASE_STMT(TPM_STS, tpm_sts)
      `CREATE_TPM_CASE_STMT(TPM_DID_VID, tpm_did_vid)
      `CREATE_TPM_CASE_STMT(TPM_RID, tpm_rid)
      default: return 0;
    endcase

    for (int i = 0; i < read_size; i++) begin
      int offset = i + addr[1:0];

      // if read exceeds the reg size, return 0
      if (offset < reg_data_q.size) data_q.push_back(reg_data_q[offset]);
      else                          data_q.push_back(0);
    end

    `uvm_info(`gfn, $sformatf("Read on the hw-returned reg, addr 0x%0x, data %p",
                              addr, data_q), UVM_MEDIUM)
    return 1;
  endfunction : is_hw_return_reg
  `undef CREATE_TPM_CASE_STMT
endclass
