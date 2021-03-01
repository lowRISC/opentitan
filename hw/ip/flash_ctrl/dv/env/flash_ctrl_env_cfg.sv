// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_env_cfg extends cip_base_env_cfg #(.RAL_T(flash_ctrl_reg_block));

  // vifs
  mem_bkdr_vif mem_bkdr_vifs[flash_dv_part_e][flash_ctrl_pkg::NumBanks];

  // ext component cfgs
  rand tl_agent_cfg m_eflash_tl_agent_cfg;

  // seq cfg
  flash_ctrl_seq_cfg seq_cfg;

  // knobs
  // ral.status[init_wip] status is set for the very first clock cycle right out of reset.
  // This causes problems in the read value especially in CSR tests.
  int post_reset_delay_clks = 1;

  `uvm_object_utils_begin(flash_ctrl_env_cfg)
    `uvm_field_object(m_eflash_tl_agent_cfg, UVM_DEFAULT)
  `uvm_object_utils_end

  `uvm_object_new

  virtual function void initialize(bit [TL_AW-1:0] csr_base_addr = '1);
    list_of_alerts = flash_ctrl_env_pkg::LIST_OF_ALERTS;
    super.initialize(csr_base_addr);
    // create tl agent config obj
    m_eflash_tl_agent_cfg = tl_agent_cfg::type_id::create("m_eflash_tl_agent_cfg");
    m_eflash_tl_agent_cfg.if_mode = dv_utils_pkg::Host;

    // create the seq_cfg
    seq_cfg = flash_ctrl_seq_cfg::type_id::create("seq_cfg");

    // set num_interrupts & num_alerts
    begin
      uvm_reg rg = ral.get_reg_by_name("intr_state");
      if (rg != null) begin
        num_interrupts = ral.intr_state.get_n_used_bits();
      end
    end
  endfunction : initialize

  
  // --------------------------------------------
  // Back-door access methods
  // --------------------------------------------


  virtual function void flash_mem_bkdr_init(flash_dv_part_e part = FlashPartData,
                                            flash_mem_init_e flash_mem_init);
    case (flash_mem_init)
      FlashMemInitSet: begin
        foreach (mem_bkdr_vifs[part][i]) mem_bkdr_vifs[part][i].set_mem();
      end
      FlashMemInitClear: begin
        foreach (mem_bkdr_vifs[part][i]) mem_bkdr_vifs[part][i].clear_mem();
      end
      FlashMemInitRandomize: begin
        foreach (mem_bkdr_vifs[part][i]) mem_bkdr_vifs[part][i].randomize_mem();
      end
      FlashMemInitInvalidate: begin
        foreach (mem_bkdr_vifs[part][i]) mem_bkdr_vifs[part][i].invalidate_mem();
      end
    endcase
  endfunction : flash_mem_bkdr_init

  // Reads flash mem contents via backdoor.
  // The addr arg need not be word aligned- its the same addr programmed into the `control` CSR.
  // TODO: support for partition.
  virtual function void flash_mem_bkdr_read(flash_op_t flash_op,
                                            ref logic [TL_DW-1:0] data[$]);
    flash_mem_addr_attrs addr_attrs = new(flash_op.addr);
    data.delete();
    for (int i = 0; i < flash_op.num_words; i++) begin
      data[i] = mem_bkdr_vifs[flash_op.partition][addr_attrs.bank].read32(
          addr_attrs.bank_addr);
      `uvm_info(`gfn, $sformatf("flash_mem_bkdr_read: {%s} = 0x%0h",
                              addr_attrs.sprint(), data[i]), UVM_MEDIUM)
      addr_attrs.incr(TL_DBW);
    end
  endfunction : flash_mem_bkdr_read


  // Writes the flash mem contents via backdoor.
  // The addr arg need not be word aligned- its the same addr programmed into the `control` CSR.
  // TODO: support for partition.
  virtual function void flash_mem_bkdr_write(flash_op_t flash_op,
                                             flash_mem_init_e flash_mem_init,
                                             logic [TL_DW-1:0] data[$] = {});
    flash_mem_addr_attrs addr_attrs = new(flash_op.addr);
    logic [TL_DW-1:0] wr_data;
    case (flash_mem_init)
      FlashMemInitCustom: begin
        flash_op.num_words = data.size();
      end
      FlashMemInitSet: begin
        wr_data = {TL_DW{1'b1}};
      end
      FlashMemInitClear: begin
        wr_data = {TL_DW{1'b0}};
      end
      FlashMemInitInvalidate: begin
        wr_data = {TL_DW{1'bx}};
      end
    endcase
    for (int i = 0; i < flash_op.num_words; i++) begin
      logic [TL_DW-1:0] loc_data;
      if(flash_mem_init == FlashMemInitCustom)
        loc_data = data[i];
      else if (flash_mem_init == FlashMemInitRandomize)
        loc_data = $urandom;
      else
        loc_data = wr_data;
      mem_bkdr_vifs[flash_op.partition][addr_attrs.bank].write32(
                addr_attrs.bank_addr, loc_data);
      `uvm_info(`gfn, $sformatf("flash_mem_bkdr_write: {%s} = 0x%0h",
                               addr_attrs.sprint(), loc_data), UVM_MEDIUM)
      addr_attrs.incr(TL_DBW);
    end
  endfunction : flash_mem_bkdr_write

  // Checks flash mem contents via backdoor.
  // The addr arg need not be word aligned- its the same addr programmed into the `control` CSR.
  // TODO: support for partition.
  virtual function void flash_mem_bkdr_read_check(flash_op_t flash_op,
                                                  const ref bit [TL_DW-1:0] exp_data[$]);
    logic [TL_DW-1:0] data[$];
    flash_mem_bkdr_read(flash_op, data);
    foreach (data[i]) begin
      `DV_CHECK_CASE_EQ(data[i], exp_data[i])
    end
  endfunction : flash_mem_bkdr_read_check

  // Ensure that the flash page / bank has indeed been erased.
  virtual function void flash_mem_bkdr_erase_check(flash_op_t flash_op);
    flash_mem_addr_attrs    addr_attrs = new(flash_op.addr);
    bit [TL_AW-1:0]         erase_check_addr;
    uint                    num_words;

    case (flash_op.erase_type)
      flash_ctrl_pkg::FlashErasePage: begin
        erase_check_addr = addr_attrs.page_start_addr;
        num_words = FlashNumBusWordsPerPage;
      end
      flash_ctrl_pkg::FlashEraseBank: begin
        // TODO: check if bank erase was supported
        erase_check_addr = addr_attrs.bank_start_addr;
        num_words = FlashNumBusWordsPerBank;
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("Invalid erase_type: %0s", flash_op.erase_type.name()))
      end
    endcase
    `uvm_info(`gfn, $sformatf("flash_mem_bkdr_erase_check: addr = 0x%0h, num_words = %0d",
                              erase_check_addr, num_words), UVM_MEDIUM)

    for (int i = 0; i < num_words; i++) begin
      logic [TL_DW-1:0] data;
      data = mem_bkdr_vifs[flash_op.partition][addr_attrs.bank].read32(erase_check_addr);
      `uvm_info(`gfn, $sformatf("flash_mem_bkdr_erase_check: bank: %0d, addr: 0x%0h, data: 0x%0h",
                                addr_attrs.bank, erase_check_addr, data), UVM_MEDIUM)
      `DV_CHECK_CASE_EQ(data, '1)
      erase_check_addr += TL_DBW;
    end
  endfunction : flash_mem_bkdr_erase_check


endclass
