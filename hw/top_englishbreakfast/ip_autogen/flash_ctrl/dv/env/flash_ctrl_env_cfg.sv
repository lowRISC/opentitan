// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
typedef class flash_ctrl_scoreboard;
typedef class flash_ctrl_otf_scoreboard;

class flash_ctrl_env_cfg extends cip_base_env_cfg #(
  .RAL_T(flash_ctrl_core_reg_block)
);

  // Type for an associative array on address and partition to record injected errors.
  typedef bit per_caller_err_addr_tbl_t[addr_t][flash_dv_part_e];
  // Type for a regular array per read_task_e of the associative array above.
  typedef per_caller_err_addr_tbl_t err_addr_tbl_t[NumReadTask];

  // Memory backdoor util instances for each partition in each bank.
  mem_bkdr_util mem_bkdr_util_h[flash_dv_part_e][flash_ctrl_pkg::NumBanks];

  // Pass scoreboard handle to address multiple exp_alert issue.
  flash_ctrl_scoreboard scb_h;
  flash_ctrl_otf_scoreboard otf_scb_h;

  // seq cfg
  flash_ctrl_seq_cfg seq_cfg;

  // Flash phy prim interface agent config
  flash_phy_prim_agent_cfg m_fpp_agent_cfg;
  // interface
  virtual flash_ctrl_if flash_ctrl_vif;
  virtual clk_rst_if clk_rst_vif_flash_ctrl_eflash_reg_block;
  virtual clk_rst_if clk_rst_vif_flash_ctrl_prim_reg_block;
  virtual flash_ctrl_mem_if flash_ctrl_mem_vif[NumBanks];

  // knobs
  // ral.status[init_wip] status is set for the very first clock cycle right out of reset.
  // This causes problems in the read value especially in CSR tests.
  int post_reset_delay_clks = 1;

  // Knob for blocking host reads
  bit block_host_rd = 0;

  // Knob for control direct read checking
  bit dir_rd_in_progress = 1'b0;

  // Knob for scoreboard write and check on reads
  bit scb_check = 0;

  // Knob for scoreboard set expected alert
  bit scb_set_exp_alert = 0;

  // Knob for Bank Erase
  bit bank_erase_enable = 1;

  // Enable full checks of the scoreboard memory model, enabled by default.
  bit check_full_scb_mem_model = 1'b1;

  // mem for scoreboard
  data_model_t scb_flash_data = '{default: 1};
  data_model_t scb_flash_info = '{default: 1};
  data_model_t scb_flash_info1 = '{default: 1};
  data_model_t scb_flash_info2 = '{default: 1};

  // Run small page rma
  bit en_small_rma = 0;

  // Knob to enable on the fly scoreboard.
  bit scb_otf_en = 0;

  // TB ecc support enable
  // With ecc enabled, read path requires pre encoded data patterns.
  // 0 : no ecc
  // 1 : ecc enable
  // Below mode use address split.
  // 2 : 1 bit error test mode
  //     Based on serr_pct, single bit error is injected in 'flash_mem_otf_read'
  // 3 : 2 bit error test mode
  // 4 : integrity error test mode
  ecc_mode_e ecc_mode = FlashEccDisabled;

  // For tracking addresses that have had errors injected use *err_addr_tbl, since they
  // persist past each transaction.

  // single bit error rate scale of 0~10. 10: 100%.
  int serr_pct = 0;
  // Tracks lines with single bit errors.
  local err_addr_tbl_t serr_addr_tbl;

  int serr_cnt[NumBanks] = '{default : 0};
  // latest single bit error address
  bit [OTFBankId:0] serr_addr[NumBanks];

  // Create serr only once. Used in directed test case.
  bit serr_once = 0;
  bit serr_created = 0;

  // Double bit error test
  int derr_pct = 0;
  int derr_idx[76];
  // Tracks lines with double bit errors.
  local err_addr_tbl_t derr_addr_tbl;
  bit derr_once = 0;
  bit derr_created[read_task_e];

  // Mark out standing transactions.
  // With heavy concurrency, derr can be injected where read transaction
  // is issued and outstanding.
  // This can change error expectation of the first transaction.
  // To handle this cornercase, don't assert derr on outstanding read location.
  int derr_otd[rd_cache_t];

  // Integrity ecc err
  int ierr_pct = 0;
  // Tracks lines with integrity errors.
  local err_addr_tbl_t ierr_addr_tbl;
  bit ierr_created [read_task_e];
  // Transaction counters for otf
  int otf_ctrl_wr_sent = 0;
  int otf_ctrl_wr_rcvd = 0;
  int otf_ctrl_rd_sent = 0;
  int otf_ctrl_rd_rcvd = 0;
  int otf_host_rd_sent = 0;
  int otf_host_rd_rcvd = 0;

  // Page to region map.
  // This is used to validate transactions based on their page address
  // and policy config associate with it.
  // 8 : default region
  int p2r_map[FlashNumPages] = '{default : 8};

  flash_mp_region_cfg_t mp_regions[MpRegions];
  flash_bank_mp_info_page_cfg_t mp_info[NumBanks][InfoTypes][];

  // Permission to access special partition
  // 0: secret / creator
  // 1: secret / owner
  // 2: isolated
  bit [2:0] allow_spec_info_acc = 3'h0;

  // Allow multiple expected allert in a single test
  bit multi_alert_en = 0;

  // Max delay for alerts in clocks
  uint alert_max_delay;

  // Max delay for alerts in ns
  int alert_max_delay_in_ns;

  // read data by host if
  data_q_t flash_rd_data;

  // 2bit of target prefix. Use with cfg.ecc_mode > FlashEccEnabled
  // When cfg.ecc_mode > FlashEccEnabled, this will be randomized
  // before sequence starts.
  // tgt_pre[0]: rd
  // tgt_pre[1]: direct_rd
  // tgt_pre[2]: wr
  // tgt_pre[3]: erase
  // then assigned to bit 18:17
  bit [1:0] tgt_pre[flash_dv_part_e][NumTgt];

  // Store recent 4 read address.
  // If address is here, there is high chance read data is in cache.
  // This can nullify error injection so task should avoid injecting error
  // for these addresses.
  flash_otf_read_entry otf_read_entry;

  // OTF Sequence parameters
  int       otf_num_rw = 250;
  int       otf_num_hr = 2500;
  int       otf_wr_pct = 1;
  int       otf_rd_pct = 1;
  // overflow error rate
  int       otf_bwr_pct = 1;
  int       otf_brd_pct = 1;

  // interrupt mode
  bit       intr_mode = 0;

  // interrupt mode buffer credit
  int       rd_crd = 16;

  // fifo level to trigger lvl interrupt
  int       rd_lvl = 0;
  int       wr_lvl = 0;

  // force all region enable to '1'
  // '0' doesn't affect randomization
  bit       en_always_read = 0;
  bit       en_always_erase = 0;
  bit       en_always_prog = 0;
  bit       en_always_all = 0;

  // This is not tied to plusarg.
  // Internal use only.
  bit       en_always_any = 0;

  bit       en_all_info_acc = 0;
  // tlul error transaction counter
  // compare at the end of sim
  int       tlul_core_exp_cnt = 0;
  int       tlul_core_obs_cnt = 0;

  int       tlul_eflash_exp_cnt = 0;
  int       tlul_eflash_obs_cnt = 0;

  // stop rma process
  bit       rma_ack_polling_stop = 0;

  // Store program data for read back check
  data_q_t prog_data[flash_op_t];

  // Pointer for bkdr mem task.
  logic [KeyWidth-1:0] otp_addr_key;
  logic [KeyWidth-1:0] otp_data_key;

  bit                  skip_init = 0;
  bit                  skip_init_buf_en = 0;
  bit                  wr_rnd_data = 1;
  int                  wait_rd_buf_en_timeout_ns = 100_000; // 100 us

  // hw info cfg override
  mubi4_t ovrd_scr_dis = MuBi4False;
  mubi4_t ovrd_ecc_dis = MuBi4False;

  `uvm_object_utils(flash_ctrl_env_cfg)
  `uvm_object_new

  string flash_ral_name = "flash_ctrl_eflash_reg_block";

  // default region cfg
  flash_mp_region_cfg_t default_region_cfg = '{
      default: MuBi4True,
      scramble_en: MuBi4False,
      ecc_en: MuBi4False,
      he_en: MuBi4False,
      // Below two values won't be programmed
      // rtl uses hardcoded values
      // start:0
      // size : 2 * 256 (0x200)
      num_pages: 512,
      start_page: 0
  };

  // default info cfg
  flash_bank_mp_info_page_cfg_t default_info_page_cfg = '{
      default: MuBi4True,
      scramble_en: MuBi4False,
      ecc_en: MuBi4False,
      he_en: MuBi4False
  };

  // 1page : 2048Byte
  // returns 9 bit (max 512) pages
  function int addr2page(bit[OTFBankId:0] addr);
    return (int'(addr[OTFBankId:11]));
  endfunction // addr2page

  virtual function flash_mp_region_cfg_t get_region(int page, bit dis = 1);
    flash_mp_region_cfg_t my_region;
    if (p2r_map[page] == 8) begin
      my_region = default_region_cfg;
    end else begin
      my_region = mp_regions[p2r_map[page]];
      if (my_region.en != MuBi4True) my_region = default_region_cfg;
    end
    if (dis) begin
      `uvm_info("get_region", $sformatf("page:%0d --> region:%0d",
                                        page, p2r_map[page]), UVM_MEDIUM)
    end
    return my_region;
  endfunction // get_region

  function flash_mp_region_cfg_t get_region_from_info(flash_bank_mp_info_page_cfg_t info);
    flash_mp_region_cfg_t region;
    region.en          = info.en;
    region.read_en     = info.read_en;
    region.program_en  = info.program_en;
    region.erase_en    = info.erase_en;
    region.scramble_en = info.scramble_en;
    region.ecc_en      = info.ecc_en;
    region.he_en       = info.he_en;
    return region;
  endfunction // get_region_from_info

  virtual function void initialize(addr_t csr_base_addr = '1);
    string prim_ral_name = "flash_ctrl_prim_reg_block";
    string fast_rcvr_name = "";

    list_of_alerts = flash_ctrl_env_pkg::LIST_OF_ALERTS;
    tl_intg_alert_name = "fatal_std_err";
    sec_cm_alert_name = tl_intg_alert_name;
    // Set up second RAL model for Flash memory
    ral_model_names.push_back(flash_ral_name);
    ral_model_names.push_back(prim_ral_name);

    // both RAL models use same clock frequency
    clk_freqs_mhz[flash_ral_name] = clk_freq_mhz;
    clk_freqs_mhz[prim_ral_name] = clk_freq_mhz;
    super.initialize(csr_base_addr);

    void'($value$plusargs("fast_rcvr_%s", fast_rcvr_name));
    if (fast_rcvr_name != "") begin
      m_alert_agent_cfgs[fast_rcvr_name].fast_rcvr = 1;
    end
    tl_intg_alert_fields[ral.std_fault_status.reg_intg_err] = 1;
    shadow_update_err_status_fields[ral.err_code.update_err] = 1;
    shadow_storage_err_status_fields[ral.std_fault_status.storage_err] = 1;

    // create the seq_cfg and call configure
    seq_cfg = flash_ctrl_seq_cfg::type_id::create("seq_cfg");
    seq_cfg.configure();

    m_fpp_agent_cfg = flash_phy_prim_agent_cfg::type_id::create("m_fpp_agent_cfg");
    m_fpp_agent_cfg.is_active = 0;
    m_fpp_agent_cfg.en_cov = 0;

    // set num_interrupts & num_alerts
    num_interrupts = ral.intr_state.get_n_used_bits();

    m_tl_agent_cfg.max_outstanding_req = 1;
    m_tl_agent_cfgs[flash_ral_name].max_outstanding_req = 2;
    m_tl_agent_cfgs[prim_ral_name].max_outstanding_req = 1;

    alert_max_delay = 20000;
    `uvm_info(`gfn, $sformatf("ral_model_names: %0p", ral_model_names), UVM_LOW)

    foreach (tgt_pre[FlashPartData][i]) tgt_pre[FlashPartData][i] = i;
    foreach (tgt_pre[FlashPartInfo][i]) tgt_pre[FlashPartInfo][i] = i;
    foreach (tgt_pre[FlashPartInfo1][i]) tgt_pre[FlashPartInfo1][i] = i;
    foreach (tgt_pre[FlashPartInfo2][i]) tgt_pre[FlashPartInfo2][i] = i;

    foreach (derr_idx[i]) derr_idx[i] = i;
    foreach (mp_info[i, j]) mp_info[i][j] = new[InfoTypeSize[j]];
    otf_read_entry = new("otf_read_entry");
  endfunction : initialize

  // For a given partition returns its size in bytes in each of the banks.
  function uint get_partition_words_num(flash_dv_part_e part);
    case(part)
      FlashPartData:    return BytesPerBank / 4;
      FlashPartInfo:    return InfoTypeBytes[0] / 4;
      FlashPartInfo1:   return InfoTypeBytes[1] / 4;
      FlashPartInfo2:   return InfoTypeBytes[2] / 4;
      default: `uvm_error(`gfn, $sformatf("Undefined partition - %s", part.name()))
    endcase
  endfunction : get_partition_words_num

  // Method to do a back-door update of a selected partition memory model to the actual flash data.
  // Usualy should only be done after flash initialization.
  task update_partition_mem_model(flash_dv_part_e part);
    flash_mem_addr_attrs addr_attr;
    data_4s_t bkdr_rd_data;
    uint partition_words_num;
    data_model_t scb_flash_model;
    addr_attr = new();
    partition_words_num = get_partition_words_num(part);

    `uvm_info(`gfn, $sformatf("\nStart back-door updating partition %s memory model\n",
                              part.name()), UVM_MEDIUM)

    for (int i = 0; i < flash_ctrl_pkg::NumBanks; i++) begin : iterate_all_banks
      addr_attr.set_attrs(i * BytesPerBank);
      for (int j = 0; j < partition_words_num; j++) begin : iterate_all_bank_partition_words
        bkdr_rd_data = mem_bkdr_util_h[part][addr_attr.bank].read32(addr_attr.bank_addr);
        if ($isunknown(bkdr_rd_data)) begin
          scb_flash_model[addr_attr.addr] = ALL_ONES;
        end else begin
          scb_flash_model[addr_attr.addr] = bkdr_rd_data;
        end
        addr_attr.incr(flash_ctrl_pkg::BusBytes);
      end : iterate_all_bank_partition_words
    end : iterate_all_banks

    case(part)
      flash_ctrl_env_pkg::FlashPartData:    scb_flash_data      = scb_flash_model;
      flash_ctrl_env_pkg::FlashPartInfo:    scb_flash_info      = scb_flash_model;
      flash_ctrl_env_pkg::FlashPartInfo1:   scb_flash_info1     = scb_flash_model;
      flash_ctrl_env_pkg::FlashPartInfo2:   scb_flash_info2     = scb_flash_model;
      default: `uvm_error(`gfn, $sformatf("Undefined partition - %s", part.name()))
    endcase

    `uvm_info(`gfn, $sformatf("\nFinished back-door updating partition %s memory model\n",
                              part.name()), UVM_MEDIUM)

  endtask : update_partition_mem_model

  // Backdoor initialize flash memory elements.
  // Applies the initialization scheme to the given flash partition in all banks.
  // @part is the type of flash partition.
  // @scheme is the type of initialization to be done.
  virtual task flash_mem_bkdr_init(flash_dv_part_e part = FlashPartData,
                                   flash_mem_init_e scheme);

    `uvm_info("flash_mem_bkdr_init", $sformatf("scheme: %s", scheme.name), UVM_MEDIUM)
    case (scheme)
      FlashMemInitSet: begin
        foreach (mem_bkdr_util_h[part][i]) mem_bkdr_util_h[part][i].set_mem();
      end
      FlashMemInitClear: begin
        foreach (mem_bkdr_util_h[part][i]) mem_bkdr_util_h[part][i].clear_mem();
      end
      FlashMemInitRandomize: begin
        foreach (mem_bkdr_util_h[part][i]) mem_bkdr_util_h[part][i].randomize_mem();
      end
      FlashMemInitInvalidate: begin
        foreach (mem_bkdr_util_h[part][i]) mem_bkdr_util_h[part][i].invalidate_mem();
      end
      FlashMemInitEccMode: begin
        foreach (mem_bkdr_util_h[part][i]) mem_bkdr_util_h[part][i].set_mem();
      end
      default: begin
        `uvm_error(`gfn, $sformatf("Undefined initialization scheme - %s", scheme.name()))
      end
    endcase

    // Update the memory model with the initialization data
    if (scb_check) update_partition_mem_model(part);
  endtask : flash_mem_bkdr_init

  // For a given partition returns its respective memory model.
  function data_model_t get_partition_mem_model(flash_ctrl_env_pkg::flash_dv_part_e part);
    case(part)
      flash_ctrl_env_pkg::FlashPartData:    return scb_flash_data;
      flash_ctrl_env_pkg::FlashPartInfo:    return scb_flash_info;
      flash_ctrl_env_pkg::FlashPartInfo1:   return scb_flash_info1;
      flash_ctrl_env_pkg::FlashPartInfo2:   return scb_flash_info2;
      default: `uvm_error(`gfn, $sformatf("Undefined partition - %s", part.name()))
    endcase
  endfunction : get_partition_mem_model

  // Task to back-door check a selected partition memory model
  // This will be called in the scoreboard check_phase if the check_full_scb_mem_model will
  //  be set to 1 (enabled by default).
  function void check_partition_mem_model(flash_ctrl_env_pkg::flash_dv_part_e part);
    flash_mem_addr_attrs addr_attr;
    data_4s_t bkdr_rd_data;
    data_model_t scb_flash_model = get_partition_mem_model(part);
    addr_attr = new();
    foreach (scb_flash_model[addr]) begin
      addr_attr.set_attrs(addr);
      bkdr_rd_data = mem_bkdr_util_h[part][addr_attr.bank].read32(addr_attr.bank_addr);
      if ($isunknown(bkdr_rd_data)) bkdr_rd_data = ALL_ONES;
      `DV_CHECK_EQ(bkdr_rd_data, scb_flash_model[addr],
                   $sformatf({"Memory model check failed in partition %s, bank %0d, addr 0x%0x ",
                              "(%0d)"}, part.name(), addr_attr.bank, addr_attr.bank_addr,
                              addr_attr.bank_addr))
    end
  endfunction : check_partition_mem_model

  // Task to back-door check the full memory model
  // This will be called in the scoreboard check_phase & between calls to the inner rand_ops vseq
  //  (in partner_flash_ctrl_base_vseq post_tran task) if the check_full_scb_mem_model will
  //  be set to 1 (enabled by default).
  function void check_mem_model();
    flash_ctrl_env_pkg::flash_dv_part_e part = part.first();
    `uvm_info(`gfn, $sformatf("\nStart checking all memory model\n"), UVM_MEDIUM)
    do begin
      check_partition_mem_model(part);
      part = part.next();
    end while (part != part.first());
    `uvm_info(`gfn, $sformatf("\nFinished checking all memory model\n"), UVM_MEDIUM)
  endfunction : check_mem_model

  // Read full word from the memory. (76bits per word line)
  // flash_op.op should be FlashOpRead
  function void flash_mem_otf_read(flash_op_t flash_op, ref fdata_q_t data);
    flash_dv_part_e partition;
    int bank;
    logic [flash_phy_pkg::FullDataWidth-1:0] rdata;
    int        size, is_odd, tail;

    // If address is not 8byte aligned, full 76bit has to be read.
    // This exception is identified using 4Byte address bit, (addr[2])
    // and size of 4byte word.
    is_odd = flash_op.addr[2];
    size = (flash_op.num_words + is_odd) / 2;
    tail = (flash_op.num_words + is_odd) % 2;
    // QW (8byte) align
    flash_op.addr[2:0] = 'h0;

    `uvm_info("flash_mem_otf_read", $sformatf(
              "addr:0x%x is_odd:%0d size:%0d tail:%0d wd:%0d", flash_op.addr, is_odd, size, tail,
              flash_op.num_words), UVM_MEDIUM)
    for (int i = 0; i < size; i++) begin
      flash_bkdr_read_full_word(flash_op, rdata);
      `uvm_info("flash_mem_otf_read", $sformatf("addr:0x%x data:0x%x", flash_op.addr, rdata),
                UVM_MEDIUM)
      data.push_back(rdata);
      flash_op.addr += 8;
    end
    if (tail) begin
      flash_bkdr_read_full_word(flash_op, rdata);
      `uvm_info("flash_mem_otf_read", $sformatf("addr:0x%x data:0x%x", flash_op.addr, rdata),
                UVM_MEDIUM)
      data.push_back(rdata);
    end
  endfunction // flash_mem_otf_read

  // Method to read one full width word of the flash.
  virtual function void flash_bkdr_read_full_word(flash_op_t flash_op,
                                          ref logic [flash_phy_pkg::FullDataWidth-1:0] word_data);
    flash_mem_addr_attrs addr_attrs = new(flash_op.addr);
    word_data = mem_bkdr_util_h[flash_op.partition][addr_attrs.bank].read(addr_attrs.bank_addr);
  endfunction : flash_bkdr_read_full_word

  // Reads flash mem contents via backdoor.
  //
  // The addr arg need not be word aligned - its the same addr programmed into the `control` CSR.
  virtual function void flash_mem_bkdr_read(flash_op_t flash_op, ref data_q_t data);
    flash_mem_addr_attrs             addr_attrs = new(flash_op.addr);

    if (flash_op.op == flash_ctrl_pkg::FlashOpErase) begin
      case (flash_op.erase_type)
        flash_ctrl_pkg::FlashErasePage: begin
          addr_attrs.set_attrs(addr_attrs.bank_start_addr + addr_attrs.page_start_addr);
          flash_op.num_words = FlashNumBusWordsPerPage;
        end
        flash_ctrl_pkg::FlashEraseBank: begin
          addr_attrs.set_attrs(addr_attrs.bank * BytesPerBank);
          case (flash_op.partition)
            FlashPartData: begin
              flash_op.num_words = FlashNumBusWordsPerBank;
            end
            FlashPartInfo: begin
              flash_op.num_words = InfoTypeBusWords[0];
            end
            default: begin
              `uvm_fatal(`gfn, $sformatf(
                         {
                           "Invalid partition for bank_erase: %0s. ",
                           "Bank erase is only valid in the data partition ",
                           "(FlashPartData) and the first info partition ",
                           "(FlashPartInfo)."
                         },
                         flash_op.partition.name()
                         ))
            end
          endcase
        end
        default: begin
          `uvm_fatal(`gfn, $sformatf("Invalid erase_type: %0s", flash_op.erase_type.name()))
        end
      endcase
    end

    data.delete();
    for (int i = 0; i < flash_op.num_words; i++) begin
      data[i] = mem_bkdr_util_h[flash_op.partition][addr_attrs.bank].read32(addr_attrs.bank_addr);
      `uvm_info(`gfn, $sformatf(
                                "flash_mem_bkdr_read: partition = %s , {%s} = 0x%0h",
                                flash_op.partition.name(),
                                addr_attrs.sprint(),
                                data[i]
                                ), UVM_HIGH)
      addr_attrs.incr(TL_DBW);
    end
  endfunction : flash_mem_bkdr_read

  // Writes the flash mem contents via backdoor.
  //
  // The addr need not be bus word aligned, Its the same addr programmed into the `control` CSR.
  // The data queue is sized for the bus word.
  virtual function void flash_mem_bkdr_write(flash_op_t flash_op, flash_mem_init_e scheme,
                                             data_q_t data = {});
    flash_mem_addr_attrs addr_attrs = new(flash_op.addr);
    data_4s_t wr_data;
    data_b_t mem_data;

    // Randomize the lower half-word (if Xs) if the first half-word written in the below loop is
    // corresponding upper half-word.
    if (addr_attrs.bank_addr[flash_ctrl_pkg::DataByteWidth-1]) begin
      _randomize_uninitialized_half_word(.partition(flash_op.partition), .bank(addr_attrs.bank),
                                         .addr(addr_attrs.word_addr));
    end

    case (scheme)
      FlashMemInitCustom: begin
        flash_op.num_words = data.size();
      end
      FlashMemInitSet: begin
        wr_data = {flash_ctrl_pkg::DataWidth{1'b1}};
      end
      FlashMemInitClear: begin
        wr_data = {flash_ctrl_pkg::DataWidth{1'b0}};
      end
      FlashMemInitInvalidate: begin
        wr_data = {flash_ctrl_pkg::DataWidth{1'bx}};
      end
      default: ; // Do nothing.
    endcase

    for (int i = 0; i < flash_op.num_words; i++) begin
      data_4s_t loc_data = (scheme == FlashMemInitCustom) ? data[i] :
                 (scheme == FlashMemInitRandomize) ? $urandom() : wr_data;

      _flash_full_write(flash_op.partition, addr_attrs.bank, addr_attrs.bank_addr, loc_data);
      `uvm_info(`gfn, $sformatf(
                                "flash_mem_bkdr_write: partition = %s, {%s} = 0x%0h",
                                flash_op.partition.name(),
                                addr_attrs.sprint(),
                                loc_data
                                ), UVM_HIGH)

      // update the scoreboard on backdoor-programs as well
      mem_data[0] = loc_data;
      set_scb_mem(1, flash_op.partition,
                  addr_attrs.addr, CustomVal, mem_data);

      // increment after all updates are complete
      addr_attrs.incr(TL_DBW);
    end

    // Randomize the upper half-word (if Xs) if the last word written in the above loop is
    // corresponding lower half-word.
    if (addr_attrs.bank_addr[flash_ctrl_pkg::DataByteWidth-1]) begin
      _randomize_uninitialized_half_word(.partition(flash_op.partition), .bank(addr_attrs.bank),
                                         .addr(addr_attrs.bank_addr));
    end
  endfunction : flash_mem_bkdr_write

  // Helper function that takes a 32-bit data and correctly populates the integrity ECC
  //
  function void _flash_full_write(flash_dv_part_e partition, uint bank,
                                  // bus word aligned address
                                  addr_t addr,
                                  data_t wr_data);

    // read back the full flash word
    logic [flash_ctrl_pkg::DataWidth-1:0] data;
    logic [7:0] intg_data;
    logic is_upper = addr[flash_ctrl_pkg::DataByteWidth-1];
    addr_t aligned_addr = addr;

    if (is_upper) begin
      aligned_addr = {addr[TL_AW-1:FlashDataByteWidth], {FlashDataByteWidth{1'b0}}};
    end

    // get the full flash word
    data = mem_bkdr_util_h[partition][bank].read64(aligned_addr);

    // writing the upper portion of the flash word
    if (is_upper) begin
      data = {wr_data, data[TL_DW-1:0]};
    end else begin
      data = {data[flash_ctrl_pkg::DataWidth-1:TL_DW], wr_data};
    end

    // calculate truncated integrity
    {intg_data, data} = prim_secded_pkg::prim_secded_hamming_72_64_enc(data);

    // program fully via backdoor
    // TODO: review this later.
    // it has to be write(aligned_addr, instead of write64(aligned_addr
    mem_bkdr_util_h[partition][bank].write64(aligned_addr, {intg_data[3:0], data});

    // Update scoreboard memory model with this back-door write
    if (scb_check) begin
      write_data_all_part(.part(partition), .addr({bank, addr[FlashMemAddrPageMsbBit:0]}),
                          .is_front_door(1'b0), .data(wr_data));
    end

  endfunction : _flash_full_write


  // Helper function that randomizes the half-word at the given address if unknown.
  //
  // When the 'other' flash half-word is being written by the flash_mem_bkdr_write() method, the
  // half-word at the given address needs to also be updated, of the data at that address is
  // unknown. This is needed because the flash_ctrl RTL internally fetches full words. This method
  // randomizes the data at the given address via backdoor.
  function void _randomize_uninitialized_half_word(flash_dv_part_e partition, uint bank,
                                                   addr_t addr);
    data_4s_t data = mem_bkdr_util_h[partition][bank].read32(addr);
    if ($isunknown(data)) begin
      `DV_CHECK_STD_RANDOMIZE_FATAL(data)
      `uvm_info(`gfn, $sformatf("Data at 0x%0h is Xs, writing random 0x%0h", addr, data), UVM_HIGH)
      _flash_full_write(partition, bank, addr, data);
    end
  endfunction

  // Checks flash mem contents via backdoor.
  //
  // The addr need not be bus word aligned. Its the same addr programmed into the `control` CSR.
  // The exp data queue is sized for the bus word.
  // TODO: support for partition.
  virtual function void flash_mem_bkdr_read_check(flash_op_t flash_op,
                                                  const ref data_q_t exp_data,
                                                  input bit check_match = 1,
                                                  bit scr_en = 0,
                                                  int ecc_en = 2);
    data_q_t data;
    flash_otf_item item;

    // Default value of ecc_en in this function should be the same as scr_en
    if (ecc_en == 2) ecc_en = scr_en;
    // If scramble is enabled, read data and descramble before return.
    if (scr_en) begin
      `uvm_create_obj(flash_otf_item, item)
      flash_mem_otf_read(flash_op, item.fq);
      flash_op.otf_addr = flash_op.addr;
      flash_op.otf_addr[BusAddrByteW-2:OTFHostId] = 'h0;

      item.region.scramble_en = MuBi4True;
      item.region.ecc_en = (ecc_en)? MuBi4True : MuBi4False;
      item.mem_addr = flash_op.otf_addr>>3;
      item.descramble(otp_addr_key, otp_data_key);
      foreach (item.dq[i]) data[i] = item.dq[i];
    end else begin
      flash_mem_bkdr_read(flash_op, data);
    end

    foreach (data[i]) begin
      if (check_match) begin
        `DV_CHECK_CASE_EQ(data[i], exp_data[i])
      end else begin
        `DV_CHECK_CASE_NE(data[i], exp_data[i])
      end
    end
  endfunction : flash_mem_bkdr_read_check

  // Verifies that the flash page / bank has indeed been erased.
  virtual function void flash_mem_bkdr_erase_check(flash_op_t flash_op, data_q_t exp_data = {},
                                                   bit check_match = 1);
    flash_mem_addr_attrs             addr_attrs = new(flash_op.addr);
    bit                  [TL_AW-1:0] erase_check_addr;
    string                           erase_page_num_msg;
    uint                             num_words;

    case (flash_op.erase_type)
      flash_ctrl_pkg::FlashErasePage: begin
        erase_check_addr = addr_attrs.page_start_addr;
        num_words = FlashNumBusWordsPerPage;
        erase_page_num_msg = $sformatf("page = %0d, ", addr_attrs.page);
      end
      flash_ctrl_pkg::FlashEraseBank: begin
        // This address is relative to the bank it's in.
        erase_check_addr   = 0;
        // No need to state page for bank erase.
        erase_page_num_msg = "";
        case (flash_op.partition)
          FlashPartData: begin
            num_words = FlashNumBusWordsPerBank;
          end
          FlashPartInfo: begin
            num_words = InfoTypeBusWords[0];
          end
          default: begin
            `uvm_fatal(`gfn, $sformatf(
                       {
                         "Invalid partition for bank_erase: %0s. ",
                         "Bank erase is only valid in the data partition ",
                         "(FlashPartData) and the first info partition ",
                         "(FlashPartInfo)."
                       },
                       flash_op.partition.name()
                       ))
          end
        endcase
      end
      default: begin
        `uvm_fatal(`gfn, $sformatf("Invalid erase_type: %0s", flash_op.erase_type.name()))
      end
    endcase
    `uvm_info(`gfn, $sformatf(
              {
                "flash_mem_bkdr_erase_check: Erase type = %s, bank = %0d, ",
                "partition = %s , %snum_words = %0d"
              },
              flash_op.erase_type.name(),
              addr_attrs.bank,
              flash_op.partition.name(),
              erase_page_num_msg,
              num_words
              ), UVM_MEDIUM)

    for (int i = 0; i < num_words; i++) begin
      data_4s_t data;
      data = mem_bkdr_util_h[flash_op.partition][addr_attrs.bank].read32(erase_check_addr);
      `uvm_info(`gfn, $sformatf(
                {
                  "flash_mem_bkdr_erase_check: Erase type = %s, bank: %0d, ",
                  "partition: %s , %saddr: 0x%0h, data: 0x%0h"
                },
                flash_op.erase_type.name(),
                addr_attrs.bank,
                flash_op.partition.name(),
                erase_page_num_msg,
                erase_check_addr,
                data
                ), UVM_HIGH)
      // If the expected data is not empty then it should be taken is expected. If it is empty the
      //  default expected value is checked - which for successful erase is all 1s.
      if (check_match) begin
        if (exp_data.size() <= i) begin
          `DV_CHECK_CASE_EQ(data, '1)
        end else begin
          `DV_CHECK_CASE_EQ(data, exp_data[i])
        end
      end else begin
        `DV_CHECK_CASE_NE(data, '1)
      end
      erase_check_addr += TL_DBW;
    end
  endfunction : flash_mem_bkdr_erase_check

  // Function to enable changing of the expected data to be checked in the post-transaction
  // checks.
  virtual function data_q_t calculate_expected_data(flash_op_t flash_op,
                                                    const ref data_q_t exp_data);
    data_q_t rdata;
    data_q_t data;
    flash_mem_bkdr_read(flash_op, rdata);
    foreach(exp_data[i]) data[i] = exp_data[i] & rdata[i];

    return data;
  endfunction : calculate_expected_data

  // Writing data to the scoreboard memory model, this writes one word of data to the selected
  //  address in the selected partition.
  // is_front_door added to indicate if this method called by front-door
  //  write (program transaction), which is the default, or by back-door methods.
  //  This is required for extending env.
  virtual function void write_data_all_part(flash_dv_part_e part, addr_t addr,
                                            bit is_front_door = 1'b1, ref data_t data);
  `uvm_info(`gfn, $sformatf("WRITE SCB MEM part: %0s addr:%0h data:0x%0h",
                            part.name, addr, data), UVM_HIGH)
    case (part)
      FlashPartData: scb_flash_data[addr] = data;
      FlashPartInfo: scb_flash_info[addr] = data;
      FlashPartInfo1: scb_flash_info1[addr] = data;
      FlashPartInfo2: scb_flash_info2[addr] = data;
      default: `uvm_fatal(`gfn, "flash_ctrl_scoreboard: Partition type not supported!")
    endcase
  endfunction

  // Task for clean scb memory
  virtual function reset_scb_mem();
    scb_flash_data.delete();
    scb_flash_info.delete();
    scb_flash_info1.delete();
    scb_flash_info2.delete();
  endfunction : reset_scb_mem

  // Task for set scb memory
  virtual function set_scb_mem(int bkd_num_words, flash_dv_part_e bkd_partition,
                               addr_t write_bkd_addr,flash_scb_wr_e val_type,
                               data_b_t custom_val = {});
    addr_t wr_bkd_addr;
    data_t wr_value;

    `uvm_info(`gfn, $sformatf(
              "SET SCB MEM TEST part: %0s addr:%0h data:0x%0h num: %0d",
              bkd_partition.name,
              write_bkd_addr,
              wr_value,
              bkd_num_words
              ), UVM_HIGH)
    wr_bkd_addr = {write_bkd_addr[TL_AW-1:2], 2'b00};
    `uvm_info(`gfn, $sformatf("SET SCB MEM ADDR:%0h", wr_bkd_addr), UVM_HIGH)
    for (int i = 0; i < bkd_num_words; i++) begin
      case (val_type)
        AllOnes: begin
          wr_value = ALL_ONES;
        end
        AllZeros: begin
          wr_value = ALL_ZEROS;
        end
        CustomVal: begin
          wr_value = custom_val[i];
        end
        default: `uvm_fatal(`gfn, "Unknown write type, allowed: AllOnes, AllZeros, CustomVal")
      endcase
      `uvm_info(`gfn, $sformatf(
                "SET SCB MEM part: %0s addr:%0h data:0x%0h num: %0d",
                bkd_partition.name,
                wr_bkd_addr,
                wr_value,
                bkd_num_words
                ), UVM_HIGH)
      write_data_all_part(.part(bkd_partition), .addr(wr_bkd_addr), .is_front_door(1'b0),
                          .data(wr_value));
      wr_bkd_addr = wr_bkd_addr + 4;
    end
  endfunction : set_scb_mem

  // Increase single bit error count.
  function void inc_serr_cnt(int bank, bit dis = 0);
    if (serr_cnt[bank] < 255) serr_cnt[bank]++;
    if (dis) begin
      `uvm_info("inc_serr_cnt", $sformatf("serr_cnt[%0d]=%0d", bank, serr_cnt[bank]), UVM_MEDIUM)
    end
  endfunction

  // Flip a bit at given address.
  function void flash_bit_flip(mem_bkdr_util _h, addr_t addr, int idx);
    bit [75:0] rdata;
    rdata = _h.read(addr);
    `uvm_info(`gfn, $sformatf("ECC error injection at address 0x%x for bit %0d", addr, idx),
              UVM_MEDIUM)
    rdata[idx] = ~rdata[idx];
    _h.write(addr, rdata);
  endfunction

  // Corrupt integrity check value only
  virtual function void flash_icv_flip(mem_bkdr_util _h, addr_t addr, flash_dv_part_e part,
                               bit bank, flash_otf_item exp_item);
    flash_otf_item item;

    `uvm_create_obj(flash_otf_item, item)
    item.dq.push_back($urandom());
    item.dq.push_back($urandom());
    if (part == FlashPartData) begin
      addr_t full_addr = addr;
      full_addr[OTFBankId] = bank;
      item.region = get_region(addr2page(full_addr));
    end else begin
      item.region = get_region_from_info(mp_info[bank][part>>1][addr2page(addr)]);
    end
    `uvm_info(`gfn, $sformatf("Integrity error injection at address 0x%x", addr), UVM_MEDIUM)
    item.scramble(exp_item.addr_key, exp_item.data_key, addr, 1, 1);
    _h.write(addr, item.fq[0]);
    item.clear_qs();
  endfunction

  // This shows errors injected per the given caller table.
  local function void show_errors(ref per_caller_err_addr_tbl_t addr_tbl);
    addr_t addr;
    if (addr_tbl.first(addr) == 0) return;
    while (addr_tbl.next(addr) != 0) begin
      flash_dv_part_e part;
      `DV_CHECK_EQ(addr_tbl[addr].first(part), 1)
      do
        `uvm_info(`gfn, $sformatf("error injected at addr:0x%x, part:%0s", addr, part.name),
                  UVM_MEDIUM)
      while (addr_tbl[addr].next(part) != 0);
    end
  endfunction

  function void show_derrors(read_task_e caller);
    `uvm_info(`gfn, $sformatf("Double bit errors injected for %s caller:", caller.name),
              UVM_MEDIUM)
    show_errors(derr_addr_tbl[caller]);
  endfunction

  local function int err_count(ref per_caller_err_addr_tbl_t err_addr_tbl);
    int count = 0;
    addr_t addr;
    if (err_addr_tbl.first(addr) == 0) return 0;
    while (err_addr_tbl.next(addr) != 0) begin
      flash_dv_part_e part;
      `DV_CHECK_EQ(err_addr_tbl[addr].first(part), 1)
      do count++; while (err_addr_tbl[addr].next(part) != 0);
    end
    return count;
  endfunction

  // These count the total number of errors per caller for the different error kinds.
  function int derr_count(input read_task_e caller);
    return err_count(derr_addr_tbl[caller]);
  endfunction

  function int ierr_count(input read_task_e caller);
    return err_count(ierr_addr_tbl[caller]);
  endfunction

  function int serr_count(input read_task_e caller);
    return err_count(serr_addr_tbl[caller]);
  endfunction

  local function bit address_has_err(ref err_addr_tbl_t err_addr_tbl, input addr_t addr,
                                     input flash_dv_part_e part);
    return (err_addr_tbl[ReadTaskCtrl].exists(addr) &&
            err_addr_tbl[ReadTaskCtrl][addr].exists(part)) ||
           (err_addr_tbl[ReadTaskHost].exists(addr) &&
            err_addr_tbl[ReadTaskHost][addr].exists(part));
  endfunction

  // These functions are used to track the creation of lines with bit errors.
  function bit address_has_derr(addr_t addr, flash_dv_part_e part);
    return address_has_err(derr_addr_tbl, addr, part);
  endfunction

  function bit address_has_ierr(addr_t addr, flash_dv_part_e part);
    return address_has_err(ierr_addr_tbl, addr, part);
  endfunction

  function bit address_has_serr(addr_t addr, flash_dv_part_e part);
    return address_has_err(serr_addr_tbl, addr, part);
  endfunction

  function bit address_has_some_injected_error(addr_t addr, flash_dv_part_e part);
    return address_has_derr(addr, part) || address_has_ierr(addr, part) ||
        address_has_serr(addr, part);
  endfunction

  virtual function bit address_has_ecc_injected_error(addr_t addr, flash_dv_part_e part);
    return address_has_derr(addr, part) || address_has_serr(addr, part);
  endfunction

  protected function void add_derr(input addr_t addr, input flash_dv_part_e partition,
                                   input read_task_e caller, input int idx_0, input int idx_1);
    int bank = addr[OTFBankId];

    `uvm_info(`gfn, $sformatf(
              "double bit ecc error injected for %s at bank %0d %s addr:0x%x bits %0d and %0d",
              caller.name, bank, partition.name, addr, idx_0, idx_1),
              UVM_MEDIUM)
    derr_addr_tbl[caller][addr][partition] = 1;
    derr_created[caller] = 1;
  endfunction

  protected function void add_ierr(input addr_t addr, input flash_dv_part_e partition,
                                   input read_task_e caller);
    int bank = addr[OTFBankId];

    `uvm_info(`gfn, $sformatf("icv error injected for %s at bank %0d %s addr:0x%x",
                               caller.name, bank, partition.name, addr),
              UVM_MEDIUM)
    ierr_addr_tbl[caller][addr][partition] = 1;
    ierr_created[caller] = 1;
  endfunction

  function void add_serr(input addr_t addr, input flash_dv_part_e partition,
                         input read_task_e caller, input int bit_index);
    int bank = addr[OTFBankId];

    `uvm_info(`gfn, $sformatf(
              "single bit ecc error injected for %s at bank %0d %s addr:0x%x bit %0d",
              caller.name, bank, partition.name, addr, bit_index), UVM_MEDIUM)
    serr_addr_tbl[caller][addr][partition] = 1;
  endfunction

  // Create bit error following flash_op and ecc_mode.
  // @caller : 0 controller,  1: host
  virtual function void add_bit_err(flash_op_t flash_op, read_task_e caller = ReadTaskCtrl,
                            flash_otf_item item = null);
    flash_dv_part_e partition;
    int bank;
    bit [75:0] rdata;
    int        size, is_odd, tail;
    // The flash word aligned address including the bank.
    addr_t addr_cp;
    rd_cache_t rd_entry;
    string     name = $sformatf("add_bit_err from %s", caller.name);

    bank = flash_op.addr[OTFBankId];
    partition = flash_op.partition;
    rd_entry.bank = bank;
    rd_entry.part = partition;
    // If address is not 8byte aligned, full 76bit has to be read.
    // This exception is identified using 4Byte address bit, (addr[2])
    // and size of 4byte word.
    is_odd = flash_op.addr[2];
    size = (flash_op.num_words + is_odd) / 2;
    tail = (flash_op.num_words + is_odd) % 2;

    addr_cp = flash_op.addr;
    // flash word is 8 byte aligned
    addr_cp[2:0] = 'h0;

    // Include tail in the range of flash words to consider for error injection.
    for (int i = 0; i < size + tail; i++) begin
      // For controller initiated read, in the worst case, each word (8byte) can belong to
      // different memory protection region.
      // So before inject bit error, we have to check per word ecc_en
      // to make sure bit error injection become valid.
      // If ecc is not enabled, bit error cannot be detected.
      if (caller == ReadTaskHost || (item.ctrl_rd_region_q[i].ecc_en == MuBi4True)) begin
        otf_addr_t otf_addr = otf_addr_t'(addr_cp);
        rd_entry.addr = addr_cp;
        if (ecc_mode == FlashSerrTestMode) begin
          randcase
            serr_pct: begin
              int err_idx;
              if (serr_once && serr_created) continue;
              // Do not inject more than one error per address.
              if (address_has_some_injected_error(addr_cp, partition)) begin
                 `uvm_info(`gfn, $sformatf(
                           "single bit error injection %s bank:%0d addr:0x%x blocked by prior",
                           partition.name, bank, otf_addr), UVM_MEDIUM)
                continue;
              end
              err_idx = $urandom_range(0, 75);
              flash_bit_flip(mem_bkdr_util_h[partition][bank], otf_addr, err_idx);
              add_serr(addr_cp, partition, caller, err_idx);
            end
            10-serr_pct: begin
            end
          endcase
        end else if (ecc_mode == FlashIerrTestMode) begin
          randcase
            ierr_pct: begin
              if (derr_otd.exists(rd_entry)) begin
                `uvm_info(`gfn, $sformatf(
                          "icv error injection %s bank:%0d addr:0x%x blocked by otd",
                          partition.name, bank, otf_addr), UVM_MEDIUM)
                continue;
              end
              if (address_has_some_injected_error(addr_cp, partition)) begin
                `uvm_info(`gfn, $sformatf(
                          "icv error injection %s bank:%0d addr:0x%x blocked by prior error",
                          partition.name, bank, otf_addr), UVM_MEDIUM)
                continue;
              end
              flash_icv_flip(mem_bkdr_util_h[partition][bank], otf_addr, partition, bank,
                             item);
              add_ierr(addr_cp, partition, caller);
            end
            10-ierr_pct: begin
            end
          endcase // randcase
        end else begin // ecc_mode == FlashDerrTestMode)
          randcase
            derr_pct: begin
              string block_reason = "";
              if (derr_once == 1 && derr_created[caller] == 1'b1) continue;
              if (derr_otd.exists(rd_entry)) begin
                block_reason = "otd";
              end else if (address_has_some_injected_error(addr_cp, partition)) begin
                block_reason = "prior error";
              end else if (otf_read_entry.hash.exists(rd_entry)) begin
                block_reason = "otf_read_entry";
              end
              if (block_reason != "") begin
                `uvm_info(`gfn, $sformatf(
                          "double bit error injection %s bank:%0d addr:0x%x blocked by %s",
                          partition.name, bank, otf_addr, block_reason), UVM_MEDIUM)
                continue;
              end
              derr_idx.shuffle();
              flash_bit_flip(mem_bkdr_util_h[partition][bank], otf_addr, derr_idx[0]);
              flash_bit_flip(mem_bkdr_util_h[partition][bank], otf_addr, derr_idx[1]);
              add_derr(addr_cp, partition, caller, derr_idx[0], derr_idx[1]);
            end
            10-derr_pct: begin
            end
          endcase
        end
        addr_cp += 8;
        // Don't change banks.
        if (addr_cp[OTFBankId] != bank) break;
      end
    end
  endfunction : add_bit_err

  // Increase outstanding table entry.
  function void inc_otd_tbl(bit bank, addr_t addr, flash_dv_part_e part);
    rd_cache_t ent;
    ent.bank = bank;
    ent.addr = align_to_flash_word(addr);
    ent.part = part;
    if (!derr_otd.exists(ent)) begin
      derr_otd[ent] = 1;
    end else begin
      derr_otd[ent]++;
    end
  endfunction // inc_otd_tbl

  // Descrease outstanding table entry.
  function void dec_otd_tbl(bit bank, addr_t addr, flash_dv_part_e part);
    rd_cache_t ent;
    ent.bank = bank;
    ent.addr = align_to_flash_word(addr);
    ent.part = part;
    if (!derr_otd.exists(ent)) begin
      `uvm_error("dec_otd_tbl", $sformatf("addr %x %s doesn't exits", addr, part.name))
    end else begin
      derr_otd[ent]--;
      if (derr_otd[ent] == 0) derr_otd.delete(ent);
    end
  endfunction // dec_otd_tbl

  function flash_dv_part_e get_part(flash_part_e part,
                                    logic [InfoTypesWidth-1:0] mem_info_sel);
    if (part == FlashPartData) begin
      return FlashPartData;
    end else begin
      case (mem_info_sel)
        1: return FlashPartInfo1;
        2: return FlashPartInfo2;
        default: return FlashPartInfo;
      endcase
    end
  endfunction // get_part

  virtual function void load_otf_mem_page(flash_dv_part_e part,
                                          int bank,
                                          int page);
    addr_t addr = '0;
    addr[OTFBankId-1:11] = page;
    `uvm_info(`gfn, $sformatf("in load_otf_mem_page bank:%0d %s, page:%0d", bank, part.name, page),
              UVM_HIGH)
    update_otf_mem_read_zone(part, bank, addr, addr + BytesPerPage - 1);
  endfunction : load_otf_mem_page

  function void update_otf_mem_read_zone(flash_dv_part_e part, int bank,
                                         addr_t start_addr, addr_t end_addr);
    start_addr = align_to_flash_word(start_addr);
    `uvm_info(`gfn, $sformatf(
              "mem_bkdr initializing bank:%0d %s from 0x%x to 0x%x per attributes",
              bank, part.name, start_addr, end_addr),
              UVM_HIGH)
    for (addr_t addr = start_addr; addr <= end_addr; addr += 8) begin
      flash_otf_item item;
      int page;
      bit [BankAddrW-1:0] mem_addr;

      `uvm_create_obj(flash_otf_item, item)
      item.dq.push_back($urandom());
      item.dq.push_back($urandom());
      if (part == FlashPartData) begin
        addr_t pd_addr = addr;
        pd_addr[OTFBankId] = bank;
        page = addr2page(pd_addr);
        item.region = get_region(page, 0);
      end else begin
        page = addr2page(addr);
        item.region = get_region_from_info(mp_info[bank][part>>1][page]);
      end
      item.page = page;
      `uvm_info(`gfn, $sformatf(
                "update_otf_mem_read_zone part:%0d, bank:%0d addr:0x%08x orig data:0x%0x%0x",
                part, bank, addr, item.dq[1], item.dq[0]), UVM_HIGH)
      item.scramble(otp_addr_key, otp_data_key, addr, 0);
      `uvm_info(`gfn, $sformatf(
                "update_otf_mem_read_zone part:%0d, bank:%0d addr:0x%08x scr data:0x%x",
                part, bank, addr, item.fq[0]), UVM_HIGH)

      mem_bkdr_util_h[part][bank].write(addr, item.fq[0]);
      // address should be mem_addr
      mem_addr = addr >> 3;
      if (part == FlashPartData) otf_scb_h.data_mem[bank][mem_addr] = item.fq[0];
      else otf_scb_h.info_mem[bank][part>>1][mem_addr] = item.fq[0];
    end
  endfunction : update_otf_mem_read_zone

  // Update memory with random data through backdoor.
  // Data can be either scrambled or attached calculated ecc if config in the address
  // is enabled.
  virtual task preload_mem();
    for (int j = 0; j < NumBanks; j++) begin
      for (int i = 0; i < InfoTypeSize[0]; i++)
        load_otf_mem_page(flash_ctrl_env_pkg::FlashPartInfo, j, i);
      for (int i = 0; i < InfoTypeSize[1]; i++)
        load_otf_mem_page(flash_ctrl_env_pkg::FlashPartInfo1, j, i);
      for (int i = 0; i < InfoTypeSize[2]; i++)
        load_otf_mem_page(flash_ctrl_env_pkg::FlashPartInfo2, j, i);
      for (int i = 0; i < PagesPerBank; i++)
        load_otf_mem_page(flash_ctrl_env_pkg::FlashPartData, j, i);
    end
  endtask

  // Print a page of the memory
  function void print_page(int bank, flash_dv_part_e part, int page);
    string name = $sformatf("%s_bank%0d_page%0d",part.name, bank, page);
    addr_t addr;
    bit [75:0] rdata;
    addr[OTFBankId-1:11] = page;
    for (int i = 0; i < 256; i++) begin
      rdata = mem_bkdr_util_h[part][bank].read(addr);
      `uvm_info(name,$sformatf("addr:%x(%x) data:%x",addr,(addr>>3), rdata), UVM_NONE)
      addr += 8;
    end
  endfunction

  // Cleans up some variables to support multiple sequence runs.
  task otf_clean_up();
    scb_h.alert_count["fatal_err"] = 0;
    scb_h.exp_alert_contd["fatal_err"] = 0;
    scb_h.alert_count["recov_err"] = 0;
    scb_h.exp_alert_contd["recov_err"] = 0;
    scb_h.eflash_addr_phase_queue = '{};

    derr_addr_tbl[ReadTaskCtrl].delete();
    derr_addr_tbl[ReadTaskHost].delete();
    derr_created = '{default: ReadTaskCtrl};
    derr_otd.delete();
    ierr_addr_tbl[ReadTaskCtrl].delete();
    ierr_addr_tbl[ReadTaskHost].delete();
    serr_addr_tbl[ReadTaskCtrl].delete();
    serr_addr_tbl[ReadTaskHost].delete();

    scb_h.ecc_error_addr.delete();
    scb_h.in_error_addr.delete();

    otf_scb_h.stop = 1;
    otf_read_entry.hash.delete();
    foreach (otf_read_entry.prv_read[i]) otf_read_entry.prv_read[i] = '{};
    otf_scb_h.clear_fifos();

    for (int i = 0; i < NumBanks; i++) begin
      otf_scb_h.data_mem[i].delete();
      foreach (otf_scb_h.info_mem[i][j])
        otf_scb_h.info_mem[i][j].delete();
    end
  endtask
endclass
