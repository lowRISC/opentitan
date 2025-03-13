// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
import alert_esc_agent_pkg::*;

class flash_ctrl_scoreboard #(
  type CFG_T = flash_ctrl_env_cfg
) extends cip_base_scoreboard #(
  .CFG_T(CFG_T),
  .RAL_T(flash_ctrl_core_reg_block),
  .COV_T(flash_ctrl_env_cov)
);
  `uvm_component_param_utils(flash_ctrl_scoreboard#(CFG_T))

  `uvm_component_new

  uvm_reg_data_t         data;
  uvm_reg                csr;
  string                 csr_name;
  flash_dv_part_e        part          = FlashPartData;
  addr_t                 wr_addr;
  addr_t                 rd_addr;
  addr_t                 erase_addr;
  bit              [1:0] erase_bank_en;
  int                    num_wr        = 0;
  int                    num_rd        = 0;
  int                    idx_wr        = 0;
  int                    idx_rd        = 0;
  bit                    part_sel      = 0;
  bit              [1:0] info_sel      = 2'b00;
  bit                    wr_access     = 1'b0;
  bit                    rd_access     = 1'b0;
  bit                    erase_access  = 1'b0;
  bit                    erase_sel;
  bit              [1:0] curr_op;
  tl_seq_item            eflash_addr_phase_queue[$];
  int                    num_erase_words;
  int                    exp_alert_contd[string];
  bit                    exp_alert_ff[string][$];
  alert_handshake_e      hs_state;

  // ecc error expected
  bit ecc_error_addr[bit [AddrWidth - 1 : 0]];
  int over_rd_err[addr_t];
  bit exp_tl_rsp_intg_err = 0;

   //host error injection
  bit in_error_addr[bit [AddrWidth - 1 : 0]];

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(tl_seq_item)       eflash_tl_a_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item)       eflash_tl_d_chan_fifo;

  bit skip_read_check = 0;
  bit skip_alert_chk[string];
  // Prevent to execute predict_tl_err during fatal error test
  bit stop_tl_err_chk = 0;
  flash_phy_pkg::rd_buf_t evict_q[NumBanks][$];

  // utility function to word-align an input TL address
  function addr_t word_align_addr(addr_t addr);
    return {addr[TL_AW-1:2], 2'b00};
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    eflash_tl_a_chan_fifo = new("eflash_tl_a_chan_fifo", this);
    eflash_tl_d_chan_fifo = new("eflash_tl_d_chan_fifo", this);
    hs_state = AlertComplete;
    foreach(LIST_OF_ALERTS[i]) skip_alert_chk[i] = 1'b0;
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
    cfg.scb_h = this;
  endfunction

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_eflash_tl_a_chan_fifo();
      process_eflash_tl_d_chan_fifo();
      mon_eviction();
      mon_rma();
    join_none
  endtask

  task mon_rma;
    bit init_set = 0;
    forever begin
      @(negedge cfg.clk_rst_vif.clk);
      if (init_set == 0 && cfg.flash_ctrl_vif.init == 1) begin
        init_set = 1;
        if (cfg.en_cov) cov.rma_init_cg.sample(cfg.flash_ctrl_vif.rma_state);
      end
    end
  endtask // mon_rma

  task mon_eviction;
    flash_mp_region_cfg_t my_region;
    bit ecc_en, scr_en;
    int page;
    forever begin
      @(negedge cfg.clk_rst_vif.clk);
      for (int i = 0; i < NumBanks; i++) begin
        foreach (cfg.flash_ctrl_vif.hazard[i][j]) begin
          if (cfg.flash_ctrl_vif.hazard[i][j]) begin
            otf_addr_t addr = cfg.flash_ctrl_vif.rd_buf[i][j].addr << 3;
            page = cfg.addr2page(addr);
            if (cfg.flash_ctrl_vif.rd_buf[i][j].part == 0) begin // data
              my_region = cfg.get_region(page + 256*i);
            end else begin // info
              my_region =
                cfg.get_region_from_info(
                    cfg.mp_info[i][cfg.flash_ctrl_vif.rd_buf[i][j].info_sel][page]);
            end
            ecc_en = (my_region.ecc_en == MuBi4True);
            scr_en = (my_region.scramble_en == MuBi4True);
            `uvm_info(`gfn, $sformatf(
                      "eviction bank:%0d buffer:%0d addr:0x%x(%x) page:%0d ecc_en:%0d scr_en:%0d",
                      i, j ,cfg.flash_ctrl_vif.rd_buf[i][j].addr, addr, page, ecc_en, scr_en),
                      UVM_MEDIUM)
            if (cfg.en_cov) cov.eviction_cg.sample(j, {cfg.flash_ctrl_vif.evict_prog[i],
                                                       cfg.flash_ctrl_vif.evict_erase[i]},
                                                   {scr_en, ecc_en});
          end
        end
      end
    end
  endtask // mon_eviction

  // Task for receiving addr trans and storing them for later usage
  virtual task process_eflash_tl_a_chan_fifo();
    tl_seq_item item;

    forever begin
      eflash_tl_a_chan_fifo.get(item);
      if (!cfg.en_scb) continue;
      `uvm_info(`gfn, $sformatf(
                "Received eflash_tl a_chan item:\n%0s", item.sprint(uvm_default_line_printer)),
                UVM_HIGH)
      // write the item into the addr queue
      eflash_addr_phase_queue.push_back(item);
      `uvm_info({`gfn, "::process_eflash_tl_a_chan_fifo()"}, $sformatf(
                "Put ADDR_PHASE transaction into eflash_item_q: %0p", item), UVM_HIGH)
    end
  endtask

  // Task for receiving data trans and checking if they matched with address trans
  virtual task process_eflash_tl_d_chan_fifo();
    tl_seq_item item;
    tl_seq_item addr_item;

    forever begin
      eflash_tl_d_chan_fifo.get(item);
      if (!cfg.en_scb) continue;
      `uvm_info(`gfn, $sformatf(
                "Received eflash_tl d_chan item:\n%0s", item.sprint(uvm_default_line_printer)),
                UVM_HIGH)
      // check tl packet integrity
      if (!item.is_ok()) begin
        `uvm_error(`gfn,
                   $sformatf("a_source: 0x%0h & d_source: 0x%0h mismatch",
                             item.a_source, item.d_source))
      end

      // check that address phase for this read is done
      `DV_CHECK_GT_FATAL(eflash_addr_phase_queue.size(), 0)
      addr_item = eflash_addr_phase_queue.pop_front();

      `DV_CHECK_EQ(word_align_addr(item.a_addr), word_align_addr(addr_item.a_addr))
      `DV_CHECK_EQ(item.a_source, addr_item.a_source)
      if (cfg.block_host_rd) begin  // blocking reads are checked with backdoor reads
        check_trans(item);
      end else begin  // non blocking reads are pushed to the queue and in test checked
        cfg.flash_rd_data.push_back(item.d_data);
      end
    end
  endtask

  // the TLUL response data are compared to the backdoor-read data using the bit-mask.
  virtual function void check_trans(ref tl_seq_item trans);
    flash_op_t             flash_read;
    logic      [TL_DW-1:0] exp_data   [$];
    // Flash read trans

    flash_read.partition  = FlashPartData;
    flash_read.erase_type = FlashErasePage;
    flash_read.op         = flash_ctrl_top_specific_pkg::FlashOpRead;
    flash_read.num_words  = 1;
    flash_read.addr       = trans.a_addr;

    //comparing backdoor read data and direct read data
    cfg.flash_mem_bkdr_read(flash_read, exp_data);
    `DV_CHECK_EQ(exp_data[0], trans.d_data)
    // check data with internal memory
    if (cfg.scb_check) begin
      `uvm_info(`gfn, $sformatf("Direct read address 0x%0h data: 0x%0h", trans.a_addr, trans.d_data
                ), UVM_HIGH)
      check_rd_data(flash_read.partition, trans.a_addr, trans.d_data);
      `uvm_info(`gfn, $sformatf("Direct read successfully!!!"), UVM_HIGH)
    end
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg        csr;
    string         csr_wr_name = "";
    bit            do_read_check = 1'b1;
    bit            write = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    bit            addr_phase_read = (!write && channel == AddrChannel);
    bit            addr_phase_write = (write && channel == AddrChannel);
    bit            data_phase_read = (!write && channel == DataChannel);
    bit            data_phase_write = (write && channel == DataChannel);
    bit            erase_req;
    if (skip_read_check) do_read_check = 0;
    // if access was to a valid csr, get the csr handle
    if ((is_mem_addr(
            item, ral_name
        ) || (csr_addr inside {cfg.ral_models[ral_name].csr_addrs})) &&
            !cfg.dir_rd_in_progress) begin

      // if incoming access is a write to a valid csr, then make updates right away.
      if (addr_phase_write) begin
        if (is_mem_addr(item, ral_name) && cfg.scb_check) begin  // prog fifo
          if (idx_wr == 0) begin
            csr_rd(.ptr(ral.addr), .value(data), .backdoor(1'b1));
            wr_addr = word_align_addr(get_field_val(ral.addr.start, data));
            csr_rd(.ptr(ral.control), .value(data), .backdoor(1'b1));
            num_wr = get_field_val(ral.control.num, data);
            part_sel = get_field_val(ral.control.partition_sel, data);
            info_sel = get_field_val(ral.control.info_sel, data);
            part = calc_part(part_sel, info_sel);
            `uvm_info(`gfn, $sformatf("SCB WRITE ADDR: 0x%0h EXP ADDR: 0x%0h", csr_addr, wr_addr),
                      UVM_HIGH)
          end else begin
            wr_addr += 4;
          end
          write_allowed(part, wr_addr);
          `uvm_info(`gfn, $sformatf("wr_access: 0x%0b wr_addr: 0x%0h", wr_access, wr_addr), UVM_LOW)
          if (wr_access) begin
            cfg.write_data_all_part(.part(part), .addr(wr_addr), .data(item.a_data));
          end
          if (idx_wr == num_wr) begin
            idx_wr = 0;
          end else begin
            idx_wr += 1;
          end
        end else if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
          csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
          `DV_CHECK_NE_FATAL(csr, null)
          csr_wr_name = csr.get_name();
          void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
          `uvm_info(`gfn, $sformatf("SCB EXP FLASH REG: 0x%0h", csr_addr), UVM_HIGH)
          if ((csr_wr_name == "control") && cfg.scb_check) begin
            csr_rd(.ptr(ral.control), .value(data), .backdoor(1'b1));
            curr_op = get_field_val(ral.control.op, data);
            if (curr_op == 2) begin  //erase op
              erase_sel = get_field_val(ral.control.erase_sel, data);
              part_sel = get_field_val(ral.control.partition_sel, data);
              info_sel = get_field_val(ral.control.info_sel, data);
              part = calc_part(part_sel, info_sel);
              csr_rd(.ptr(ral.addr), .value(data), .backdoor(1'b1));
              erase_addr = word_align_addr(get_field_val(ral.addr.start, data));
              csr_rd(.ptr(ral.mp_bank_cfg_shadowed[0]), .value(data), .backdoor(1'b1));
              `uvm_info(`gfn, $sformatf("UVM_REG_DATA: 0x%0p", data), UVM_HIGH)
              erase_bank_en = data;
              `uvm_info(
                  `gfn, $sformatf(
                  "erase_sel: 0x%0b part sel: 0x%0b info sel 0x%0d", erase_sel, part_sel, info_sel),
                  UVM_LOW)
              `uvm_info(
                  `gfn, $sformatf(
                  "part: %0s addr: 0x%0h erase_bank_en: 0x%0h", part.name, erase_addr, erase_bank_en
                  ), UVM_LOW)
              erase_allowed(part, erase_sel, erase_addr, erase_bank_en);
              `uvm_info(`gfn, $sformatf(
                        "erase_access: 0x%0b part:%0s erase_addr: 0x%0h",
                        erase_access,
                        part.name,
                        erase_addr
                        ), UVM_LOW)
              if (erase_access) begin
                if (erase_sel) erase_bank(erase_addr[OTFBankId], part_sel);
                else erase_data(part, erase_addr, erase_sel);
              end
            end
          end
          // coverage collection
          case (csr_wr_name)
            "control": begin
              if (skip_read_check == 0) begin
                csr_rd(.ptr(ral.control), .value(data), .backdoor(1'b1));
                curr_op = get_field_val(ral.control.op, data);
                erase_sel = get_field_val(ral.control.erase_sel, data);
                part_sel = get_field_val(ral.control.partition_sel, data);
                info_sel = get_field_val(ral.control.info_sel, data);
                part = calc_part(part_sel, info_sel);
                if (cfg.en_cov) begin
                  flash_op_t     flash_op_cov;
                  flash_op_cov.partition  = part;
                  flash_op_cov.erase_type = flash_erase_e'(erase_sel);
                  flash_op_cov.op = flash_op_e'(curr_op);
                  cov.control_cg.sample(flash_op_cov);
                end
              end
            end
            "erase_suspend": begin
               csr_rd(.ptr(ral.erase_suspend), .value(data), .backdoor(1'b1));
               erase_req = get_field_val(ral.erase_suspend.req, data);
               if (cfg.en_cov) begin
                 cov.erase_susp_cg.sample(erase_req);
               end
            end
            "intr_test": begin
               bit [TL_DW-1:0] intr_en = `gmv(ral.intr_enable);
               bit [NumFlashCtrlIntr-1:0] intr_exp = `gmv(ral.intr_state);
               intr_exp |= item.a_data;
               foreach (intr_exp[i]) begin
                  if (cfg.en_cov) begin
                     cov.intr_test_cg.sample(i, item.a_data[i], intr_en[i], intr_exp[i]);
                  end
               end
            end
            default: begin
               `uvm_info(`gfn, $sformatf("Not for func coverage: %0s",
                                         csr.get_full_name()),UVM_HIGH)
            end
          endcase
        end
      end

      if (data_phase_read) begin
        if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
          csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
          `DV_CHECK_NE_FATAL(csr, null)
          // process the csr req
          // for write, update local variable and fifo at address phase
          // for read, update predication at address phase and compare at data phase
          if(!uvm_re_match("err_code*",csr.get_name())) begin
            if (cfg.en_cov) begin
              cov.sw_error_cg.sample(item.d_data);
            end
          end
          case (csr.get_name())
            // add individual case item for each csr
            "intr_state": begin
              bit [TL_DW-1:0] intr_en = `gmv(ral.intr_enable);
              bit [NumFlashCtrlIntr-1:0] intr_exp = `gmv(ral.intr_state);
              csr_rd(.ptr(ral.curr_fifo_lvl), .value(data), .backdoor(1'b1));
              if (cfg.en_cov) begin
                foreach (intr_exp[i]) begin
                  flash_ctrl_intr_e intr = flash_ctrl_intr_e'(i);
                  cov.intr_cg.sample(i, intr_en[i], item.d_data[i]);
                  cov.intr_pins_cg.sample(i, cfg.intr_vif.pins[i]);
                end
                cov.msgfifo_level_cg.sample(data[4:0], data[12:8],
                                            cfg.intr_vif.pins[FlashCtrlIntrProgLvl],
                                            cfg.intr_vif.pins[FlashCtrlIntrRdLvl]);
              end
              // Skip read check on intr_state CSR, since it is WO.
              do_read_check = 1'b0;
            end

            "op_status", "status", "erase_suspend", "curr_fifo_lvl", "debug_state",
            "ecc_single_err_cnt", "ecc_single_err_addr_0", "ecc_single_err_addr_1",
            "std_fault_status": begin
              do_read_check = 1'b0;
            end
            "err_code", "fault_status": begin
              do_read_check = 1'b0;
            end
            default: begin
              // Do nothing.
              // This is place holder for default csr test.
            end
          endcase
          // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
          if (do_read_check) begin
            `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data, $sformatf(
                         "reg name: %0s", csr.get_full_name()))
          end
          void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
        end else if (is_mem_addr(item, ral_name) && cfg.scb_check) begin  // rd fifo
          if (idx_rd == 0) begin
            csr_rd(.ptr(ral.addr), .value(data), .backdoor(1'b1));
            rd_addr = word_align_addr(get_field_val(ral.addr.start, data));
            csr_rd(.ptr(ral.control), .value(data), .backdoor(1'b1));
            num_rd = get_field_val(ral.control.num, data);
            part_sel = get_field_val(ral.control.partition_sel, data);
            info_sel = get_field_val(ral.control.info_sel, data);
            part = calc_part(part_sel, info_sel);
            `uvm_info(`gfn, $sformatf("SCB READ ADDR: 0x%0h EXP ADDR: 0x%0h", csr_addr, rd_addr),
                      UVM_HIGH)
          end else begin
            rd_addr += 4;
          end
          read_allowed(part, rd_addr);
          `uvm_info(`gfn, $sformatf("rd_access: 0x%0b", rd_access), UVM_LOW)
          if (rd_access) begin
            check_rd_data(part, rd_addr, item.d_data);
          end
          if (idx_rd == num_rd) begin
            idx_rd = 0;
          end else begin
            idx_rd += 1;
          end
        end
      end
    end
  endtask

  // Update scb_flash_* with bank erase command.
  // If data partition is selected, erase data partition only,
  // otherwise all partitions in the bank will be erased.
  virtual function void erase_bank(int bank, bit part_sel);
    uint partition_words_num;
    data_model_t scb_flash_model;
    flash_mem_addr_attrs addr_attr;
    flash_dv_part_e part = part.first();
    do begin
      partition_words_num = cfg.get_partition_words_num(part);
      scb_flash_model = cfg.get_partition_mem_model(part);
      addr_attr = new();
      addr_attr.set_attrs(bank * BytesPerBank);
      if (part_sel == 1 || part == FlashPartData) begin
        for (int j = 0; j < partition_words_num; j++) begin
          scb_flash_model[addr_attr.addr] = ALL_ONES;
          addr_attr.incr(flash_ctrl_top_specific_pkg::BusBytes);
        end
        case (part)
          FlashPartData: cfg.scb_flash_data = scb_flash_model;
          FlashPartInfo: cfg.scb_flash_info = scb_flash_model;
          FlashPartInfo1: cfg.scb_flash_info1 = scb_flash_model;
          FlashPartInfo2: cfg.scb_flash_info2 = scb_flash_model;
          default: `uvm_fatal(`gfn, "flash_ctrl_scoreboard: Partition type not supported!")
        endcase
      end
      part = part.next();
    end while (part != part.first());

  endfunction

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    foreach(cfg.list_of_alerts[i]) begin
      exp_alert_contd[i] = 0;
    end
    // reset local fifos queues and variables
    eflash_tl_a_chan_fifo.flush();
    eflash_tl_d_chan_fifo.flush();
    cfg.scb_flash_data.delete();
    cfg.scb_flash_info.delete();
    cfg.scb_flash_info1.delete();
    cfg.scb_flash_info2.delete();
  endfunction

  virtual function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, eflash_tl_a_chan_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, eflash_tl_d_chan_fifo)
    if (cfg.en_scb) begin
      `DV_CHECK_EQ(eflash_addr_phase_queue.size, 0)
    end
    if (cfg.scb_check && cfg.check_full_scb_mem_model) begin
      cfg.check_mem_model();
    end

    `DV_CHECK_EQ(cfg.tlul_core_obs_cnt, cfg.tlul_core_exp_cnt,
                 "core_tlul_error_cnt mismatch")
  endfunction

  virtual function flash_dv_part_e calc_part(bit part_sel, bit [1:0] info_sel);
    if (!part_sel) begin
      return FlashPartData;
    end else begin
      case (info_sel)
        2'b00: return FlashPartInfo;
        2'b01: return FlashPartInfo1;
        2'b10: return FlashPartInfo2;
        default: begin
          `uvm_fatal("flash_ctrl_scoreboard", $sformatf("unknown info part sel 0x%0h", info_sel))
        end
      endcase
    end
  endfunction

  virtual function void check_rd_data(flash_dv_part_e part, addr_t addr,
                                      ref data_t data);
    case (part)
      FlashPartData: begin
        check_rd_part(cfg.scb_flash_data, addr, data);
      end
      FlashPartInfo: begin
        check_rd_part(cfg.scb_flash_info, addr, data);
      end
      FlashPartInfo1: begin
        check_rd_part(cfg.scb_flash_info1, addr, data);
      end
      FlashPartInfo2: begin
        check_rd_part(cfg.scb_flash_info2, addr, data);
      end
      default: `uvm_fatal(`gfn, "flash_ctrl_scoreboard: Partition type not supported!")
    endcase
  endfunction

  // In opensource, `sel` is always 0.
  // When `sel` is 1, which indicates bank erase,
  // task `erase_bank` is called.
  virtual function void erase_data(flash_dv_part_e part, addr_t addr, bit sel);
    case (part)
      FlashPartData: begin
        erase_page_bank(NUM_BK_DATA_WORDS, addr, sel, cfg.scb_flash_data, "scb_flash_data");
      end
      FlashPartInfo: begin
        if (sel) begin
          erase_page_bank(NUM_BK_DATA_WORDS, addr, sel, cfg.scb_flash_data, "scb_flash_data");
        end
        erase_page_bank(NUM_BK_INFO_WORDS, addr, sel, cfg.scb_flash_info, "scb_flash_info");
      end
      FlashPartInfo1: begin
        if (!sel) begin
          erase_page_bank(NUM_PAGE_WORDS, addr, sel, cfg.scb_flash_info1, "scb_flash_info1");
        end else begin
          `uvm_fatal(`gfn, "flash_ctrl_scoreboard: Bank erase for INFO1 part not supported!")
        end
      end
      FlashPartInfo2: begin
        if (!sel) begin
          erase_page_bank(NUM_PAGE_WORDS, addr, sel, cfg.scb_flash_info2, "scb_flash_info2");
        end else begin
          `uvm_fatal(`gfn, "flash_ctrl_scoreboard: Bank erase for INFO2 part not supported!")
        end
      end
      default: `uvm_fatal(`gfn, "flash_ctrl_scoreboard: Partition type not supported!")
    endcase

  endfunction

  virtual task write_allowed(ref flash_dv_part_e part, ref addr_t in_addr);
    bit en;
    bit prog_en;
    bit prog_en_def;
    bit [8:0] base;
    bit [9:0] size;
    bit bk_idx;
    int pg_idx;
    bit wr_access_found;

    wr_access_found = 1'b0;
    wr_access       = 1'b0;
    case (part)
      FlashPartData: begin
        for (int i = 0; i < cfg.seq_cfg.num_en_mp_regions; i++) begin
          if (!wr_access_found) begin
            csr_rd(.ptr(ral.mp_region_cfg[i]), .value(data), .backdoor(1'b1));
            en = mubi4_test_true_strict(mubi4_t'(
                     get_field_val(ral.mp_region_cfg[i].en, data)));
            prog_en = mubi4_test_true_strict(mubi4_t'(
                          get_field_val(ral.mp_region_cfg[i].prog_en, data)));
            csr_rd(.ptr(ral.mp_region[i]), .value(data), .backdoor(1'b1));
            base = get_field_val(ral.mp_region[i].base, data);
            size = get_field_val(ral.mp_region[i].size, data);
            if (in_addr inside {[base*BytesPerPage:base*BytesPerPage+size*BytesPerPage]}) begin
              if (en) begin
                wr_access = prog_en;
                wr_access_found = 1'b1;
              end
            end
          end
        end
        if (!wr_access_found) begin
          csr_rd(.ptr(ral.default_region), .value(data), .backdoor(1'b1));
          prog_en_def = mubi4_test_true_strict(mubi4_t'(
                            get_field_val(ral.default_region.prog_en, data)));
          wr_access = prog_en_def;
          wr_access_found = 1'b1;
        end
      end
      FlashPartInfo: begin
        bk_idx   = in_addr[19];
        pg_idx   = in_addr[18:11];
        csr_name = $sformatf("bank%0d_info0_page_cfg_%0d", bk_idx, pg_idx);
        write_access_info();
      end
      FlashPartInfo1: begin
        bk_idx   = in_addr[19];
        csr_name = $sformatf("bank%0d_info1_page_cfg", bk_idx);
        write_access_info();
      end
      FlashPartInfo2: begin
        bk_idx   = in_addr[19];
        pg_idx   = in_addr[18:11];
        csr_name = $sformatf("bank%0d_info2_page_cfg_%0d", bk_idx, pg_idx);
        write_access_info();
      end
      default: `uvm_fatal(`gfn, "flash_ctrl_scoreboard: Partition type not supported!")
    endcase
  endtask

  virtual task read_allowed(ref flash_dv_part_e part, ref addr_t in_rd_addr);
    bit en;
    bit read_en;
    bit read_en_def;
    bit [8:0] base;
    bit [9:0] size;
    bit bk_idx;
    int pg_idx;
    bit rd_access_found;

    rd_access_found = 1'b0;
    rd_access       = 1'b0;
    case (part)
      FlashPartData: begin
        for (int i = 0; i < cfg.seq_cfg.num_en_mp_regions; i++) begin
          if (!rd_access_found) begin
            csr_rd(.ptr(ral.mp_region_cfg[i]), .value(data), .backdoor(1'b1));
            en = mubi4_test_true_strict(mubi4_t'(
                     get_field_val(ral.mp_region_cfg[i].en, data)));
            read_en = mubi4_test_true_strict(mubi4_t'(
                          get_field_val(ral.mp_region_cfg[i].rd_en, data)));
            csr_rd(.ptr(ral.mp_region[i]), .value(data), .backdoor(1'b1));
            base = get_field_val(ral.mp_region[i].base, data);
            size = get_field_val(ral.mp_region[i].size, data);
            if (in_rd_addr inside {[base*BytesPerPage:base*BytesPerPage+size*BytesPerPage]}) begin
              if (en) begin
                rd_access_found = 1'b1;
              end
            end
          end
        end
        if (!rd_access_found) begin
          csr_rd(.ptr(ral.default_region), .value(data), .backdoor(1'b1));
          read_en_def = mubi4_test_true_strict(mubi4_t'(
                            get_field_val(ral.default_region.rd_en, data)));
          rd_access = read_en_def;
          rd_access_found = 1'b1;
        end
      end
      FlashPartInfo: begin
        bk_idx   = in_rd_addr[19];
        pg_idx   = in_rd_addr[18:11];
        csr_name = $sformatf("bank%0d_info0_page_cfg_%0d", bk_idx, pg_idx);
        read_access_info();
      end
      FlashPartInfo1: begin
        bk_idx   = in_rd_addr[19];
        csr_name = $sformatf("bank%0d_info1_page_cfg", bk_idx);
        read_access_info();
      end
      FlashPartInfo2: begin
        bk_idx   = in_rd_addr[19];
        pg_idx   = in_rd_addr[18:11];
        csr_name = $sformatf("bank%0d_info2_page_cfg_%0d", bk_idx, pg_idx);
        read_access_info();
      end
      default: `uvm_fatal(`gfn, "flash_ctrl_scoreboard: Partition type not supported!")
    endcase
  endtask

  virtual task erase_allowed(ref flash_dv_part_e part, bit erase_sel,
                             ref addr_t in_erase_addr, bit [1:0] bk_en);
    bit en;
    bit erase_en;
    bit erase_en_def;
    bit [8:0] base;
    bit [9:0] size;
    bit bk_idx;
    int pg_idx;
    bit erase_access_found;

    erase_access_found = 1'b0;
    erase_access       = 1'b0;
    if (!erase_sel) begin  // page erase
      case (part)
        FlashPartData: begin
          for (int i = 0; i < cfg.seq_cfg.num_en_mp_regions; i++) begin
            if (!erase_access_found) begin
              csr_rd(.ptr(ral.mp_region_cfg[i]), .value(data), .backdoor(1'b1));
              en = mubi4_test_true_strict(mubi4_t'(get_field_val(ral.mp_region_cfg[i].en, data)));
              erase_en = mubi4_test_true_strict(mubi4_t'(
                         get_field_val(ral.mp_region_cfg[i].erase_en, data)));
              csr_rd(.ptr(ral.mp_region[i]), .value(data), .backdoor(1'b1));
              base = get_field_val(ral.mp_region[i].base, data);
              size = get_field_val(ral.mp_region[i].size, data);
              if (in_erase_addr
                  inside {[base*BytesPerPage:base*BytesPerPage+size*BytesPerPage-1]}) begin
                if (en) begin
                  erase_access       = erase_en;
                  erase_access_found = 1'b1;
                end
              end
            end
          end
          if (!erase_access_found) begin
            csr_rd(.ptr(ral.default_region), .value(data), .backdoor(1'b1));
            erase_en_def = mubi4_test_true_strict(mubi4_t'(
                           get_field_val(ral.default_region.erase_en, data)));
            erase_access       = erase_en_def;
            erase_access_found = 1'b1;
          end
        end
        FlashPartInfo: begin
          bk_idx   = in_erase_addr[19];
          pg_idx   = in_erase_addr[18:11];
          csr_name = $sformatf("bank%0d_info0_page_cfg_%0d", bk_idx, pg_idx);
          erase_access_info();
        end
        FlashPartInfo1: begin
          bk_idx   = in_erase_addr[19];
          csr_name = $sformatf("bank%0d_info1_page_cfg", bk_idx);
          erase_access_info();
        end
        FlashPartInfo2: begin
          bk_idx   = in_erase_addr[19];
          pg_idx   = in_erase_addr[18:11];
          csr_name = $sformatf("bank%0d_info2_page_cfg_%0d", bk_idx, pg_idx);
          erase_access_info();
        end
        default: `uvm_fatal(`gfn, "flash_ctrl_scoreboard: Partition type not supported!")
      endcase
    end else begin  // bank erase
      bk_idx = in_erase_addr[19];
      erase_access = bk_en[bk_idx];
      `uvm_info(`gfn, $sformatf("erase_access bank: 0x%0b", erase_access), UVM_LOW)
    end
  endtask

  virtual function void check_rd_part(const ref data_model_t exp_data_part,
                                      addr_t addr, ref data_t data);
    if (exp_data_part.exists(addr)) begin
      `uvm_info(
          `gfn, $sformatf(
          "addr: 0x%0h scb data: 0x%0h data 0: 0x%0h", addr, exp_data_part[addr], exp_data_part[0]),
          UVM_HIGH)
      `DV_CHECK_EQ(exp_data_part[addr], data, $sformatf("read addr:0x%0h data: 0x%0h", addr, data))
    end else begin
      `uvm_info(`gfn, $sformatf("addr %0h is not written!", addr), UVM_MEDIUM)
    end
  endfunction

  virtual task write_access_info();
    bit en;
    bit prog_en;

    csr = ral.get_reg_by_name(csr_name);
    csr_rd(.ptr(csr), .value(data), .backdoor(1'b1));
    en = mubi4_test_true_strict(mubi4_t'(
             get_field_val(csr.get_field_by_name("en"), data)));
    prog_en = mubi4_test_true_strict(mubi4_t'(
                  get_field_val(csr.get_field_by_name("prog_en"), data)));
    if (en) begin
      wr_access = prog_en;
    end else begin
      wr_access = 0;  //protected
    end
  endtask

  virtual task read_access_info();
    bit en;
    bit read_en;

    csr = ral.get_reg_by_name(csr_name);
    csr_rd(.ptr(csr), .value(data), .backdoor(1'b1));
    en = mubi4_test_true_strict(mubi4_t'(
             get_field_val(csr.get_field_by_name("en"), data)));
    read_en = mubi4_test_true_strict(mubi4_t'(
                  get_field_val(csr.get_field_by_name("rd_en"), data)));
    if (en) begin
      rd_access = read_en;
    end else begin
      rd_access = 0;  //protected
    end
  endtask

  virtual task erase_access_info();
    bit en;
    bit erase_en;

    csr = ral.get_reg_by_name(csr_name);
    csr_rd(.ptr(csr), .value(data), .backdoor(1'b1));
    en = mubi4_test_true_strict(mubi4_t'(
             get_field_val(csr.get_field_by_name("en"), data)));
    erase_en = mubi4_test_true_strict(mubi4_t'(
             get_field_val(csr.get_field_by_name("erase_en"),data)));
    if (en) begin
      erase_access = erase_en;
    end else begin
      erase_access = 0;  //protected
    end
  endtask

  virtual function void erase_page_bank(int num_bk_words, addr_t addr, bit sel,
                                        ref data_model_t exp_part,
                                        input string scb_mem_name);
    int num_wr;
    if (sel) begin  // bank sel
      num_wr = num_bk_words;
      `uvm_info(`gfn, $sformatf("num_wr: %0d", num_wr), UVM_LOW)
      if (addr[19]) begin  // bank 1
        addr = BytesPerBank;
      end else begin  // bank 0
        addr = 0;
      end
    end else begin  // page sel
      num_wr = NUM_PAGE_WORDS;
      addr   = {addr[19:11], {11{1'b0}}};
    end
    for (int i = 0; i < num_wr; i++) begin
      if (exp_part.exists(addr)) begin
        exp_part[addr] = {TL_DW{1'b1}};
        `uvm_info(`gfn, $sformatf("ERASE ADDR:0x%0h %s: 0x%0h", addr, scb_mem_name, exp_part[addr]),
                  UVM_LOW)
      end
      addr = addr + 4;
    end
  endfunction

  // Overriden function from cip_base_scoreboard, to handle TL/UL Error seen on Hardware Interface
  // when using Code Access Restrictions (EXEC)
  virtual function bit predict_tl_err(tl_seq_item item, tl_channels_e channel, string ral_name);
    bit   ecc_err, in_err;

    // Skip this routine when fatal error event is asserted
    if (stop_tl_err_chk) return 1;

    // For flash, address has to be 8byte aligned.
    ecc_err = ecc_error_addr.exists({item.a_addr[AddrWidth-1:3],3'b0});
    in_err = in_error_addr.exists({item.a_addr[AddrWidth-1:3],3'b0});
    `uvm_info("predict_tl_err_dbg",
              $sformatf({"addr:0x%x(%x) ecc_err:%0d in_err:%0d channel:%s ral_name:%s",
                         " tlul_exp_cnt:%0d"},
                        {item.a_addr[AddrWidth-1:3],3'b0},
                        item.a_addr, ecc_err, in_err,
                        channel.name, ral_name,
                        cfg.tlul_core_exp_cnt
                        ), UVM_HIGH)

    if (over_rd_err.exists(item.a_addr)) begin
      if (channel == DataChannel)  begin
        over_rd_err[item.a_addr]--;
        if (over_rd_err[item.a_addr] == 0) over_rd_err.delete(item.a_addr);
        `uvm_info(`gfn, $sformatf("addr is clear 0x%x", item.a_addr), UVM_HIGH)
      end
      return 1;
    end

    if (ral_name == cfg.flash_ral_name) begin
      if (get_flash_instr_type_err(item, channel)) return (1);
      if (cfg.tlul_eflash_exp_cnt > 0 && item.d_error == 1) begin
        cfg.tlul_eflash_obs_cnt++;
        return 1;
      end
    end else begin
      if (cfg.tlul_core_exp_cnt > 0 && item.d_error == 1) begin
        cfg.tlul_core_obs_cnt++;
        return 1;
      end
    end

    if (ecc_err | in_err) begin
      if (channel == DataChannel) begin
        `DV_CHECK_EQ(item.d_error, 1,
                     $sformatf("On interface %s, TL item: %s, ecc_err:%0d in_err:%0d",
                               ral_name, item.sprint(uvm_default_line_printer),
                               ecc_err, in_err))
        return 1;
      end
    end

    if (exp_tl_rsp_intg_err == 1 && channel == DataChannel) begin
      return (!item.is_d_chan_intg_ok(.throw_error(0)));
    end

    if (ral_name == cfg.flash_ral_name && channel == DataChannel) begin
      bit has_error = cfg.address_has_some_injected_error({item.a_addr[TL_AW-1:3],3'h0},
                                                          FlashPartData);
      if (has_error) begin
        `uvm_info(`gfn, $sformatf("A double ecc or integrity error for addr:0x%x", item.a_addr),
                  UVM_MEDIUM)
        return 1;
      end
    end
    return (super.predict_tl_err(item, channel, ral_name));
  endfunction : predict_tl_err

  // Check if the input tl_seq_item has any tl errors.
  virtual function bit get_flash_instr_type_err(tl_seq_item item, tl_channels_e channel);
    bit is_exec_key = `gmv(ral.exec) == CODE_EXEC_KEY;
    // Local Variable
    tlul_pkg::tl_a_user_t a_user = item.a_user;
    if (cfg.en_cov) begin
      if (channel == AddrChannel) begin
        cov.fetch_code_cg.sample(is_exec_key, a_user.instr_type);
      end
    end

    // If Data Access, or a Write, or the CODE_EXEC_KEY Matches
    if (((a_user.instr_type == MuBi4False) || (item.a_opcode != tlul_pkg::Get)) ||
         (`gmv(ral.exec) == CODE_EXEC_KEY)) return(0);  // No Error Predicted

    // Error is Predicted,  Expect an Error if Channel==DataChannel
    if (channel == DataChannel) begin
      `uvm_info(`gfn, "TL Error Expected", UVM_HIGH)
      `DV_CHECK_EQ(item.d_error, 1)
    end
    return (1);  // Error Predicted

  endfunction : get_flash_instr_type_err

  function void process_alert(string alert_name, alert_esc_seq_item item);
    bit pop_out;
    if (!(alert_name inside {cfg.list_of_alerts})) begin
      `uvm_fatal(`gfn, $sformatf("alert_name %0s is not in cfg.list_of_alerts!", alert_name))
    end
    hs_state = item.alert_handshake_sta;

    `uvm_info(`gfn, $sformatf("alert %0s detected, alert_status is %s exp:%0d contd:%0d",
                              alert_name,
                              item.alert_handshake_sta,
                              expected_alert[alert_name].expected,
                              exp_alert_contd[alert_name]
                              ), UVM_MEDIUM)
    if (item.alert_handshake_sta == AlertReceived) begin
      under_alert_handshake[alert_name] = 1;
      if (exp_alert_ff[alert_name].size > 0) expected_alert[alert_name].expected = 1;
      on_alert(alert_name, item);
      alert_count[alert_name]++;
    end else begin
      if (!cfg.under_reset && under_alert_handshake[alert_name] == 0) begin
        `uvm_error(`gfn, $sformatf("alert %0s is not received!", alert_name))
      end
      pop_out = exp_alert_ff[alert_name].pop_front();
      if (exp_alert_ff[alert_name].size() == 0) expected_alert[alert_name].expected = 0;
      under_alert_handshake[alert_name] = 0;
      if (exp_alert_contd[alert_name] > 0) begin
        expected_alert[alert_name].expected = 1;
        exp_alert_contd[alert_name]--;
      end
    end
  endfunction

  virtual function void on_alert(string alert_name, alert_esc_seq_item item);
    if(!skip_alert_chk[alert_name]) begin
      super.on_alert(alert_name, item);
    end
  endfunction

endclass : flash_ctrl_scoreboard
