// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_scoreboard #(
  type CFG_T = flash_ctrl_env_cfg
) extends cip_base_scoreboard #(
  .CFG_T(CFG_T),
  .RAL_T(flash_ctrl_core_reg_block),
  .COV_T(flash_ctrl_env_cov)
);
  `uvm_component_param_utils(flash_ctrl_scoreboard#(CFG_T))

  `uvm_component_new

  data_t                                     exp_flash_data  [addr_t]  = '{default: 1};
  data_t                                     exp_flash_info  [addr_t]  = '{default: 1};
  data_t                                     exp_flash_info1 [addr_t]  = '{default: 1};
  data_t                                     exp_flash_redund[addr_t]  = '{default: 1};
  uvm_reg_data_t                             data;
  uvm_reg                                    csr;
  string                                     csr_name;
  flash_dv_part_e                            part                      = FlashPartData;
  addr_t                                     wr_addr;
  addr_t                                     rd_addr;
  int                                        num_wr                    = 0;
  int                                        num_rd                    = 0;
  int                                        idx_wr                    = 0;
  int                                        idx_rd                    = 0;
  bit                                        part_sel                  = 0;
  bit                                  [1:0] info_sel                  = 2'b00;
  bit                                        wr_access                 = 1'b0;
  bit                                        rd_access                 = 1'b0;

  tl_seq_item                                eflash_addr_phase_queue[$];

  // TLM agent fifos
  uvm_tlm_analysis_fifo #(tl_seq_item)       eflash_tl_a_chan_fifo;
  uvm_tlm_analysis_fifo #(tl_seq_item)       eflash_tl_d_chan_fifo;

  // utility function to word-align an input TL address
  function bit [TL_AW-1:0] word_align_addr(bit [TL_AW-1:0] addr);
    return {addr[TL_AW-1:2], 2'b00};
  endfunction

  virtual function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    eflash_tl_a_chan_fifo = new("eflash_tl_a_chan_fifo", this);
    eflash_tl_d_chan_fifo = new("eflash_tl_d_chan_fifo", this);
  endfunction

  virtual function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  virtual task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_eflash_tl_a_chan_fifo();
      process_eflash_tl_d_chan_fifo();
    join_none
  endtask

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

    bit addr_trans_available = 0;

    forever begin
      eflash_tl_d_chan_fifo.get(item);
      if (!cfg.en_scb) continue;
      `uvm_info(`gfn, $sformatf(
                "Received eflash_tl d_chan item:\n%0s", item.sprint(uvm_default_line_printer)),
                UVM_HIGH)
      // check tl packet integrity
      void'(item.is_ok());

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
    flash_read.op         = flash_ctrl_pkg::FlashOpRead;
    flash_read.num_words  = 1;
    flash_read.addr       = trans.a_addr;

    //comparing backdoor read data and direct read data
    cfg.flash_mem_bkdr_read(flash_read, exp_data);
    `DV_CHECK_EQ(exp_data[0], trans.d_data)
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg        csr;
    bit            do_read_check = 1'b1;
    bit            write = item.is_write();
    uvm_reg_addr_t csr_addr = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    bit            addr_phase_read = (!write && channel == AddrChannel);
    bit            addr_phase_write = (write && channel == AddrChannel);
    bit            data_phase_read = (!write && channel == DataChannel);
    bit            data_phase_write = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if ((is_mem_addr(item, ral_name))
         || (csr_addr inside {cfg.ral_models[ral_name].csr_addrs})) begin
      if (cfg.scb_set_exp_alert) begin
        set_exp_alert(.alert_name("recov_err"), .is_fatal(1), .max_delay(cfg.alert_max_delay));
      end
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
          wr_access = 0;
          write_allowed(part, wr_addr);
          `uvm_info(`gfn, $sformatf("wr_access: 0x%0b", wr_access), UVM_LOW)
          if (wr_access) begin
            write_data_all_part(part, wr_addr, item.a_data);
          end
          if (idx_wr == num_wr) begin
            idx_wr = 0;
          end else begin
            idx_wr += 1;
          end
        end else if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
          csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
          `DV_CHECK_NE_FATAL(csr, null)
          void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
          `uvm_info(`gfn, $sformatf("SCB EXP FLASH REG: 0x%0h", csr_addr), UVM_HIGH)
        end
      end

      if (data_phase_read) begin
        if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
          csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
          `DV_CHECK_NE_FATAL(csr, null)
          // process the csr req
          // for write, update local variable and fifo at address phase
          // for read, update predication at address phase and compare at data phase
          case (csr.get_name())
            // add individual case item for each csr
            "intr_state": begin
              // Skip read check on intr_state CSR, since it is WO.
              do_read_check = 1'b0;
            end

            "intr_enable": begin
            end

            "intr_test": begin
            end

            "op_status", "status", "erase_suspend": begin
              // TODO: FIXME
              do_read_check = 1'b0;
            end

            default: begin
              // TODO: uncomment when all CSRs are specified
              // `uvm_fatal(`gfn, $sformatf("CSR access not processed: %0s", csr.get_full_name()))
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
          rd_access = 0;
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

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
    eflash_tl_a_chan_fifo.flush();
    eflash_tl_d_chan_fifo.flush();
  endfunction

  virtual function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, eflash_tl_a_chan_fifo)
    `DV_EOT_PRINT_TLM_FIFO_CONTENTS(tl_seq_item, eflash_tl_d_chan_fifo)
    `DV_CHECK_EQ(eflash_addr_phase_queue.size, 0)
  endfunction

  virtual function flash_dv_part_e calc_part(bit part_sel, bit [1:0] info_sel);
    if (!part_sel) begin
      return FlashPartData;
    end else begin
      case (info_sel)
        2'b00: return FlashPartInfo;
        2'b01: return FlashPartInfo1;
        2'b10: return FlashPartRedundancy;
        default: begin
          `uvm_fatal("flash_ctrl_scoreboard", $sformatf("unknown info part sel 0x%0h", info_sel))
        end
      endcase
    end
  endfunction

  virtual function void write_data_all_part(flash_dv_part_e part, bit [TL_AW-1:0] addr,
                                            ref bit [TL_DW-1:0] data);
    case (part)
      FlashPartData:  exp_flash_data[addr]   = data;
      FlashPartInfo:  exp_flash_info[addr]   = data;
      FlashPartInfo1: exp_flash_info1[addr]  = data;
      //FlashPartRedundancy
      default:        exp_flash_redund[addr] = data;
    endcase
  endfunction

  virtual function void check_rd_data(ref flash_dv_part_e part, bit [TL_AW-1:0] addr,
                                      ref bit [TL_DW-1:0] data);
    case (part)
      FlashPartData: begin
        check_rd_part(exp_flash_data, addr, data);
      end
      FlashPartInfo: begin
        check_rd_part(exp_flash_info, addr, data);
      end
      FlashPartInfo1: begin
        check_rd_part(exp_flash_info1, addr, data);
      end
      // FlashPartRedundancy
      default: begin
        check_rd_part(exp_flash_redund, addr, data);
      end
    endcase
  endfunction

  virtual task write_allowed(ref flash_dv_part_e part, ref bit [TL_AW-1:0] in_addr);
    bit en;
    bit prog_en;
    bit prog_en_def;
    bit [8:0] base;
    bit [9:0] size;
    bit bk_idx;
    int pg_idx;
    bit wr_access_found = 1'b0;

    case (part)
      FlashPartData: begin
        for (int i = 0; i < cfg.seq_cfg.num_en_mp_regions; i++) begin
          if (!wr_access_found) begin
            csr_rd(.ptr(ral.mp_region_cfg_shadowed[i]), .value(data), .backdoor(1'b1));
            en = get_field_val(ral.mp_region_cfg_shadowed[i].en, data);
            prog_en = get_field_val(ral.mp_region_cfg_shadowed[i].prog_en, data);
            base = get_field_val(ral.mp_region_cfg_shadowed[i].base, data);
            size = get_field_val(ral.mp_region_cfg_shadowed[i].size, data);
            if (in_addr inside {[base*BytesPerPage:base*BytesPerPage+size*BytesPerPage]}) begin
              if (en) begin
                wr_access = prog_en;
                wr_access_found = 1'b1;
              end
            end
          end
        end
        if (!wr_access_found) begin
          csr_rd(.ptr(ral.default_region_shadowed), .value(data), .backdoor(1'b1));
          prog_en_def = get_field_val(ral.default_region_shadowed.prog_en, data);
          wr_access = prog_en_def;
          wr_access_found = 1'b1;
        end
      end
      FlashPartInfo: begin
        bk_idx = in_addr[19];
        pg_idx = in_addr[18:11];
        csr_name = $sformatf("bank%0d_info0_page_cfg_shadowed_%0d", bk_idx, pg_idx);
        write_access_info();
      end
      FlashPartInfo1: begin
        bk_idx = in_addr[19];
        csr_name = $sformatf("bank%0d_info1_page_cfg_shadowed", bk_idx);
        write_access_info();
      end
      // FlashPartRedundancy
      default: begin
        bk_idx = in_addr[19];
        pg_idx = in_addr[18:11];
        csr_name = $sformatf("bank%0d_info2_page_cfg_shadowed_%0d", bk_idx, pg_idx);
        write_access_info();
      end
    endcase
  endtask

  virtual task read_allowed(ref flash_dv_part_e part, ref bit [TL_AW-1:0] in_rd_addr);
    bit en;
    bit read_en;
    bit read_en_def;
    bit [8:0] base;
    bit [9:0] size;
    bit bk_idx;
    int pg_idx;
    bit rd_access_found = 1'b0;

    case (part)
      FlashPartData: begin
        for (int i = 0; i < cfg.seq_cfg.num_en_mp_regions; i++) begin
          if (!rd_access_found) begin
            csr_rd(.ptr(ral.mp_region_cfg_shadowed[i]), .value(data), .backdoor(1'b1));
            en = get_field_val(ral.mp_region_cfg_shadowed[i].en, data);
            read_en = get_field_val(ral.mp_region_cfg_shadowed[i].rd_en, data);
            base = get_field_val(ral.mp_region_cfg_shadowed[i].base, data);
            size = get_field_val(ral.mp_region_cfg_shadowed[i].size, data);
            if (in_rd_addr inside {[base*BytesPerPage:base*BytesPerPage+size*BytesPerPage]}) begin
              if (en) begin
                rd_access = read_en;
                rd_access_found = 1'b1;
              end
            end
          end
        end
        if (!rd_access_found) begin
          csr_rd(.ptr(ral.default_region_shadowed), .value(data), .backdoor(1'b1));
          read_en_def = get_field_val(ral.default_region_shadowed.rd_en, data);
          rd_access = read_en_def;
          rd_access_found = 1'b1;
        end
      end
      FlashPartInfo: begin
        bk_idx = in_rd_addr[19];
        pg_idx = in_rd_addr[18:11];
        csr_name = $sformatf("bank%0d_info0_page_cfg_shadowed_%0d", bk_idx, pg_idx);
        read_access_info();
      end
      FlashPartInfo1: begin
        bk_idx = in_rd_addr[19];
        csr_name = $sformatf("bank%0d_info1_page_cfg_shadowed", bk_idx);
        read_access_info();
      end
      // FlashPartRedundancy
      default: begin
        bk_idx = in_rd_addr[19];
        pg_idx = in_rd_addr[18:11];
        csr_name = $sformatf("bank%0d_info2_page_cfg_shadowed_%0d", bk_idx, pg_idx);
        read_access_info();
      end
    endcase

  endtask

  virtual function void check_rd_part(const ref data_t exp_data_part[addr_t],
                                      bit [TL_AW-1:0] addr, ref bit [TL_DW-1:0] data);
    if (exp_data_part.exists(addr)) begin
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
    en = get_field_val(csr.get_field_by_name("en"), data);
    prog_en = get_field_val(csr.get_field_by_name("prog_en"), data);
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
    en = get_field_val(csr.get_field_by_name("en"), data);
    read_en = get_field_val(csr.get_field_by_name("rd_en"), data);
    if (en) begin
      rd_access = read_en;
    end else begin
      rd_access = 0;  //protected
    end
  endtask

endclass
