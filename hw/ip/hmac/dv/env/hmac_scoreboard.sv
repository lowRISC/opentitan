// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class hmac_scoreboard extends cip_base_scoreboard #(.CFG_T (hmac_env_cfg),
                                                    .RAL_T (hmac_reg_block),
                                                    .COV_T (hmac_env_cov));
  `uvm_component_utils(hmac_scoreboard)
  `uvm_component_new

  bit       sha_en;
  bit [7:0] msg_q[$];
  bit       hmac_start, hmac_process;
  bit       fifo_full;
  int       hmac_wr_cnt;
  int       hmac_rd_cnt;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    hmac_process_fifo_rd();
    hmac_process_fifo_full();
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg csr;
    bit     do_read_check           = 1'b1;
    bit     do_cycle_accurate_check = 1'b1;
    bit     write                   = item.is_write();
    uvm_reg_addr_t csr_addr         = get_normalized_addr(item.a_addr);

    super.process_tl_access(item, channel);
    if (is_tl_err_exp || is_tl_unmapped_addr) return;

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    // if addr inside msg fifo, no ral model
    end else if (!(item.a_addr inside {[HMAC_MSG_FIFO_BASE : HMAC_MSG_FIFO_LAST_ADDR]})) begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // if incoming access is a write to a valid csr or mem, then update right away on addr channel
    if (write && channel == AddrChannel) begin
      // push the msg into msg_fifo
      if (item.a_addr inside {[HMAC_MSG_FIFO_BASE : HMAC_MSG_FIFO_LAST_ADDR]}) begin
        if (!sha_en) begin
          void'(ral.intr_state.hmac_err.predict(.value(1), .kind(UVM_PREDICT_DIRECT)));
          void'(ral.err_code.predict(.value(SwPushMsgWhenShaDisabled), .kind(UVM_PREDICT_DIRECT)));
        end else if (hmac_start) begin
          bit [7:0] bytes[4];
          bit [7:0] msg[];
          {<<byte{bytes}} = item.a_data;
          // do endian swap in the word according to the mask, then push to the queue of msgs
          foreach (item.a_mask[i]) begin
            if (item.a_mask[i]) begin
              // The DUT by default (endian_swap bit set to 0) operates at big endian data
              msg = (ral.cfg.endian_swap.get_mirrored_value()) ? {bytes[i], msg} : {msg, bytes[i]};
            end
          end
          foreach (msg[i])  begin
            msg_q.push_back(msg[i]);
            if (msg_q.size() % 4 == 0) begin
              wait(cfg.d2h_a_ready_vif.pins == 1); // wait for outstanding transaction
              incr_wr_and_check_fifo_full();
            end
          end
        end
      end else begin
        // csr write: predict and update according to the csr names
        void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
        case (csr.get_name())
          "cmd": begin
            if (sha_en) begin
              {hmac_process, hmac_start} = item.a_data[1:0];
              if (hmac_process) begin
                // check if msg all streamed in, could happen during wr msg or trigger process
                predict_digest(msg_q);
                update_wr_msg_length(msg_q.size());
                // any bytes left after hmac_process will be added to the wr_cnt
                if (msg_q.size() % 4 != 0) incr_wr_and_check_fifo_full();
                msg_q.delete();
              end
            end else if (item.a_data[HashStart] == 1) begin
              void'(ral.intr_state.hmac_err.predict(.value(1), .kind(UVM_PREDICT_DIRECT)));
              void'(ral.err_code.predict(.value(SwHashStartWhenShaDisabled),
                                         .kind(UVM_PREDICT_DIRECT)));
            end
          end
          "intr_test": begin // testmode, intr_state is W1C, cannot use UVM_PREDICT_WRITE
            bit [TL_DW-1:0] intr_state_exp = item.a_data | ral.intr_state.get_mirrored_value();
            void'(ral.intr_state.predict(.value(intr_state_exp), .kind(UVM_PREDICT_DIRECT)));
          end
          "cfg": begin
            if (cfg.en_cov) cov.cfg_cg.sample(item.a_data);
            sha_en = item.a_data[ShaEn];
            if (!sha_en) predict_digest(msg_q);
          end
          "wipe_secret", "key0", "key1", "key2", "key3", "key4", "key5", "key6", "key7",
          "intr_enable", "intr_state": begin
            // Do nothing
          end
          "digest0", "digest1", "digest2", "digest3", "digest4", "digest5", "digest6", "digest7",
          "status", "msg_length_lower", "msg_length_upper": begin
            `uvm_error(`gfn, $sformatf("this reg does not have write access: %0s",
                                       csr.get_full_name()))
          end
          default: begin
            `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
          end
        endcase
      end
    end

    // predict status based on csr read addr channel
    if (!write && channel != DataChannel) begin
        if (csr.get_name() == "status") begin
          bit [4:0]       hmac_fifo_depth  = hmac_wr_cnt - hmac_rd_cnt;
          bit             hmac_fifo_full   = hmac_fifo_depth == HMAC_MSG_FIFO_DEPTH;
          bit             hmac_fifo_empty  = hmac_fifo_depth == 0;
          bit [TL_DW-1:0] hmac_status_data = (hmac_fifo_empty << HmacStaMsgFifoEmpty) |
                                             (hmac_fifo_full << HmacStaMsgFifoFull) |
                                             (hmac_fifo_depth << HmacStaMsgFifoDepth);
          void'(ral.status.predict(.value(hmac_status_data), .kind(UVM_PREDICT_READ)));
        end
      return;
    end

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (!write) begin
      case (csr.get_name())
        "intr_state": begin
          if (!do_cycle_accurate_check) do_read_check = 0;
          if (cfg.en_cov) begin
            hmac_intr_e intr;
            intr = intr.first;
            do begin
              bit [TL_DW-1:0] intr_en = ral.intr_enable.get_mirrored_value();
              cov.intr_cg.sample(intr, intr_en[intr], item.d_data[intr]);
              cov.intr_pins_cg.sample(intr, cfg.intr_vif.pins[intr]);
              intr = intr.next;
            end while (intr != intr.first);
          end
          if (item.d_data[HmacDone] == 1) begin
            hmac_wr_cnt = 0;
            hmac_rd_cnt = 0;
            // here sanity check DUT should only trigger hmac_done when sha is enabled, and
            // previously triggered hash_process.
            // future throughput test should check the accurate cycles
            if (sha_en && hmac_process) begin
              void'(ral.intr_state.hmac_done.predict(.value(1), .kind(UVM_PREDICT_READ)));
              hmac_process = 0;
            end
          end
        end
        "digest0", "digest1", "digest2", "digest3", "digest4", "digest5", "digest6", "digest7":
        begin
          // HW default output Littie Endian for each digest (32 bits)
          // But standard DPI function expect output is in Big Endian
          // So digest_swap = 0 will require flip the expect value
          if (ral.cfg.digest_swap.get_mirrored_value() == 1'b0) begin
            bit [TL_AW-1:0] digest_data = {<<8{csr.get_mirrored_value()}};
            `DV_CHECK_EQ(item.d_data, digest_data);
            // do not want to update mirror value here, directly return
            return;
          end
        end
        "status": begin
          if (!do_cycle_accurate_check) do_read_check = 0;
          if (cfg.en_cov) cov.status_cg.sample(item.d_data, ral.cfg.get_mirrored_value());
        end
        "msg_length_lower": begin
          if (cfg.en_cov) begin
            cov.msg_len_cg.sample(item.d_data, ral.cfg.get_mirrored_value());
          end
        end
        "key0", "key1", "key2", "key3", "key4", "key5", "key6", "key7", "cfg", "cmd", "err_code",
        "intr_enable", "intr_test", "wipe_secret", "msg_length_upper": begin
          // Do nothing
        end
        default: begin
          `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
        end
      endcase
      if (do_read_check) begin
        `uvm_info(`gfn, $sformatf("%s reg is checked with expected value %0h",
                                  csr.get_name(), csr.get_mirrored_value()), UVM_HIGH);
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data, csr.get_name())
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    flush();
    sha_en      = 0;
    hmac_wr_cnt = 0;
    hmac_rd_cnt = 0;
  endfunction

  // clear variables after expected digest is calculated
  virtual function void flush();
    hmac_start = 1'b0;
    hmac_process = 1'b0;
    msg_q.delete();
  endfunction

  virtual task incr_wr_and_check_fifo_full();
    if (sha_en) begin
      // if fifo full, tlul will not write next data until fifo has space again
      if (fifo_full) begin
        wait (hmac_wr_cnt - hmac_rd_cnt < HMAC_MSG_FIFO_DEPTH)
        fifo_full = 0;
      end
      @(negedge cfg.clk_rst_vif.clk);
      hmac_wr_cnt++;
      `uvm_info(`gfn, $sformatf("increase wr cnt %0d", hmac_wr_cnt), UVM_HIGH)
    end
  endtask

  virtual task hmac_process_fifo_full();
    forever @(hmac_wr_cnt, hmac_rd_cnt) begin
      // when hmac_wr_cnt and hmac_rd_cnt update at the same time, wait 1ps to guarantee
      // get both update
      #1ps;
      if ((hmac_wr_cnt - hmac_rd_cnt) == HMAC_MSG_FIFO_DEPTH) begin
        void'(ral.intr_state.fifo_full.predict(1));
        `uvm_info(`gfn, "predict interrupt fifo full is set", UVM_HIGH)
        fifo_full = 1;
      end
    end
  endtask

  // internal msg_fifo model to check fifo status and interrupt.
  // monitor rd_cnt and wr_cnt on the negedge of the clk
  // rd_cnt followed by wr_cnt with a clk cycle delay, except:
  // 1). hmac process key: DUT will process the key first
  // 2). read cnt reaches FIFO_MAX: DUT will process msg in the FIFO
  virtual task hmac_process_fifo_rd();
    bit key_processed;
    fork
      begin : process_hmac_key_pad
        forever begin
          wait(cfg.clk_rst_vif.rst_n === 1 && sha_en === 1);
          fork
            begin : key_padding
              wait(hmac_start);
              if (ral.cfg.hmac_en.get_mirrored_value() && hmac_rd_cnt == 0) begin
                // 80 cycles for hmac key padding, 1 cycle for hash_start reg to reset
                cfg.clk_rst_vif.wait_clks(HMAC_KEY_PROCESS_CYCLES + 1);
                @(negedge cfg.clk_rst_vif.clk);
                key_processed = 1;
              end
              while (1) begin
                if (ral.intr_state.hmac_done.get_mirrored_value() == 1) break;
                cfg.clk_rst_vif.wait_clks(1);
              end
            end
            begin : reset_key_padding
              wait(!cfg.clk_rst_vif.rst_n);
            end
          join_any
          disable fork;
          key_processed = 0;
        end // end forever
      end

      begin : process_internal_fifo_rd
        forever begin
          wait(cfg.clk_rst_vif.rst_n === 1 && sha_en === 1);
          fork
            begin : hmac_fifo_rd
              wait(hmac_wr_cnt > hmac_rd_cnt);
              if (ral.cfg.hmac_en.get_mirrored_value() && hmac_rd_cnt == 0) begin
                wait(key_processed);
              end
              #1; // delay 1 ns to make sure did not sample right at negedge clk
              cfg.clk_rst_vif.wait_n_clks(1);
              hmac_rd_cnt++;
              `uvm_info(`gfn, $sformatf("increase rd cnt %0d", hmac_rd_cnt), UVM_HIGH)
              if (hmac_rd_cnt % HMAC_MSG_FIFO_DEPTH == 0) begin
                cfg.clk_rst_vif.wait_n_clks(HMAC_MSG_PROCESS_CYCLES);
              end
            end
            begin : reset_hmac_fifo_rd
              wait(!cfg.clk_rst_vif.rst_n);
            end
          join_any
          disable fork;
        end // end forever
      end
    join_none
  endtask

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    `DV_CHECK_EQ(cfg.intr_vif.pins[HmacMsgFifoFull], 1'b0)
    `DV_CHECK_EQ(cfg.intr_vif.pins[HmacDone], 1'b0)
    `DV_CHECK_EQ(cfg.intr_vif.pins[HmacErr], 1'b0)
  endfunction

  // query the sha / hmac c model to get expected digest
  // update predicted digest to ral mirrored value
  virtual function void predict_digest(bit [7:0] msg_q[]);
    int unsigned exp_digest[8];
    bit          hmac_en = ral.cfg.hmac_en.get_mirrored_value();
    bit          sha_en  = ral.cfg.sha_en.get_mirrored_value();
    case ({hmac_en, sha_en})
      2'b11: begin
        bit [31:0] key[8];
        key[0] = ral.key0.get_mirrored_value();
        key[1] = ral.key1.get_mirrored_value();
        key[2] = ral.key2.get_mirrored_value();
        key[3] = ral.key3.get_mirrored_value();
        key[4] = ral.key4.get_mirrored_value();
        key[5] = ral.key5.get_mirrored_value();
        key[6] = ral.key6.get_mirrored_value();
        key[7] = ral.key7.get_mirrored_value();
        cryptoc_dpi_pkg::get_hmac_sha256(key, msg_q, exp_digest);
      end
      2'b01: begin
        cryptoc_dpi_pkg::get_sha256_digest(msg_q, exp_digest);
      end
      default: begin
        // disgest is cleared if sha_en = 0
        exp_digest = '{default:0};
      end
    endcase
    void'(ral.digest0.predict(exp_digest[0]));
    void'(ral.digest1.predict(exp_digest[1]));
    void'(ral.digest2.predict(exp_digest[2]));
    void'(ral.digest3.predict(exp_digest[3]));
    void'(ral.digest4.predict(exp_digest[4]));
    void'(ral.digest5.predict(exp_digest[5]));
    void'(ral.digest6.predict(exp_digest[6]));
    void'(ral.digest7.predict(exp_digest[7]));
  endfunction

  virtual function void update_wr_msg_length(int size_bytes);
    uint64 size_bits = size_bytes * 8;
    void'(ral.msg_length_upper.predict(size_bits[TL_DW*2-1:TL_DW]));
    void'(ral.msg_length_lower.predict(size_bits[TL_DW-1:0]));
  endfunction

endclass
