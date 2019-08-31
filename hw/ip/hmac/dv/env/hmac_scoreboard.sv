// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class hmac_scoreboard extends cip_base_scoreboard #(.CFG_T (hmac_env_cfg),
                                                    .RAL_T (hmac_reg_block),
                                                    .COV_T (hmac_env_cov));
  `uvm_component_utils(hmac_scoreboard)
  `uvm_component_new

  bit [7:0]  msg_q[$];
  bit [63:0] msg_length_bits;
  bit        hmac_start, hmac_process;
  bit        status_msg_fifo_full;

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg csr;
    uvm_mem mem;
    bit     do_read_check = 1'b1;
    bit     write         = item.is_write();

    // for read: grab completed transactions from data channel; ignore packets from addr channel
    // for write: will keep both channels
    if (!write && channel != DataChannel) return;

    // if access was to a valid csr, get the csr handle
    if (item.a_addr inside {cfg.csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(item.a_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end
    if (csr == null) begin
      if (!(item.a_addr inside {[HMAC_MSG_FIFO_BASE : HMAC_MSG_FIFO_LAST_ADDR]})) begin
        // we hit an oob addr - expect error response and return
        `DV_CHECK_EQ(item.d_error, 1'b1)
        return;
      end
    end

    // if incoming access is a write to a valid csr or mem, then update right away on addr channel
    if (write && channel == AddrChannel) begin
      // push the msg into msg_fifo
      if (item.a_addr inside {[HMAC_MSG_FIFO_BASE : HMAC_MSG_FIFO_LAST_ADDR]}) begin
        if (write && channel == AddrChannel && hmac_start) begin
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
          foreach(msg[i]) msg_q.push_back(msg[i]);
        end
      end else begin
        // csr write: predict and update according to the csr names
        csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask));
        case (csr.get_name())
          "msg_length_lower": msg_length_bits[31:0]  = item.a_data;
          "msg_length_upper": msg_length_bits[63:32] = item.a_data;
          "cmd":              {hmac_process, hmac_start} = item.a_data[1:0];
          "cfg", "wipe_secret", "key0", "key1", "key2", "key3", "key4", "key5", "key6", "key7",
          "digest0", "digest1", "digest2", "digest3", "digest4", "digest5", "digest6", "digest7",
          "intr_enable", "intr_test", "intr_state": begin
            // Do nothing
          end
          default: begin
            `uvm_fatal(`gfn, $sformatf("invalid csr: %0s", csr.get_full_name()))
          end
        endcase
      end
      // check if msg all streamed in, could happen during write mem_fifo or trigger hmac_cmd
      if (hmac_process) begin
        predict_digest(msg_q);
        update_wr_msg_length(msg_q.size());
        flush();
      end
    end

    // process the csr req

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (!write) begin
      // TODO: check intr_state
      if (csr.get_name() inside {"intr_state"}) do_read_check = 1'b0;
      if (csr.get_name() == "status") begin
        do_read_check = 1'b0;
        status_msg_fifo_full = item.d_data[HmacStaMsgFifoFull];
      end
      if (do_read_check) begin
        `uvm_info(`gfn, $sformatf("%s reg is checked with expected value %0h",
                                  csr.get_name(), csr.get_mirrored_value()), UVM_HIGH);
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data)
      end
      csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ));
    end
  endtask

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
  endfunction

  // clear variables after expected digest is calculated
  virtual function void flush();
    hmac_start = 1'b0;
    hmac_process = 1'b0;
    msg_q.delete();
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // check all the intr reg are set to 0
    // temp intr checking, will implement a more comprehensive check
    `DV_CHECK_EQ(cfg.intr_vif.pins[HmacMsgFifoFull], 1'b0)
    `DV_CHECK_EQ(cfg.intr_vif.pins[HmacDone], 1'b0)
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
        // sha needs to be enabled?
        exp_digest = '{default:0};
      end
    endcase
    // HW default output Littie Endian for each digest (32 bits)
    // But standard DPI function expect output is in Big Endian
    // So digest_swap = 0 will require flip the expect value
    if (ral.cfg.digest_swap.get_mirrored_value() == 1'b0) begin
      foreach (exp_digest[i]) exp_digest[i] = {<<8{exp_digest[i]}};
    end
    ral.digest0.predict(exp_digest[0]);
    ral.digest1.predict(exp_digest[1]);
    ral.digest2.predict(exp_digest[2]);
    ral.digest3.predict(exp_digest[3]);
    ral.digest4.predict(exp_digest[4]);
    ral.digest5.predict(exp_digest[5]);
    ral.digest6.predict(exp_digest[6]);
    ral.digest7.predict(exp_digest[7]);
  endfunction

  virtual function update_wr_msg_length(int size_bytes);
    uint64 size_bits = size_bytes * 8;
    ral.msg_length_upper.predict(size_bits[63:32]);
    ral.msg_length_lower.predict(size_bits[31:0]);
  endfunction

endclass
