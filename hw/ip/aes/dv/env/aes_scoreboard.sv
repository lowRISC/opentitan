// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

import aes_model_dpi_pkg::*;
import aes_pkg::*;

class aes_scoreboard extends cip_base_scoreboard #(
  .CFG_T(aes_env_cfg),
  .RAL_T(aes_reg_block),
  .COV_T(aes_env_cov)
  );

  `uvm_component_utils(aes_scoreboard)
  `uvm_component_new

  // local variables
  aes_seq_item input_item;                    // item containing data and config
  aes_seq_item output_item;                   // item containing resulting output
  aes_seq_item complete_item;                 // merge of input and output items
  aes_seq_item key_item;                      // sequence item holding last sideload valid key
  bit          ok_to_fwd          = 0;        // 0: item is not ready to forward
  bit          reset_rebuilding   = 0;        // reset message rebuilding task
  bit          exp_clear          = 0;        // if using sideload - we are expecting a clear
  keymgr_pkg::hw_key_req_t sideload_key = 0;  // will hold the key from sideload
  uvm_tlm_analysis_fifo #(key_sideload_item)  key_manager_fifo;
  bit [3:0]    datain_rdy         = '0;       // indicate if DATA_IN can be updated

  virtual      aes_cov_if   cov_if;           // handle to aes coverage interface
  // local queues to hold incoming packets pending comparison //

  // Items containing both input and output data, ready to be added to a message
  mailbox      #(aes_seq_item)      item_fifo;
  // completed message item ready for scoring
  mailbox      #(aes_message_item)  msg_fifo;
  // once an operation is started the item is put here to wait for the resuting output
  aes_seq_item                      rcv_item_q[$];

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    msg_fifo         = new();
    item_fifo        = new();
    key_manager_fifo = new("keymgr_analysis_fifo");
    input_item       = new("input_item");
    key_item         = new("key_item");
    output_item      = new ();

    if (!uvm_config_db#(virtual aes_cov_if)::get(null, "*.env" , "aes_cov_if", cov_if)) begin
      `uvm_fatal(`gfn, $sformatf("FAILED TO GET HANDLE TO COVER IF"))
    end
  endfunction


  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction


  task run_phase(uvm_phase phase);
    // disable check as we don't
    // know when the alert will happen
    do_alert_check = 0;
    super.run_phase(phase);
    if (cfg.en_scb) begin
      fork
        compare();
        process_sideload_key();
        rebuild_message();
      join_none
    end
  endtask

  function void on_ctrl_shadowed_write(logic [31:0] wdata);
    input_item.manual_op   = get_field_val(ral.ctrl_shadowed.manual_operation, wdata);
    input_item.key_len     = get_field_val(ral.ctrl_shadowed.key_len, wdata);
    input_item.sideload_en = get_field_val(ral.ctrl_shadowed.sideload, wdata);
    `downcast(input_item.operation, get_field_val(ral.ctrl_shadowed.operation, wdata));
    input_item.valid = 1'b1;
    case (get_field_val(ral.ctrl_shadowed.mode, wdata))
      6'b00_0001:  input_item.mode = AES_ECB;
      6'b00_0010:  input_item.mode = AES_CBC;
      6'b00_0100:  input_item.mode = AES_CFB;
      6'b00_1000:  input_item.mode = AES_OFB;
      6'b01_0000:  input_item.mode = AES_CTR;
      6'b10_0000:  input_item.mode = AES_NONE;
      default:     input_item.mode = AES_NONE;
    endcase
    // sample coverage on ctrl register
    cov_if.cg_ctrl_sample(get_field_val(ral.ctrl_shadowed.operation, wdata),
                          get_field_val(ral.ctrl_shadowed.mode, wdata),
                          get_field_val(ral.ctrl_shadowed.key_len, wdata),
                          get_field_val(ral.ctrl_shadowed.manual_operation, wdata),
                          get_field_val(ral.ctrl_shadowed.sideload, wdata),
                          get_field_val(ral.ctrl_shadowed.prng_reseed_rate, wdata));

    input_item.clean();
    input_item.start_item = 1;
    if (input_item.sideload_en) begin
      exp_clear = 1;
    end
  endfunction

  function void on_key_share_write(string csr_name, logic [31:0] wdata);
    for (int share = 0; share < 2; share++) begin
      for (int i = 0; i < 8; i++) begin
        string keyname = $sformatf("key_share%0d_%0d", share, i);
        if (keyname == csr_name) begin
          input_item.key[share][i]     = wdata;
          input_item.key_vld[share][i] = 1'b1;
          cov_if.cg_key_sample(i + 8 * share);
        end
      end
    end
  endfunction

  function void on_data_in_write(string csr_name, logic [31:0] wdata);
    for (int i = 0; i < 4; i++) begin
      string keyname = $sformatf("data_in_%0d", i);
      // you can update datain until all have been
      // updated then DUT will auto start
      if (keyname == csr_name && (|datain_rdy || input_item.manual_op)) begin
        input_item.data_in[i]     = wdata;
        input_item.data_in_vld[i] = 1'b1;
        cov_if.cg_wr_data_sample(i);
        datain_rdy[i] = 0;
      end
    end
  endfunction

  function void on_iv_in_write(string csr_name, logic [31:0] wdata);
    for (int i = 0; i < 4; i++) begin
      string keyname = $sformatf("iv_%0d", i);
      if (keyname == csr_name) begin
        input_item.iv[i]      = wdata;
        input_item.iv_vld[i]  = 1'b1;
        cov_if.cg_iv_sample(i);
      end
    end
  endfunction

  function void on_trigger_write(logic [31:0] wdata);
    //start triggered
    cov_if.cg_trigger_sample(get_field_val(ral.trigger.start, wdata),
                             get_field_val(ral.trigger.key_iv_data_in_clear, wdata),
                             get_field_val(ral.trigger.data_out_clear, wdata),
                             get_field_val(ral.trigger.prng_reseed, wdata));
    `uvm_info(`gfn, $sformatf("\n CLEAR REGISTER SEEN 0x%h", wdata), UVM_MEDIUM)
    if (get_field_val(ral.trigger.start, wdata)) begin
      ok_to_fwd = input_item.mode != AES_NONE;
    end
    // clear key, IV, data_in
    if (get_field_val(ral.trigger.key_iv_data_in_clear, wdata)) begin
      void'(input_item.key_clean(0, 1));
      void'(input_item.iv_clean(0, 1));
      void'(key_item.key_clean(0, 1));
      input_item.clean_data_in();
      datain_rdy = 4'b0;
      // if in the middle of a message
      // this is seen as the beginning of a new message
      if (!input_item.start_item) begin
        input_item.start_item = 1;
        if (!exp_clear) input_item.split_item = 1;
        exp_clear = 0;
        `uvm_info(`gfn, $sformatf("splitting message"), UVM_MEDIUM)
      end
      `uvm_info(`gfn, $sformatf("\n\t ----| clearing KEY"), UVM_MEDIUM)
      `uvm_info(`gfn, $sformatf("\n\t ----| clearing IV"), UVM_MEDIUM)
      `uvm_info(`gfn, $sformatf("\n\t ----| clearing DATA_IN"), UVM_MEDIUM)
    end
    // clear data out
    if (get_field_val(ral.trigger.data_out_clear, wdata)) begin
      `uvm_info(`gfn, $sformatf("\n\t ----| clearing DATA_OUT"), UVM_MEDIUM)
      if (cfg.clear_reg_w_rand) begin
        input_item.data_out = {4{$urandom()}};
      end else begin
        input_item.data_out = '0;
      end
      // marking the output item as potentially bad
      output_item.data_was_cleared = 1;
      // set to make sure any input item
      // waiting for output data is forwarded without the data.
    end
    // reseed
    if (wdata[5]) begin
      // nothing to do for DV
    end
  endfunction

  // Handle a write to a named CSR on the A channel
  function void on_addr_channel_write(string csr_name, logic [31:0] wdata);
    alert_test_t alert_test;
    // add individual case item for each csr
    case (1)
      (!uvm_re_match("alert_test", csr_name)): begin
        alert_test.recov_ctrl_update_err = wdata[0];
        alert_test.fatal_fault = wdata[1];
        cov_if.cg_alert_test_sample(alert_test);
      end

      (!uvm_re_match("ctrl_shadowed", csr_name)): begin
        // ignore reg write if busy
        if (cfg.idle_vif) on_ctrl_shadowed_write(wdata);
      end

      (!uvm_re_match("key_share*", csr_name)): begin
        // ignore reg write if busy
        if (cfg.idle_vif) on_key_share_write(csr_name, wdata);
      end

      (!uvm_re_match("data_in_*", csr_name)): begin
        on_data_in_write(csr_name, wdata);
      end

      (!uvm_re_match("iv_*", csr_name)): begin
        // ignore reg write if busy
        if (cfg.idle_vif) on_iv_in_write(csr_name, wdata);
      end

      (!uvm_re_match("trigger", csr_name)): begin
        on_trigger_write(wdata);
      end

      (!uvm_re_match("ctrl_aux_regwen", csr_name)): begin
        cov_if.cg_aux_regwen_sample(wdata[0]);
      end

      // (!uvm_re_match("status", csr_name)): begin
      //   // not used in scoreboard
      //  end

      default: begin
        // DO nothing- trying to write to a read only register
      end
    endcase
  endfunction

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel, string ral_name);
    uvm_reg        csr;
    aes_seq_item   input_clone;
    aes_seq_item   complete_clone;
    bit            do_read_check = 1'b0;
    bit            write         = item.is_write();
    uvm_reg_addr_t csr_addr      = cfg.ral_models[ral_name].get_word_aligned_addr(item.a_addr);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.ral_models[ral_name].csr_addrs}) begin
      csr = cfg.ral_models[ral_name].default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    if (channel == AddrChannel) begin
      string csr_name = csr.get_name();
      `uvm_info(`gfn, $sformatf("\n\t ----| ITEM received reg name : %s",csr.get_name()), UVM_FULL)

      // if incoming access is a write to a valid csr, then make updates right away
      if (write) begin
        void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
        on_addr_channel_write(csr_name, item.a_data);
      end

      ///////////////////////////////////////
      //             Valid checks          //
      ///////////////////////////////////////

      // check that the item is valid - all registers clean base on mode //
      if (input_item.valid && !input_item.manual_op) begin
        // update key with what came from sideload
        if(input_item.sideload_en && input_item.start_item) begin
          input_item.key = key_item.key;
          input_item.key_vld = key_item.key_vld;
        end
        case (input_item.mode)
          AES_ECB: begin
            `uvm_info(`gfn, $sformatf("\n\t ----| AES Mode: %0s", input_item.mode.name()),
               UVM_MEDIUM)
            if (input_item.start_item) begin
              // Verify that all 4 data_in and all 8 initial key registers have been updated.
              if (input_item.data_in_valid() && input_item.key_clean(0, 0)) begin
                // Clone and add to ref and rec data FIFO.
                ok_to_fwd = 1;
                input_item.start_item = 0;
              end
            end else begin
              // Verify that all 4 data_in and all initial 8 key registers are clean.
              `uvm_info(`gfn, $sformatf("\n\t ----| data_in_vld? %b, key clean? %b",
                  input_item.data_in_valid(), input_item.key_clean(1, 0)), UVM_MEDIUM)
              if (input_item.data_in_valid() && input_item.key_clean(1, 0)) begin
                // Clone and add to ref and rec data FIFO.
                ok_to_fwd = 1;
              end
            end
          end

          AES_CBC,
          AES_CFB,
          AES_OFB,
          AES_CTR: begin
            `uvm_info(`gfn, $sformatf("\n\t ----| AES Mode: %0s", input_item.mode.name()),
                UVM_MEDIUM)
            if (input_item.start_item) begin
              // Verify that all 4 data_in, all 8 initial key, and all 4 IV registers have been
              // updated.
              if (input_item.data_in_valid() && input_item.key_clean(0, 0)
                   && input_item.iv_clean(0, 0)) begin
                // Clone and add to ref and rec data FIFO.
                ok_to_fwd = 1;
                input_item.start_item = 0;
              end
            end else begin
              // Verify that all 4 data_in, all 8 initial key, and all 4 IV registers are clean.
              `uvm_info(`gfn, $sformatf("\n\t ----| data_in_vld? %b, key clean? %b, IV clean? %b",
                  input_item.data_in_valid(), input_item.key_clean(1, 0),
                  input_item.iv_clean(1, 0)), UVM_MEDIUM)
              if (input_item.data_in_valid() && input_item.key_clean(1, 0)
                   && input_item.iv_clean(1, 0)) begin
                // Clone and add to ref and rec data FIFO.
                ok_to_fwd = 1;
              end
            end
          end

          default: begin
            `uvm_info(`gfn, "\n\t ----| Received illegal AES_MODE setting, reverting to AES_NONE",
                UVM_MEDIUM)
          end
        endcase // case (input_item.mode)
      end // if (input_item.valid)

      // forward item to receive side
      if (ok_to_fwd) begin
        ok_to_fwd = 0;
        `downcast(input_clone, input_item.clone());
        `uvm_info(`gfn, $sformatf("\n\t AES INPUT ITEM RECEIVED - \n %s \n\t split message: %0b",
                                   input_clone.convert2string(), input_clone.split_item),
                                  UVM_MEDIUM)
        rcv_item_q.push_front(input_clone);
        input_item.clean();
        // only reset the split here
        // in the case the reset comes after data input
        // having it in clean will reset it when the ctrl
        // is written
        input_item.split_item = 0;
      end
    end

    //////////////////////////////////////////////////////////////////////////////
    // get an item from the rcv queue and wait for all output data to be received
    //////////////////////////////////////////////////////////////////////////////

    `uvm_info(`gfn, $sformatf("\n\t ---| channel  %h", channel), UVM_DEBUG)
    if (!write && channel == DataChannel) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
      `uvm_info(`gfn, $sformatf("\n\t ----| SAW READ - %s data %02h",csr.get_name(),  item.d_data)
                , UVM_MEDIUM)

      case (csr.get_name())
        "data_out_0": begin
          output_item.data_out[0]     = item.d_data;
          output_item.data_out_vld[0] = 1;
          cov_if.cg_rd_data_sample(0);
        end
        "data_out_1": begin
          output_item.data_out[1]     = item.d_data;
          output_item.data_out_vld[1] = 1;
          cov_if.cg_rd_data_sample(1);
        end
        "data_out_2": begin
          output_item.data_out[2]     = item.d_data;
          output_item.data_out_vld[2] = 1;
          cov_if.cg_rd_data_sample(2);
        end
        "data_out_3": begin
          output_item.data_out[3]     = item.d_data;
          output_item.data_out_vld[3] = 1;
          cov_if.cg_rd_data_sample(3);
        end

        "status": begin
          cov_if.cg_status_sample(item.d_data);
          datain_rdy = (get_field_val(ral.status.input_ready, item.d_data) == 1) ? '1 : '0;
          // if dut IDLE and able to accept input
          // and no output is ready
          // there won't be a response for this item
          // reset/clear was triggered
          `uvm_info(`gfn, $sformatf("\n\t ---| Status read: \n\t idle %0b \n\t output lost %0b  ",
                          get_field_val(ral.status.idle, item.d_data),
                          get_field_val(ral.status.output_lost, item.d_data)), UVM_MEDIUM)

          if (get_field_val(ral.status.idle, item.d_data) &&
              get_field_val(ral.status.output_lost, item.d_data)) begin
            if (rcv_item_q.size() != 0) begin
              void'(rcv_item_q.pop_back());
              `uvm_info(`gfn, $sformatf("\n\t ----| removing item from input queue"), UVM_MEDIUM)
            end
          end
        end
      endcase // case (csr.get_name())

      if (output_item.data_out_valid() || output_item.data_was_cleared) begin
        // if data_out is read multipletimes in a row we should not pop input more than once
        if (rcv_item_q.size() == 0) begin
          output_item                    = new();
        end else begin

          complete_item                  = rcv_item_q.pop_back();
          complete_item.data_out         = output_item.data_out;
          complete_item.data_was_cleared = output_item.data_was_cleared;
          // if message was split and data was read out.
          // we will have one more message than expected.
          if (complete_item.split_item) begin
            cfg.split_cnt++;
            `uvm_info(`gfn, $sformatf("\n\t ----| incrementing split count now at: %d",
                      cfg.split_cnt), UVM_MEDIUM)
          end

          `downcast(complete_clone, complete_item.clone());
          item_fifo.put(complete_clone);
          output_item                    = new();
          complete_item                  = new();
        end
      end
    end
  endtask // process_tl_access


  //This task will check for any sideload keys that have been provided
  virtual task process_sideload_key();
    key_sideload_item sideload_item;
    sideload_item = new("sideload_item");

      forever begin
        // Wait for a valid sideloaded key
        key_manager_fifo.get(sideload_item);
        // Note: max size of sideloaded key is keymgr_pkg::KeyWidth

        for (int i = 0; i < keymgr_pkg::KeyWidth / 32; i++) begin
          key_item.key[0][i]     = sideload_item.key0[i*32 +: 32];
          key_item.key[1][i]     = sideload_item.key1[i*32 +: 32];
          key_item.key_vld[0][i] = sideload_item.valid;
          key_item.key_vld[1][i] = sideload_item.valid;
        end
      end
  endtask


  // takes items from the item queue and builds full
  // aes_messages with both input data and output data.
  virtual task rebuild_message();
    typedef enum {
      MSG_IDLE,
      MSG_START,
      MSG_RUN
    } aes_message_stat_t;
    aes_message_stat_t msg_state = MSG_IDLE;
    aes_message_item message, msg_clone;
    aes_seq_item full_item;
    string txt =  "";

    message = new();

    fork
      begin : rebuild_messages
        forever begin
          item_fifo.get(full_item);
          if (msg_state == MSG_IDLE) begin
            // We have just received the very first item after a reset and can now start the regular
            // processing.
            msg_state = MSG_START;
          end
          case (msg_state)
            MSG_START: begin
              if (!full_item.message_start()) begin
                // Check if e.g. the start trigger got fired prematurely and skip this message if
                // needed.
                if (full_item.start_item && full_item.manual_op) begin
                  `uvm_info(`gfn, "setting skip_msg", UVM_MEDIUM)
                  message.skip_msg = 1;
                end else begin
                  `uvm_fatal(`gfn,
                      $sformatf("\n\t ----| FIRST ITEM DID NOT HAVE MESSAGE START/CONFIG SETTINGS"))
                end
              end
              `uvm_info(`gfn, $sformatf("rebuilding %s message, adding start item",
                  full_item.mode.name()), UVM_MEDIUM)
              message.add_start_msg_item(full_item);
              msg_state = MSG_RUN;
            end

            MSG_RUN: begin
              if (full_item.message_start() || (full_item.start_item && full_item.manual_op)) begin
                // The current item marks the start of a new message. End the previous message and
                // add it to the message FIFO for scoring.
                `downcast(msg_clone, message.clone());
                `uvm_info(`gfn, $sformatf("adding %s message item of size %0d to msg_fifo",
                    msg_clone.aes_mode.name(), msg_clone.output_msg.size()), UVM_MEDIUM)
                msg_fifo.put(msg_clone);
                message = new();
                if (full_item.start_item && full_item.manual_op) begin
                  // Skip the message if this is item not really marks the start of a message.
                  if (!full_item.message_start() || !full_item.data_in_valid()) begin
                    `uvm_info(`gfn, $sformatf("setting skip_msg"), UVM_MEDIUM)
                    message.skip_msg = 1;
                  end else begin
                    message.skip_msg = 0;
                  end
                end
                `uvm_info(`gfn, $sformatf("rebuilding %s message, adding start item",
                    full_item.mode.name()), UVM_MEDIUM)
                message.add_start_msg_item(full_item);
              end else begin
                `uvm_info(`gfn, $sformatf("rebuilding %s message, adding data block #%0d",
                    full_item.mode.name(), message.output_msg.size()/16), UVM_MEDIUM)
                message.add_data_item(full_item);
              end
            end
          endcase // case (msg_state)
        end
      end

      begin : finish_last_message
        forever begin
          // AES indicates when it's done with processing individual blocks but not when it's done
          // with processing an entire message. To detect the end of a message, the DV environment
          // does the following:
          // - It tracks writes to the main control register. If two successfull writes to this
          //   shadowed register are observed, this marks the start of a new message.
          // - DV then knows that the last output data retrieved marks the end of the previous
          //   message.
          // This works fine except for the very last message before the sequence ends. To mark the
          // end of the last message, the `finish_message` variable is used. It gets set by the
          // `post_body()` task defined in the base vseq.
          wait (cfg.finish_message)
          `uvm_info(`gfn, $sformatf("finish_message received"), UVM_MEDIUM)
          if (msg_state != MSG_IDLE) begin
            // The message rebuilding thread isn't idle, i.e., there was some activity since the
            // last reset.
            `downcast(msg_clone, message.clone());
            `uvm_info(`gfn, $sformatf("adding %s message item of size %0d to msg_fifo",
                msg_clone.aes_mode.name(), msg_clone.output_msg.size()), UVM_MEDIUM)
            msg_fifo.put(msg_clone);
            // Reset the message rebuilding thread.
            reset_rebuilding = 1;
          end
          // Increment counter for total number of messages seen. If the message rebuilding thread
          // is still idle, no message did actually go through the DUT and we can skip incrementing
          // the counter. The only exception is if all messages were corrupted. The DUT doesn't
          // produce any output in this case.
          if ((msg_state != MSG_IDLE) || (cfg.num_messages == cfg.num_corrupt_messages)) begin
            cfg.num_messages_tot += cfg.num_messages;
          end
          wait_fifo_empty();
          cfg.finish_message = 0;
        end
      end

      begin: reset_rebuild_messages
        forever begin
          wait (reset_rebuilding);
          msg_state = MSG_IDLE;
          message = new();
          reset_rebuilding = 0;
        end
      end
    join
  endtask // rebuild_message


  virtual task compare();
    string txt="";
    bit [3:0][31:0] tmp_input;
    bit [3:0][31:0] tmp_output;
    forever begin
      bit operation;
      aes_message_item msg;
      msg_fifo.get(msg);

      if (msg.aes_mode != AES_NONE && !msg.skip_msg) begin
        msg.alloc_predicted_msg();

        //ref-model     / opration     / chipher mode /    IV   / key_len   / key /data i /data o //
        operation = msg.aes_operation == AES_ENC ? 1'b0 :
                    msg.aes_operation == AES_DEC ? 1'b1 : 1'b0;
        c_dpi_aes_crypt_message(cfg.ref_model, operation, msg.aes_mode, msg.aes_iv,
                                msg.aes_keylen, msg.aes_key[0] ^ msg.aes_key[1],
                                msg.input_msg, msg.predicted_msg);

        `uvm_info(`gfn, $sformatf("\n\t ----| printing MESSAGE %s", msg.convert2string()),
                  UVM_MEDIUM)
        txt = "";

        foreach (msg.input_msg[i]) begin
          txt = { txt, $sformatf("\n\t %d %h \t %h \t %h \t %b",
              i, msg.input_msg[i], msg.output_msg[i], msg.predicted_msg[i], msg.output_cleared[i])};
        end

        for (int n =0 ; n < msg.input_msg.size(); n++) begin
          if ((msg.output_msg[n] != msg.predicted_msg[n]) && ~msg.output_cleared[n]) begin
            txt = {"\t TEST FAILED MESSAGES DID NOT MATCH \n ", txt};

            txt = {txt,
                 $sformatf("\n\n\t ----| ACTUAL OUTPUT DID NOT MATCH PREDICTED OUTPUT |----")};
            txt = {txt,
                 $sformatf("\n\t ----| FAILED AT BYTE #%0d \t ACTUAL: 0x%h \t PREDICTED: 0x%h ",
                                  n, msg.output_msg[n], msg.predicted_msg[n])};
          `uvm_fatal(`gfn, $sformatf(" # %0d  \n\t %s \n", cfg.good_cnt, txt))
          end
        end
        `uvm_info(`gfn,
            $sformatf("\n\t ----|   MESSAGE #%0d MATCHED  %s  |-----",
                cfg.good_cnt, msg.aes_mode.name()), UVM_MEDIUM)
        cfg.good_cnt++;
      end else begin
        if (msg.aes_mode == AES_NONE) begin
          `uvm_info(`gfn,
              $sformatf("\n\t ----| MESSAGE #%0d HAS ILLEGAL MODE MESSAGE IGNORED     |-----",
                  cfg.good_cnt), UVM_MEDIUM)
          cfg.corrupt_cnt++;
        end
        if (msg.skip_msg) begin
          `uvm_info(`gfn,
              $sformatf("\n\t ----| MESSAGE #%0d was skipped due to start triggered prematurely",
                  cfg.good_cnt), UVM_MEDIUM)
          cfg.skipped_cnt++;
        end
      end
    end
  endtask


  virtual function void phase_ready_to_end(uvm_phase phase);
    if (phase.get_name() != "run") return;

    // Don't end the test yet. First, the last message needs to be scored, and all queues and
    // FIFOs need to be emptied.
    phase.raise_objection(this, "need time to finish last item");
    fork begin
      wait_fifo_empty();
      phase.drop_objection(this);
    end
    join_none
  endfunction


  virtual task wait_fifo_empty();
    `uvm_info(`gfn, $sformatf("item fifo entries %d", item_fifo.num()), UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("rcv_queue entries %d", rcv_item_q.size()), UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("msg fifo entries %d", msg_fifo.num()), UVM_MEDIUM)
    wait (rcv_item_q.size() == 0);
    wait (item_fifo.num()   == 0);
    wait (msg_fifo.num()    == 0);
  endtask


  virtual function void reset(string kind = "HARD");
    aes_seq_item     seq_item;
    aes_message_item msg_item;
    super.reset(kind);
    // reset local fifos queues and variables
    rcv_item_q.delete();
    while (item_fifo.try_get(seq_item));
    while (msg_fifo.try_get(msg_item));

    cfg.num_messages_tot = 0;
    cfg.good_cnt = 0;
    cfg.corrupt_cnt = 0;
    cfg.skipped_cnt = 0;
    cfg.split_cnt = 0;
    // if split is set before reset make sure to cancel
    input_item.split_item = 0;
    // reset compare task to start
    reset_rebuilding = 1;
  endfunction


  function string counters2string(string txt);
      txt = { txt, $sformatf("\n\t ----| Expected:           %0d", cfg.num_messages_tot)};
      txt = { txt, $sformatf("\n\t ----| Seen:               %0d", cfg.good_cnt)};
      txt = { txt, $sformatf("\n\t ----| Expected corrupted: %0d", cfg.num_corrupt_messages)};
      txt = { txt, $sformatf("\n\t ----| Seen corrupted:     %0d", cfg.corrupt_cnt)};
      txt = { txt, $sformatf("\n\t ----| Skipped:            %0d", cfg.skipped_cnt)};
      txt = { txt, $sformatf("\n\t ----| Split:              %0d", cfg.split_cnt)};
      return txt;
  endfunction


  function void check_message_counters();
    uvm_report_server rpt_srvr;
    string txt = "";
    // check that we saw all messages
    // if there is more than expected check split count
    if (cfg.good_cnt <
        (cfg.num_messages_tot - cfg.num_corrupt_messages - cfg.skipped_cnt)) begin
      rpt_srvr = uvm_report_server::get_server();
      if (rpt_srvr.get_severity_count(UVM_FATAL)
           + rpt_srvr.get_severity_count(UVM_ERROR) == 0) begin
        txt = "\n\t ----| NO FAILURES BUT NUMBER OF EXPECTED MESSAGES DOES NOT MATCH ACTUAL";
      end else begin
        txt = "\n\t ----| TEST FAILED";
      end
      txt = counters2string(txt);
      `uvm_fatal(`gfn, $sformatf("%s", txt))
    end
    if ((cfg.good_cnt >
        (cfg.num_messages_tot - cfg.num_corrupt_messages - cfg.skipped_cnt))
        && (cfg.split_cnt == 0)) begin
      txt = "\n\t ----| SAW TOO MANY MESSAGES AND NONE WAS SPLIT";
      txt = counters2string(txt);
      `uvm_fatal(`gfn, $sformatf("%s", txt))
    end
  endfunction


  function void check_phase(uvm_phase phase);
    if (cfg.en_scb) begin
      super.check_phase(phase);
      `DV_EOT_PRINT_MAILBOX_CONTENTS(aes_message_item, msg_fifo)
      `DV_EOT_PRINT_MAILBOX_CONTENTS(aes_seq_item, item_fifo)
      `DV_EOT_PRINT_Q_CONTENTS(aes_seq_item, rcv_item_q)
      check_message_counters();
    end
  endfunction


  function void report_phase(uvm_phase phase);
    uvm_report_server rpt_srvr;
    string txt = "";

    super.report_phase(phase);
    txt = "\n\t ----|        TEST FINISHED        |----";
    txt = counters2string(txt);
    rpt_srvr = uvm_report_server::get_server();
    if (rpt_srvr.get_severity_count(UVM_FATAL) + rpt_srvr.get_severity_count(UVM_ERROR) > 0) begin
      `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_LOW)
      txt = {txt, "\n\t ---------------------------------------"};
      txt = {txt, "\n\t ----            TEST FAILED        ----"};
      txt = {txt, "\n\t ---------------------------------------"};
    end else begin
      txt = {txt, "\n\t ---------------------------------------"};
      txt = {txt, "\n\t ----            TEST PASSED        ----"};
      txt = {txt, "\n\t ---------------------------------------"};
    end
    `uvm_info(`gfn, $sformatf("%s", txt), UVM_MEDIUM)

  endfunction // report_phase
endclass
