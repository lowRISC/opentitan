// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Test processes several AES-GCM messages. During each message, at a random
// item, the GCM save and restore feature is tested. Here, before the new item
// is processed, the current state is saved, the registers are cleared, and the
// state is restored. Then, the test continues processing the item.

// scoreboard is disabled for this test
class aes_gcm_save_restore_vseq extends aes_base_vseq;
  `uvm_object_utils(aes_gcm_save_restore_vseq)

  `uvm_object_new
  virtual aes_cov_if cov_if; // handle to aes coverage interface
  aes_message_item   msg;
  bit                rst_set;
  bit                do_b2b = 0;

  task body();
    `uvm_info(`gfn, $sformatf("\n\n\t ----| STARTING AES-GCM SAVE & RESTORE SEQUENCE |----\n %s",
                              cfg.convert2string()), UVM_MEDIUM)

    if (!uvm_config_db#(virtual aes_cov_if)::get(null, "*.env" , "aes_cov_if", cov_if)) begin
      `uvm_fatal(`gfn, $sformatf("FAILED TO GET HANDLE TO COVER IF"))
    end

    fork
      // Start sideload (even if not used).
      start_sideload_seq();
    join_none

    // Generate list of messages.
    generate_message_queue();

    // Process all messages.
    while (message_queue.size() > 0 ) begin
      bit                new_aad = 1;
      bit                new_data = 1;
      int                item_cnt = 1;
      int                save_restore_item;
      int                crypto_res;
      int                aad_len, data_len;
      int                msg_blocks, msg_last_block_len_bytes, msg_block_zero;
      int                aad_blocks, aad_last_block_len_bytes, aad_block_zero;
      bit                operation;
      bit  [3:0][31:0]   predicted_tag;
      bit  [3:0][31:0]   saved_gcm_state, saved_iv;
      aes_seq_item       cfg_item   = new();
      aes_seq_item       cfg_item_restored_iv = new();
      aes_seq_item       data_item  = new();

      `uvm_info(`gfn, $sformatf("Starting New Message - messages left %d",
                                 message_queue.size() ), UVM_MEDIUM)

      msg = message_queue.pop_back();
      aad_len = msg.aad_length;
      data_len = msg.message_length;
      generate_aes_item_queue(msg);

      cfg_item = aes_item_queue.pop_back();
      msg.add_start_msg_item(cfg_item);

      // Wait until the DUT is idle. This is required to start the configuration.
      csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
      // Configure the DUT. Depending on the configuration, this might trigger a PRNG reseed
      // operation.
      csr_spinwait(.ptr(ral.status.idle) , .exp_data(1'b1));
      setup_dut(cfg_item);

      // Wait until the DUT is idle. This is required to provide key and IV.
      csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
      // Provide key, IV and data.
      write_data_key_iv(cfg_item, cfg_item, 1, cfg_item.manual_op, 0, 0, rst_set);
      if (cfg_item.manual_op && !rst_set) trigger();
      if (cfg_item.manual_op && !rst_set) trigger();

      // At which item do we perform the save and restore?
      // Do not perform before we have processed the first item and also when
      // handling the tag.
      save_restore_item = $urandom_range(2, aes_item_queue.size() - 1);

      // Process all items.
      while (aes_item_queue.size() > 0 ) begin
        int valid_bytes;
        // Wait until the DUT is idle.
        csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));

        data_item = aes_item_queue.pop_back();
        `uvm_info(`gfn, $sformatf("\n\t ----AES ITEM %s",
                                   data_item.convert2string()), UVM_MEDIUM)

        if (item_cnt == save_restore_item) begin
          `uvm_info(`gfn, $sformatf("Saving AES-GCM state before processing item %d",
                                    item_cnt), UVM_MEDIUM)
          set_gcm_phase(GCM_SAVE, 16, 0);
          if (cfg_item.manual_op) trigger();
          // Save the current AES-GCM context.
          csr_spinwait(.ptr(ral.status.output_valid), .exp_data(1'b1));
          read_data(saved_gcm_state, do_b2b);
          // Save the current IV.
          csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
          read_iv(saved_iv, do_b2b);
          `downcast(cfg_item_restored_iv, cfg_item.clone());
          cfg_item_restored_iv.iv = saved_iv;
          cfg_item_restored_iv.iv[3] = '0; // Clear upper IV bits to restore the original IV.
          // Clear the AES IV, data in, and data out registers.
          csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
          clear_regs(2'b11);
          csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
          `uvm_info(`gfn, $sformatf("Restoring AES-GCM state before processing item %d",
                                    item_cnt), UVM_MEDIUM)
          // Reconfigure the initial IV and the key.
          write_data_key_iv(cfg_item_restored_iv, data_item, 1, cfg_item.manual_op,
                            0, 0, rst_set);
          if (cfg_item.manual_op) trigger();
          if (cfg_item.manual_op) trigger();

          // Restore the saved AES-GCM context.
          set_gcm_phase(GCM_RESTORE, 16, 1);
          csr_spinwait(.ptr(ral.status.input_ready), .exp_data(1'b1));
          add_data(saved_gcm_state, do_b2b);
          // Restore the saved IV.
          csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
          write_iv(saved_iv, do_b2b);
          if (cfg_item.manual_op) trigger();
          `uvm_info(`gfn, $sformatf("Proceeding with item %d", item_cnt), UVM_MEDIUM)
          csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
          // Enforce setting the GCM phase for the next item.
          new_aad = 1;
          new_data = 1;
        end

        if (data_item.item_type == AES_GCM_AAD) begin
          if (new_aad || data_item.data_len[3:0] != 4'd0) begin
            // Configure AAD phase as this is either the first AAD block or a
            // partial block.
            valid_bytes = data_item.data_len == 0 ? 16 : data_item.data_len;
            set_gcm_phase(GCM_AAD, valid_bytes, 0);
            new_aad = 0;
          end
          csr_spinwait(.ptr(ral.status.input_ready), .exp_data(1'b1));
          add_data(data_item.data_in, do_b2b);
          if (cfg_item.manual_op) trigger();
          // Add AAD to message.
          msg.add_aad_item(data_item);
        end else if (data_item.item_type == AES_DATA) begin
          if (new_data || data_item.data_len[3:0] != 4'd0) begin
            // Configure TEXT phase as this is either the first plaintext block or a
            // partial block.
            valid_bytes = data_item.data_len == 0 ? 16 : data_item.data_len;
            set_gcm_phase(GCM_TEXT, valid_bytes, 0);
            new_aad = 0;
          end
          csr_spinwait(.ptr(ral.status.input_ready), .exp_data(1'b1));
          add_data(data_item.data_in, do_b2b);
          if (cfg_item.manual_op) trigger();
          csr_spinwait(.ptr(ral.status.output_valid), .exp_data(1'b1));
          read_data(data_item.data_out, do_b2b);
          // Add input and output data block to message.
          msg.add_data_item(data_item);
        end else if (data_item.item_type == AES_GCM_TAG) begin
          set_gcm_phase(GCM_TAG, 16, 0);
          csr_spinwait(.ptr(ral.status.input_ready), .exp_data(1'b1));
          add_data(data_item.data_in, do_b2b);
          if (cfg_item.manual_op) trigger();
          csr_spinwait(.ptr(ral.status.output_valid), .exp_data(1'b1));
          read_data(data_item.data_out, do_b2b);
          // Add tag to message.
          msg.add_tag_item(data_item);
        end
        item_cnt++;
      end

      // Check if we got the correct output.
      operation = msg.aes_operation == AES_ENC ? 1'b0 :
                  msg.aes_operation == AES_DEC ? 1'b1 : 1'b0;
      msg.alloc_predicted_msg();
      c_dpi_aes_crypt_message(cfg.ref_model, operation, msg.aes_mode, msg.aes_iv,
                              msg.aes_keylen, msg.aes_key[0] ^ msg.aes_key[1],
                              data_len, aad_len, msg.input_msg,
                              msg.input_aad, msg.output_tag, msg.predicted_msg,
                              predicted_tag, crypto_res);

      // Check the error code of the c_dpi library.
      if (crypto_res < 0) begin
        // The underlying c_dpi cyrpto lib returns an error code < 0 if something
        // is wrong.
        `uvm_fatal(`gfn, "c_dpi crypto lib error detected!\n")
      end

      // Check output data.
      for (int n =0 ; n < data_len; n++) begin
        if ((msg.output_msg[n] != msg.predicted_msg[n]) && ~msg.output_cleared[n]) begin
          `uvm_fatal(`gfn, $sformatf(" output_msg[%d] (0x%x) != predicted_msg[%d] (0x%x) \n",
                     n, msg.output_msg[n], n, msg.predicted_msg[n]))
        end
      end

      // Check tag.
      if (msg.aes_operation == AES_ENC) begin
        `uvm_info(`gfn, $sformatf("DOING TAG CHECK"), UVM_MEDIUM)
        predicted_tag = aes_transpose(predicted_tag);
        foreach(predicted_tag[n]) begin
          if ((predicted_tag[n] != msg.output_tag[n]) && msg.output_tag_vld) begin
            `uvm_fatal(`gfn, $sformatf(" predicted_tag[%d] (0x%x) != output_tag[%d] (0x%x) \n",
                       n, predicted_tag[n], n, msg.output_tag[n]))
          end
        end
      end
      // Sample the covergroup.
      msg_blocks = data_len / 16;
      msg_last_block_len_bytes = data_len % 16;
      msg_block_zero = data_len == 0 ? 1 : 0;
      aad_blocks = aad_len / 16;
      aad_last_block_len_bytes = aad_len % 16;
      aad_block_zero = aad_len == 0 ? 1 : 0;
      cov_if.cg_gcm_len_sample(aad_blocks, aad_last_block_len_bytes, aad_block_zero,
                               msg_blocks, msg_last_block_len_bytes, msg_block_zero,
                               msg.aes_operation);
    end
  endtask : body
endclass
