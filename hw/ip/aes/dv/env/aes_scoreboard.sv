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

  bit          ok_to_fwd          = 0;        // 0: item is not ready to forward
  bit          finish_message     = 0;        // set when test is trying to end
                                              // - to indicate the last message is finished
  int          good_cnt           = 0;        // number of good messages
  int          corrupt_cnt        = 0;        // number of aes_mode errors seen
  int          skipped_cnt        = 0;        // number of skipped messages

  // local queues to hold incoming packets pending comparison //

  // Items containing both input and output data, ready to be added to a message
  mailbox      #(aes_seq_item)      item_fifo;
  // completed message item ready for scoring
  mailbox      #(aes_message_item)  msg_fifo;
  // once an operation is started the item is put here to wait for the resuting output
  aes_seq_item                      rcv_item_q[$];


  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    msg_fifo    = new();
    item_fifo   = new();
    input_item  = new("input_item");
    output_item = new ();
  endfunction


  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction


  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    if (cfg.en_scb) begin
      fork
        compare();
        rebuild_message();
      join_none
    end
  endtask


  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg        csr;
    string         csr_name;
    aes_seq_item   input_clone;
    aes_seq_item   complete_clone;
    bit            do_read_check = 1'b0;
    bit            write         = item.is_write();
    uvm_reg_addr_t csr_addr      = ral.get_word_aligned_addr(item.a_addr);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    if (channel == AddrChannel) begin
      // if incoming access is a write to a valid csr, then make updates right away
      if (write) begin
        void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
      end
      `uvm_info(`gfn, $sformatf("\n\t ----| ITEM received reg name : %s",csr.get_name() ), UVM_FULL)
      csr_name = csr.get_name();
      case (1)
        // add individual case item for each csr
        (!uvm_re_match("ctrl_shadowed", csr_name)): begin
          input_item.manual_op = item.a_data[10];
          input_item.key_len   = item.a_data[9:7];
          `downcast(input_item.operation, item.a_data[0]);
          input_item.valid = 1'b1;
          case (item.a_data[6:1])
            6'b00_0001:  input_item.mode = AES_ECB;
            6'b00_0010:  input_item.mode = AES_CBC;
            6'b00_0100:  input_item.mode = AES_CFB;
            6'b00_1000:  input_item.mode = AES_OFB;
            6'b01_0000:  input_item.mode = AES_CTR;
            6'b10_0000:  input_item.mode = AES_NONE;
            default:     input_item.mode = AES_NONE;
          endcase // case item.a_data[4:1]
          input_item.clean();
          input_item.start_item = 1;

        end

        (!uvm_re_match("key_share0*", csr_name)): begin
          for (int i = 0; i < 8; i++) begin
            string keyname = $sformatf("key_share0_%0d", i);
            if (keyname == csr_name) begin
               input_item.key[0][i]     = item.a_data;
               input_item.key_vld[0][i] = 1'b1;
            end
          end
        end

        (!uvm_re_match("key_share1*", csr_name)): begin
          for (int i = 0; i < 8; i++) begin
            string keyname = $sformatf("key_share1_%0d", i);
            if (keyname == csr_name) begin
               input_item.key[1][i]     = item.a_data;
               input_item.key_vld[1][i] = 1'b1;
            end
          end
        end

        (!uvm_re_match("data_in_*", csr_name)): begin
          for (int i = 0; i < 4; i++) begin
            string keyname = $sformatf("data_in_%0d", i);
            if (keyname == csr_name) begin
              input_item.data_in[i]      = item.a_data;
              input_item.data_in_vld[i]  = 1'b1;
            end
          end
        end

       (!uvm_re_match("iv_*", csr_name)): begin
          for (int i = 0; i < 4; i++) begin
            string keyname = $sformatf("iv_%0d", i);
            if (keyname == csr_name) begin
              input_item.iv[i]      = item.a_data;
              input_item.iv_vld[i]  = 1'b1;
            end
          end
       end

      (!uvm_re_match("trigger", csr_name)): begin
        //start triggered
        `uvm_info(`gfn, $sformatf("\n CLEAR REGISTER SEEN 0x%h", item.a_data), UVM_MEDIUM)
        if (get_field_val(ral.trigger.start, item.a_data)) begin
          ok_to_fwd                = 1;
        end
        // clear key, IV, data_in
        if (get_field_val(ral.trigger.key_iv_data_in_clear, item.a_data)) begin
          void'(input_item.key_clean(0, 1));
          void'(input_item.iv_clean(0, 1));
          input_item.clean_data_in();
          // if in the middle of a message
          // this is seen as the beginning of a new message
          if (!input_item.start_item) begin
            input_item.start_item = 1;
            `uvm_info(`gfn, $sformatf("splitting message"), UVM_MEDIUM)
          end
          `uvm_info(`gfn, $sformatf("\n\t ----clearing KEY"), UVM_MEDIUM)
          `uvm_info(`gfn, $sformatf("\n\t ----| clearing IV"), UVM_MEDIUM)
          `uvm_info(`gfn, $sformatf("\n\t ----| clearing DATA_IN"), UVM_MEDIUM)
        end
        // clear data out
        if (get_field_val(ral.trigger.data_out_clear, item.a_data)) begin
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
         if (item.a_data[5]) begin
           // nothing to do for DV
        end
       end

      // "status": begin
      //   //TBD
      // end

       default: begin
         // DO nothing- trying to write to a read only register
       end
     endcase


      ///////////////////////////////////////
      //             Valid checks          //
      ///////////////////////////////////////

      // check that the item is valid - all registers clean base on mode //
      if (input_item.valid && !input_item.manual_op) begin
        case (input_item.mode)
          AES_ECB: begin
            `uvm_info(`gfn, $sformatf("\n\t ----| ECB mode"), UVM_FULL)
            if (input_item.start_item) begin
              // verify that all 4 data_in and all 8 key have been updated
              if (input_item.data_in_valid() && input_item.key_clean(0,0)) begin
                //clone and add to ref and rec data fifo
                ok_to_fwd    = 1;
                input_item.start_item = 0;
              end
            end else begin
              // verify that all 4 data_in and all 8 key are clean
              `uvm_info(`gfn, $sformatf("\n\t ----|data_inv_vld?  %b, key clean ? %b",
                        input_item.data_in_valid(), input_item.key_clean(1,0)), UVM_MEDIUM)

              if (input_item.data_in_valid() && input_item.key_clean(1,0)) begin
                //clone and add to ref and rec data fifo
                ok_to_fwd = 1;
              end
            end
          end

          AES_CBC: begin
            `uvm_info(`gfn, $sformatf("\n\t ----| CBC mode"), UVM_FULL)
            if (input_item.start_item) begin
              // verify that all 4 data_in and all 8 key and all 4 IV have been updated
              if (input_item.data_in_valid() && input_item.key_clean(0,0) && input_item.iv_clean(0,0)) begin
                //clone and add to ref and rec data fifo
                ok_to_fwd    = 1;
                input_item.start_item = 0;
              end
            end else begin
              // verify that all 4 data_in and all 8 key  and all 4 IV are clean
              `uvm_info(`gfn, $sformatf("\n\t ----|data_inv_vld?  %b, key clean ? %b",
                                input_item.data_in_valid(), input_item.key_clean(1,0)), UVM_MEDIUM)

              if (input_item.data_in_valid() && input_item.key_clean(1,0) && input_item.iv_clean(1,0)) begin
                //clone and add to ref and rec data fifo
                ok_to_fwd = 1;
              end
            end
          end

          AES_CFB: begin
            if (input_item.start_item) begin
              // verify that all 4 data_in and all 8 key and all 4 IV have been updated
              if (input_item.data_in_valid() && input_item.key_clean(0,0) && input_item.iv_clean(0,0)) begin
                //clone and add to ref and rec data fifo
                ok_to_fwd    = 1;
                input_item.start_item = 0;
              end
            end else begin
              // verify that all 4 data_in and all 8 key  and all 4 IV are clean
              if (input_item.data_in_valid() && input_item.key_clean(1,0) && input_item.iv_clean(1,0)) begin
                //clone and add to ref and rec data fifo
                ok_to_fwd = 1;
              end
            end
          end

          AES_OFB: begin
            if (input_item.start_item) begin
              // verify that all 4 data_in and all 8 key and all 4 IV have been updated
              if (input_item.data_in_valid() && input_item.key_clean(0,0) && input_item.iv_clean(0,0)) begin
                //clone and add to ref and rec data fifo
                ok_to_fwd    = 1;
                input_item.start_item = 0;
              end
            end else begin
              // verify that all 4 data_in and all 8 key  and all 4 IV are clean
              `uvm_info(`gfn, $sformatf("\n\t ----|data_inv_vld?  %b, key clean ? %b",
                                input_item.data_in_valid(), input_item.key_clean(1,0)), UVM_HIGH)

              if (input_item.data_in_valid() && input_item.key_clean(1,0) && input_item.iv_clean(1,0)) begin
                //clone and add to ref and rec data fifo
                ok_to_fwd = 1;
              end
            end
          end

          AES_CTR: begin
            `uvm_info(`gfn, $sformatf("\n\t ----| CTR mode"), UVM_FULL)
            if (input_item.start_item) begin
              // verify that all 4 data_in and all 8 key and all 4 IV have been updated
              if (input_item.data_in_valid() && input_item.key_clean(0,0) && input_item.iv_clean(0,0)) begin
                //clone and add to ref and rec data fifo
                ok_to_fwd    = 1;
                input_item.start_item = 0;
              end
            end else begin
              // verify that all 4 data_in and all 8 and all 4 IV  key are clean
              `uvm_info(`gfn, $sformatf("\n\t ----|data_inv_vld?  %b, key clean ? %b",input_item.data_in_valid(), input_item.key_clean(1,0)),
                                       UVM_MEDIUM)
              if (input_item.data_in_valid() && input_item.key_clean(1,0) && input_item.iv_clean(1,0)) begin
                //clone and add to ref and rec data fifo
                ok_to_fwd = 1;
              end
            end
          end
          default: begin
            `uvm_info(`gfn, $sformatf("\n\t ----| Received illegal AES_MODE setting reverting to AES_NONE "),
                                      UVM_HIGH)
          end
        endcase // case (input_item.mode)
      end // if (input_item.valid)

      // forward item to receive side
      if (ok_to_fwd) begin
        ok_to_fwd = 0;
        `downcast(input_clone, input_item.clone());
        `uvm_info(`gfn, $sformatf("\n\t AES INPUT ITEM RECEIVED - \n %s", input_clone.convert2string()),
                                  UVM_MEDIUM)
        rcv_item_q.push_front(input_clone);
        input_item.clean();
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
                , UVM_FULL)

      case (csr.get_name())
        "data_out_0": begin
          output_item.data_out[0]     = item.d_data;
          output_item.data_out_vld[0] = 1;
        end
        "data_out_1": begin
          output_item.data_out[1]     = item.d_data;
          output_item.data_out_vld[1] = 1;
        end
        "data_out_2": begin
          output_item.data_out[2]     = item.d_data;
          output_item.data_out_vld[2] = 1;
        end
        "data_out_3": begin
          output_item.data_out[3]     = item.d_data;
          output_item.data_out_vld[3] = 1;
        end
        "status": begin
          // if dut IDLE and able to accept input
          // and no output is ready
          // there won't be a response for this item
          // reset/clear was triggered
          if (get_field_val(ral.status.idle, item.d_data) &&
              get_field_val(ral.status.output_lost, item.d_data)) begin
            if (rcv_item_q.size() != 0) begin
              void'(rcv_item_q.pop_back());
              `uvm_info(`gfn, $sformatf("\n\t ----| removing item from input queue"), UVM_MEDIUM)
            end
          end
        end
      endcase // case (csr.get_name())

      if (output_item.data_out_valid()) begin
        // if data_out is read multipletimes in a row we should not pop input more than once
        if (rcv_item_q.size() == 0) begin
          output_item                    = new();
        end else begin

          complete_item                  = rcv_item_q.pop_back();
          complete_item.data_out         = output_item.data_out;
          complete_item.data_was_cleared = output_item.data_was_cleared;

          `downcast(complete_clone, complete_item.clone());
          item_fifo.put(complete_clone);

          `uvm_info(`gfn,
                    $sformatf("\n\t ----|added data to item_fifo mode %0b (output received) fifo entries %d",
                              complete_item.mode, item_fifo.num()), UVM_MEDIUM)

          output_item                    = new();
          complete_item                  = new();
        end
      end
    end
  endtask // process_tl_access


  // takes items from the item queue and builds full
  // aes_messages with both input data and output data.
  task rebuild_message();
    typedef enum { MSG_START,MSG_RUN } aes_message_stat_t;

    aes_message_item   message, msg_clone;
    aes_seq_item       full_item;
    aes_message_stat_t msg_state;

    message = new();

    fork
      begin
        forever begin
          case (msg_state)
            MSG_START: begin
              item_fifo.get(full_item);
              `uvm_info(`gfn, $sformatf("\n\t ----| got item from item fifo"), UVM_MEDIUM)
              if (!full_item.message_start()) begin
                // check if start trigger was fired prematurely
                if (full_item.start_item && full_item.manual_op) begin
                  message.skip_msg = 1;
                  `uvm_info(`gfn, $sformatf("\n setting skip msg"), UVM_MEDIUM)
                end else begin
                  `uvm_fatal(`gfn,
                   $sformatf("\n\t ----| FIRST ITEM DID NOT HAVE MESSAGE START/CONFIG SETTINGS"))
                end
              end
              message.add_start_msg_item(full_item);
              msg_state = MSG_RUN;
            end

            MSG_RUN: begin
              item_fifo.get(full_item);
              `uvm_info(`gfn, $sformatf("\n\t ----| got item from item fifo "), UVM_MEDIUM)
              if (full_item.message_start() || (full_item.start_item && full_item.manual_op)) begin
                `downcast(msg_clone, message.clone());
                msg_fifo.put(msg_clone);
                message = new();
                if (full_item.start_item && full_item.manual_op) begin
                   message.skip_msg = 1;
                  `uvm_info(`gfn, $sformatf("\n setting skip msg"), UVM_MEDIUM)
                end
                message.add_start_msg_item(full_item);
              end else begin
                message.add_data_item(full_item);
              end
            end
          endcase // case (msg_state)
        end
      end

      begin
        wait (finish_message)
        `uvm_info(`gfn, $sformatf("\n\t ----| Finish test received adding message item to mg_fifo"),
                                  UVM_MEDIUM)

        `downcast(msg_clone, message.clone());
        msg_fifo.put(msg_clone);
      end
    join_any
  endtask // rebuild_message


  virtual task compare();
    string txt="";
    bit [3:0][31:0] tmp_input;
    bit [3:0][31:0] tmp_output;

    forever begin
      aes_message_item msg;
      msg_fifo.get(msg);
      `uvm_info(`gfn, $sformatf("model %b, operation: %b, mode %06b, IV %h, key_len %03b, key share0 %h, key share1 %h ",
                                cfg.ref_model, msg.aes_operation, msg.aes_mode, msg.aes_iv, msg.aes_keylen,
                                msg.aes_key[0], msg.aes_key[1]),
                                UVM_MEDIUM)

      if (msg.aes_mode != AES_NONE && !msg.skip_msg) begin
        msg.alloc_predicted_msg();

        //ref-model      / opration     / chipher mode /    IV   / key_len    / key /data i /data o //
        c_dpi_aes_crypt_message(cfg.ref_model, msg.aes_operation, msg.aes_mode, msg.aes_iv,
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

            txt = {txt, $sformatf("\n\n\t ----| ACTUAL OUTPUT DID NOT MATCH PREDICTED OUTPUT |----")};
            txt = {txt, $sformatf("\n\t ----| FAILED AT BYTE #%0d \t ACTUAL: 0x%h \t PREDICTED: 0x%h ",
                                  n, msg.output_msg[n], msg.predicted_msg[n])};
          `uvm_fatal(`gfn, $sformatf(" # %0d  \n\t %s \n", good_cnt, txt))
          end
        end
        `uvm_info(`gfn, $sformatf("\n\t ----|   MESSAGE #%0d MATCHED    |-----", good_cnt),
                                  UVM_MEDIUM)
        good_cnt++;
      end else begin
        if (msg.aes_mode == AES_NONE) begin
          `uvm_info(`gfn, $sformatf("\n\t ----| MESSAGE #%0d HAS ILLEGAL MODE MESSAGE IGNORED     |-----", good_cnt),
                                   UVM_MEDIUM)
          corrupt_cnt++;
        end
        if (msg.skip_msg) begin
          `uvm_info(`gfn, $sformatf("\n\t ----| MESSAGE #%0d was skipped due to start triggered prematurely", good_cnt),
                                    UVM_MEDIUM)
          skipped_cnt++;
        end
      end
    end
  endtask

  // TODO get rid of this and do EOP checks in monitor
  virtual function void phase_ready_to_end(uvm_phase phase);
    if (phase.get_name() != "run") return;

    // the message currently being reassembled is should be sent for scoring
    finish_message = 1;
    `uvm_info(`gfn, $sformatf("Finish message: %b", finish_message), UVM_MEDIUM)

    // AES needs this objection - because PHASE READY TO END
    // is the only way to know that the very last message is now complete
    phase.raise_objection(this, "need time to finish last item");
    fork begin
      wait_fifo_empty();
      phase.drop_objection(this);
    end
    join_none
  endfunction


  virtual task wait_fifo_empty();
    `uvm_info(`gfn, $sformatf("item fifo entries %d", item_fifo.num()), UVM_MEDIUM)
    wait (rcv_item_q.size() == 0);
    wait (item_fifo.num()   == 0);
    wait (msg_fifo.num()    == 0);
  endtask


  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
  endfunction


  function void check_phase(uvm_phase phase);
    string txt =  "";
    uvm_report_server rpt_srvr;

    if (cfg.en_scb) begin
      super.check_phase(phase);
      `DV_EOT_PRINT_MAILBOX_CONTENTS(aes_message_item, msg_fifo)
      `DV_EOT_PRINT_MAILBOX_CONTENTS(aes_seq_item, item_fifo)
      `DV_EOT_PRINT_Q_CONTENTS(aes_seq_item, rcv_item_q)
      if (good_cnt != (cfg.num_messages - cfg.num_corrupt_messages - skipped_cnt + cfg.split_cnt)) begin
        rpt_srvr = uvm_report_server::get_server();
        if (rpt_srvr.get_severity_count(UVM_FATAL)+rpt_srvr.get_severity_count(UVM_ERROR) == 0) begin
          txt = "\n\t ----| NO FAILURES BUT DIDN*T SEE ALL EXPECTED MESSAGES";
        end else begin
          txt = "\n\t ----| TEST FAILED";
        end

        txt = { txt, $sformatf(" \n\t ----| Expected:\t %d", cfg.num_messages)};
        txt = { txt, $sformatf(" \n\t ----| Seen: \t%d",  good_cnt)};
        txt = { txt, $sformatf(" \n\t ----| Expected corrupted: \t%d", cfg.num_corrupt_messages)};
        txt = { txt, $sformatf(" \n\t ----| Seen corrupted: \t%d", corrupt_cnt)};
        txt = { txt, $sformatf(" \n\t ----| Skipped: \t%d", skipped_cnt)};
        txt = { txt, $sformatf(" \n\t ----| Split: \t%d", cfg.split_cnt)};
        `uvm_fatal(`gfn, $sformatf("%s", txt) )
      end
    end
  endfunction


  function void report_phase(uvm_phase phase);
    uvm_report_server rpt_srvr;
    string txt="";

    super.report_phase(phase);
    txt = $sformatf("\n\t ----|        TEST FINISHED        |----");
    txt = { txt, $sformatf("\n\t Saw %d Good messages  ", good_cnt)};
    txt = { txt, $sformatf("\n\t Skipped %d messages  " , skipped_cnt)};
    txt = { txt, $sformatf("\n\t Split %d messages  "   , cfg.split_cnt)};
    txt = { txt, $sformatf("\n\t Expected %d messages  ", cfg.num_messages)};
    txt = { txt, $sformatf("\n\t Expected %d corrupted ", cfg.num_corrupt_messages)};
    rpt_srvr = uvm_report_server::get_server();
    if (rpt_srvr.get_severity_count(UVM_FATAL)+rpt_srvr.get_severity_count(UVM_ERROR)>0) begin
      `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_LOW)
      txt = { txt,"\n\t---------------------------------------"};
      txt = { txt,"\n\t----            TEST FAILED        ----"};
      txt = { txt,"\n\t---------------------------------------"};
    end else begin
      txt = {txt, "\n\t---------------------------------------"};
      txt = { txt,"\n\t----            TEST PASSED        ----"};
      txt = { txt,"\n\t---------------------------------------"};
    end
    `uvm_info(`gfn, $sformatf("%s", txt), UVM_MEDIUM)

  endfunction // report_phase
endclass
