// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

import aes_model_dpi_pkg::*;
import aes_pkg::*;

class aes_scoreboard extends cip_base_scoreboard#(
    .CFG_T(aes_env_cfg), .RAL_T(aes_reg_block), .COV_T(aes_env_cov)
);

  `uvm_component_utils(aes_scoreboard)

  `uvm_component_new

  // local variables
  aes_seq_item input_item;  // item containing data and config
  aes_seq_item output_item;  // item containing resulting output
  aes_seq_item complete_item;  // merge of input and output items

  bit aes_from_rst = 1;  // 1: nothing has happened since rst was released
  bit ok_to_fwd = 0;  // 0: item is not ready to forward
  bit finish_message = 0;  // set when test is trying to end
  // - to indicate the last message is finished
  int message_cnt = 0;  // used to check that all messages were received

  // local queues to hold incoming packets pending comparison //

  // Items containing both input and output data, ready to be added to a message
  mailbox #(aes_seq_item) item_fifo;
  // completed message item ready for scoring
  mailbox #(aes_message_item) msg_fifo;
  // once an operation is started the item is put here to wait for the resuting output
  aes_seq_item rcv_item_q[$];


  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    msg_fifo = new();
    item_fifo = new();
    input_item = new("input_item");
    output_item = new();
  endfunction


  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction


  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_MEDIUM)
    if (cfg.en_scb) begin
      fork
        compare();
        rebuild_message();
      join_none
    end
  endtask


  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg csr;
    string csr_name;
    aes_seq_item input_clone;
    aes_seq_item complete_clone;
    bit do_read_check = 1'b0;
    bit write = item.is_write();
    uvm_reg_addr_t csr_addr = get_normalized_addr(item.a_addr);

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
      `uvm_info(`gfn, $sformatf("\n\t ----| ITEM received reg name : %s", csr.get_name()),
                UVM_MEDIUM)
      csr_name = csr.get_name();
      case (1)
        // add individual case item for each csr
        (!uvm_re_match("ctrl_shadowed", csr_name)): begin
          input_item.manual_op = item.a_data[10];
          input_item.key_len = item.a_data[9:7];
          `downcast(input_item.operation, item.a_data[0]);
          input_item.valid = 1'b1;
          case (item.a_data[6:1])
            6'b00_0001: input_item.mode = AES_ECB;
            6'b00_0010: input_item.mode = AES_CBC;
            6'b00_0100: input_item.mode = AES_CFB;
            6'b00_1000: input_item.mode = AES_OFB;
            6'b01_0000: input_item.mode = AES_CTR;
            6'b10_0000: input_item.mode = AES_NONE;
            default: input_item.mode = AES_ECB;
          endcase  // case item.a_data[4:1]
        end

        (!uvm_re_match("key_share0*", csr_name)): begin
          for (int i = 0; i < 8; i++) begin
            string keyname = $sformatf("key_share0_%0d", i);
            if (keyname == csr_name) begin
              input_item.key[0][i] = item.a_data;
              input_item.key_vld[0][i] = 1'b1;
            end
          end
        end

        (!uvm_re_match("key_share1*", csr_name)): begin
          for (int i = 0; i < 8; i++) begin
            string keyname = $sformatf("key_share1_%0d", i);
            if (keyname == csr_name) begin
              input_item.key[1][i] = item.a_data;
              input_item.key_vld[1][i] = 1'b1;
            end
          end
        end

        (!uvm_re_match("data_in_*", csr_name)): begin
          for (int i = 0; i < 4; i++) begin
            string keyname = $sformatf("data_in_%0d", i);
            if (keyname == csr_name) begin
              input_item.data_in[i] = item.a_data;
              input_item.data_in_vld[i] = 1'b1;
            end
          end
        end

        (!uvm_re_match("iv_*", csr_name)): begin
          for (int i = 0; i < 4; i++) begin
            string keyname = $sformatf("iv_%0d", i);
            if (keyname == csr_name) begin
              input_item.iv[i] = item.a_data;
              input_item.iv_vld[i] = 1'b1;
            end
          end
        end

        (!uvm_re_match("trigger", csr_name)): begin
          //start triggered
          if (item.a_data[0]) begin
            ok_to_fwd = 1;
            aes_from_rst = 0;
          end
          // clear key
          if (item.a_data[1]) begin
            if (cfg.clear_reg_w_rand) begin
              input_item.key = '{default: {8{$urandom()}}};
            end else begin
              input_item.key = '{default: '0};
            end
          end
          // clear IV
          if (item.a_data[2]) begin
            if (cfg.clear_reg_w_rand) begin
              input_item.iv = {4{$urandom()}};
            end else begin
              input_item.iv = '0;
            end
          end
          // clear data_in
          if (item.a_data[3]) begin
            if (cfg.clear_reg_w_rand) begin
              input_item.data_in = {4{$urandom()}};
            end else begin
              input_item.data_in = '0;
            end
          end
          // clear data out
          if (item.a_data[4]) begin
            if (cfg.clear_reg_w_rand) begin
              input_item.data_out = {4{$urandom()}};
            end else begin
              input_item.data_out = '0;
            end
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
            `uvm_info(`gfn, $sformatf("\n\t ----| ECB mode"), UVM_MEDIUM)
            if (aes_from_rst) begin
              // verify that all 4 data_in and all 8 key have been updated
              if (input_item.data_in_valid() && input_item.key_clean(0)) begin
                //clone and add to ref and rec data fifo
                ok_to_fwd = 1;
                aes_from_rst = 0;
              end
            end else begin
              // verify that all 4 data_in and all 8 key are clean
              `uvm_info(`gfn,
                        $sformatf("\n\t ----|data_inv_vld?  %b, key clean ? %b",
                                  input_item.data_in_valid(), input_item.key_clean(1)),
                        UVM_MEDIUM)

              if (input_item.data_in_valid() && input_item.key_clean(1)) begin
                //clone and add to ref and rec data fifo
                ok_to_fwd = 1;
              end
            end
          end

          AES_CBC: begin
            `uvm_info(`gfn, $sformatf("\n\t ----| CBC mode"), UVM_MEDIUM)
            if (aes_from_rst) begin
              // verify that all 4 data_in and all 8 key and all 4 IV have been updated
              if (input_item.data_in_valid() && input_item.key_clean(0) && input_item.iv_clean(0)
                  ) begin
                //clone and add to ref and rec data fifo
                ok_to_fwd = 1;
                aes_from_rst = 0;
              end
            end else begin
              // verify that all 4 data_in and all 8 key  and all 4 IV are clean
              `uvm_info(`gfn,
                        $sformatf("\n\t ----|data_inv_vld?  %b, key clean ? %b",
                                  input_item.data_in_valid(), input_item.key_clean(1)),
                        UVM_MEDIUM)

              if (input_item.data_in_valid() && input_item.key_clean(1) && input_item.iv_clean(1)
                  ) begin
                //clone and add to ref and rec data fifo
                ok_to_fwd = 1;
              end
            end
          end

          AES_CFB: begin
            if (aes_from_rst) begin
              // verify that all 4 data_in and all 8 key and all 4 IV have been updated
              if (input_item.data_in_valid() && input_item.key_clean(0) && input_item.iv_clean(0)
                  ) begin
                //clone and add to ref and rec data fifo
                ok_to_fwd = 1;
                aes_from_rst = 0;
              end
            end else begin
              // verify that all 4 data_in and all 8 key  and all 4 IV are clean
              `uvm_info(`gfn,
                        $sformatf("\n\t ----|data_inv_vld?  %b, key clean ? %b",
                                  input_item.data_in_valid(), input_item.key_clean(1)),
                        UVM_HIGH)

              if (input_item.data_in_valid() && input_item.key_clean(1) && input_item.iv_clean(1)
                  ) begin
                //clone and add to ref and rec data fifo
                ok_to_fwd = 1;
              end
            end
          end

          AES_OFB: begin
            if (aes_from_rst) begin
              // verify that all 4 data_in and all 8 key and all 4 IV have been updated
              if (input_item.data_in_valid() && input_item.key_clean(0) && input_item.iv_clean(0)
                  ) begin
                //clone and add to ref and rec data fifo
                ok_to_fwd = 1;
                aes_from_rst = 0;
              end
            end else begin
              // verify that all 4 data_in and all 8 key  and all 4 IV are clean
              `uvm_info(`gfn,
                        $sformatf("\n\t ----|data_inv_vld?  %b, key clean ? %b",
                                  input_item.data_in_valid(), input_item.key_clean(1)),
                        UVM_HIGH)

              if (input_item.data_in_valid() && input_item.key_clean(1) && input_item.iv_clean(1)
                  ) begin
                //clone and add to ref and rec data fifo
                ok_to_fwd = 1;
              end
            end
          end

          AES_CTR: begin
            `uvm_info(`gfn, $sformatf("\n\t ----| CTR mode"), UVM_MEDIUM)
            if (aes_from_rst) begin
              // verify that all 4 data_in and all 8 key and all 4 IV have been updated
              if (input_item.data_in_valid() && input_item.key_clean(0) && input_item.iv_clean(0)
                  ) begin
                //clone and add to ref and rec data fifo
                ok_to_fwd = 1;
                aes_from_rst = 0;
              end
            end else begin
              // verify that all 4 data_in and all 8 and all 4 IV  key are clean
              `uvm_info(`gfn,
                        $sformatf("\n\t ----|data_inv_vld?  %b, key clean ? %b",
                                  input_item.data_in_valid(), input_item.key_clean(1)),
                        UVM_MEDIUM)
              if (input_item.data_in_valid() && input_item.key_clean(1) && input_item.iv_clean(1)
                  ) begin
                //clone and add to ref and rec data fifo
                ok_to_fwd = 1;
              end
            end
          end
          default: begin
            `uvm_fatal(`gfn, $sformatf("\n\t ----| I AM IN DEFAULT CASE I SHOULD NOT BE HERE"))
          end
        endcase  // case (input_item.mode)
      end  // if (input_item.valid)

      // forward item to receive side
      if (ok_to_fwd) begin
        ok_to_fwd = 0;
        `downcast(input_clone, input_item.clone());
        `uvm_info(`gfn,
                  $sformatf("\n\t AES INPUT ITEM RECEIVED - \n %s", input_clone.convert2string()),
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
      `uvm_info(`gfn, $sformatf("\n\t ----| SAW READ - %s data %02h", csr.get_name(), item.d_data),
                UVM_MEDIUM)

      case (csr.get_name())
        "data_out_0": begin
          output_item.data_out[0] = item.d_data;
          output_item.data_out_vld[0] = 1;
        end
        "data_out_1": begin
          output_item.data_out[1] = item.d_data;
          output_item.data_out_vld[1] = 1;
        end
        "data_out_2": begin
          output_item.data_out[2] = item.d_data;
          output_item.data_out_vld[2] = 1;
        end
        "data_out_3": begin
          output_item.data_out[3] = item.d_data;
          output_item.data_out_vld[3] = 1;
        end
      endcase  // case (csr.get_name())

      if (output_item.data_out_valid()) begin
        if (rcv_item_q.size() == 0) begin
          `uvm_fatal(`gfn, $sformatf("\n\t ----| TRIED TO READ EMPTY RECEIVE QUEUE |----"))
        end

        complete_item = rcv_item_q.pop_back();
        complete_item.data_out = output_item.data_out;

        `downcast(complete_clone, complete_item.clone());
        item_fifo.put(complete_clone);

        output_item = new();
        complete_item = new();
        `uvm_info(`gfn,
                  $sformatf("\n\t ----|added data to item_fifo (output received) fifo entries %d",
                            item_fifo.num()),
                  UVM_MEDIUM)
      end
    end
  endtask  // process_tl_access


  // takes items from the item queue and builds full aes_messages with both input data and output data.
  task rebuild_message();
    typedef enum {
      MSG_START,
      MSG_RUN
    } aes_message_stat_t;

    aes_message_item message, msg_clone;
    aes_seq_item full_item;
    aes_message_stat_t msg_state;

    message = new();

    fork
      begin
        forever begin
          case (msg_state)
            MSG_START: begin
              full_item = new();
              item_fifo.get(full_item);
              `uvm_info(`gfn, $sformatf("\n\t ----| got item from item fifo"), UVM_FULL)
              if (!full_item.message_start()) begin
                `uvm_fatal(`gfn,
                           $sformatf(
                               "\n\t ----| FIRST ITEM DID NOT HAVE MESSAGE START/CONFIG SETTINGS"))
              end
              message.add_start_msg_item(full_item);
              msg_state = MSG_RUN;
            end

            MSG_RUN: begin
              full_item = new();
              item_fifo.get(full_item);
              `uvm_info(`gfn, $sformatf("\n\t ----| got item from item fifo"), UVM_FULL)
              if (full_item.message_start()) begin
                `uvm_info(`gfn, $sformatf("\n\t ----| adding message item to mg_fifo"), UVM_FULL)
                `downcast(msg_clone, message.clone());
                msg_fifo.put(msg_clone);
                message = new();
                message.add_start_msg_item(full_item);
              end else begin
                message.add_data_item(full_item);
              end
            end
          endcase  // case (msg_state)
        end
      end

      begin
        wait(finish_message)
          `uvm_info(`gfn,
                    $sformatf("\n\t ----| Finish test received adding message item to mg_fifo"),
                    UVM_MEDIUM)

        `downcast(msg_clone, message.clone());
        msg_fifo.put(msg_clone);
      end
    join_any
  endtask  // rebuild_message


  virtual task compare();
    string txt = "";
    bit [3:0][31:0] tmp_input;
    bit [3:0][31:0] tmp_output;

    forever begin
      aes_message_item msg;

      msg_fifo.get(msg);
      `uvm_info(`gfn,
                $sformatf(
                    "model %b, operation: %b, mode %06b, IV %h, key_len %03b, key share0 %h, key share1 %h "
                        , cfg.ref_model, msg.aes_operation, msg.aes_mode, msg.aes_iv,
                        msg.aes_keylen, msg.aes_key[0], msg.aes_key[1]),
                UVM_MEDIUM)

      msg.alloc_predicted_msg();
      //ref-model      / opration     / chipher mode /    IV   / key_len    / key /data i /data o //
      c_dpi_aes_crypt_message(cfg.ref_model, msg.aes_operation, msg.aes_mode, msg.aes_iv,
                              msg.aes_keylen, msg.aes_key[0] ^ msg.aes_key[1], msg.input_msg,
                              msg.predicted_msg);

      `uvm_info(`gfn, $sformatf("\n\t ----| printing MESSAGE %s", msg.convert2string()), UVM_MEDIUM)
      txt = "";
      foreach (msg.input_msg[i]) begin
        txt = {
          txt,
          $sformatf("\n\t  %h \t %h \t %h", msg.input_msg[i], msg.output_msg[i],
                    msg.predicted_msg[i])
        };
      end


      for (int n = 0; n < msg.input_msg.size(); n++) begin
        if (msg.output_msg[n] != msg.predicted_msg[n]) begin
          txt = "\t TEST FAILED MESSAGES DID NOT MATCH";

          txt = {txt, $sformatf("\n\t ----| ACTUAL OUTPUT DID NOT MATCH PREDICTED OUTPUT |----")};
          txt = {
            txt,
            $sformatf("\n\t ----| FAILED AT BLOCK #%d \t ACTUAL: %h \t PREDICTED: %h, ", n,
                      msg.output_msg[n], msg.predicted_msg[n])
          };
          `uvm_fatal(`gfn, $sformatf(" # %d  \n\t %s \n", message_cnt, txt))
        end
      end
      `uvm_info(`gfn, $sformatf("\n\t ----|   MESSAGE #%0d MATCHED    |-----", message_cnt),
                UVM_MEDIUM)
      message_cnt++;
    end
  endtask

  // TODO get rid of this and do EOP checks in monitor
  virtual function void phase_ready_to_end(uvm_phase phase);
    if (phase.get_name() != "run") return;

    // the message currently being reassembled is should be sent for scoring
    finish_message = 1;
    `uvm_info(`gfn, $sformatf("Finish message: %b", finish_message), UVM_MEDIUM)

    // AEs needs this objection - because PHASE READY TO END
    // is the only way to know that the very last message is now complete
    phase.raise_objection(this, "need time to finish last item");
    fork
      begin
        wait_fifo_empty();
        phase.drop_objection(this);
      end
    join_none
  endfunction


  virtual task wait_fifo_empty();
    `uvm_info(`gfn, $sformatf("item fifo entries %d", item_fifo.num()), UVM_MEDIUM)
    wait(rcv_item_q.size() == 0);
    wait(item_fifo.num() == 0);
    wait(msg_fifo.num() == 0);
  endtask


  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
  endfunction


  function void check_phase(uvm_phase phase);
    string txt = "";
    uvm_report_server rpt_srvr;

    if (cfg.en_scb) begin
      super.check_phase(phase);
      `DV_EOT_PRINT_MAILBOX_CONTENTS(aes_message_item, msg_fifo)
      `DV_EOT_PRINT_MAILBOX_CONTENTS(aes_seq_item, item_fifo)
      `DV_EOT_PRINT_Q_CONTENTS(aes_seq_item, rcv_item_q)
      if (message_cnt != cfg.num_messages) begin
        rpt_srvr = uvm_report_server::get_server();
        if (rpt_srvr.get_severity_count(UVM_FATAL) + rpt_srvr.get_severity_count(UVM_ERROR) == 0
            ) begin
          txt = "\n\t ----| NO FAILURES BUT DIDN*T SEE ALL EXPECTED MESSAGES";
        end else begin
          txt = "\n\t ----| TEST FAILED";
        end
        txt = {txt, $sformatf(" \n\t ----| expected %d, seen: %d", cfg.num_messages, message_cnt)};
        `uvm_fatal(`gfn, $sformatf("%s", txt))
      end
    end

  endfunction


  function void report_phase(uvm_phase phase);
    uvm_report_server rpt_srvr;
    string txt = "";

    super.report_phase(phase);
    txt = $sformatf("\n\t ----|        TEST FINISHED        |----");
    txt = {txt, $sformatf("\n\t SAW %d Good messages ", message_cnt)};
    txt = {txt, $sformatf("\n\t Expected %d messages ", cfg.num_messages)};
    rpt_srvr = uvm_report_server::get_server();
    if (rpt_srvr.get_severity_count(UVM_FATAL) + rpt_srvr.get_severity_count(UVM_ERROR) > 0) begin
      `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_LOW)
      txt = {txt, "\n\t---------------------------------------"};
      txt = {txt, "\n\t----            TEST FAILED        ----"};
      txt = {txt, "\n\t---------------------------------------"};
    end else begin
      txt = {txt, "\n\t---------------------------------------"};
      txt = {txt, "\n\t----            TEST PASSED        ----"};
      txt = {txt, "\n\t---------------------------------------"};
    end
    `uvm_info(`gfn, $sformatf("%s", txt), UVM_MEDIUM)

  endfunction  // report_phase
endclass
