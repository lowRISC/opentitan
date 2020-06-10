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

  bit          aes_from_rst   = 1;            // 1: nothing has happened since rst was released
  bit          ok_to_fwd      = 0;            // 0: item is not ready to forward
  bit          finish_message = 0;            // set when test is trying to end
                                              // - to indicate the last message is finished
  int          message_cnt    = 0;            // used to check that all messages were received

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
    `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_HIGH)
    if(cfg.en_scb) begin
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
    uvm_reg_addr_t csr_addr      = get_normalized_addr(item.a_addr);

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
      `uvm_info(`gfn, $sformatf("ITEM received reg name : %s",csr.get_name() ), UVM_HIGH)
      csr_name = csr.get_name();
      case (1)
        // add individual case item for each csr
         (!uvm_re_match("ctrl", csr_name)): begin
          input_item.manual_op = item.a_data[7];
          input_item.key_len   = item.a_data[6:4];
          `downcast(input_item.operation, item.a_data[0]);
          case (item.a_data[3:1])
            3'b001:  input_item.mode = AES_ECB;
            3'b010:  input_item.mode = AES_CBC;
            3'b100:  input_item.mode = AES_CTR;
            default: input_item.mode = AES_ECB;
          endcase // case item.a_data[3
        end

        (!uvm_re_match("key*", csr_name)): begin
          for (int i = 0; i < 8; i++) begin
            string keyname = $sformatf("key%0d", i);
            if (keyname == csr_name) begin
               input_item.key[i]      = item.a_data;
               input_item.key_vld[i]  = 1'b1;
            end
          end
        end

        (!uvm_re_match("data_in*", csr_name)): begin
          for (int i = 0; i < 4; i++) begin
            string keyname = $sformatf("data_in%0d", i);
            if (keyname == csr_name) begin
              input_item.data_in[i]      = item.a_data;
              input_item.data_in_vld[i]  = 1'b1;
            end
          end
        end

       (!uvm_re_match("iv*", csr_name)): begin
          for (int i = 0; i < 4; i++) begin
            string keyname = $sformatf("iv%0d", i);
            if (keyname == csr_name) begin
              input_item.iv[i]      = item.a_data;
              input_item.iv_vld[i]  = 1'b1;
            end
          end
       end

     //    TODO
     //   "trigger": begin
     //     if (item.a_data[0]) begin
     //       //            `downcast(ref_item, input_item.clone());
     //       //            ref_fifo.put(ref_item);
     //     end
     //   end
     //
     //   "status": begin
     //     //TBD
     //   end

        default: begin
          // DO nothing- trying to write to a read only register
        end
      endcase


      ///////////////////////////////////////
      //             Valid checks          //
      ///////////////////////////////////////

      // check that the item is valid - all registers clean base on mode //
      case (input_item.mode)
        AES_ECB: begin
          if(aes_from_rst) begin
            // verify that all 4 data_in and all 8 key have been updated
            if(input_item.data_in_valid() && input_item.key_clean(0)) begin
              //clone and add to ref and rec data fifo
              ok_to_fwd    = 1;
              aes_from_rst = 0;
              `uvm_info(`gfn, $sformatf("\n\t ----| First ITEM created  OK to clone"), UVM_HIGH)
            end
          end else begin
            // verify that all 4 data_in and all 8 key are clean
            `uvm_info(`gfn, $sformatf("\n\t ----|data_inv_vld?  %b, key clean ? %b",
                      input_item.data_in_valid(), input_item.key_clean(1) ), UVM_HIGH)

            if(input_item.data_in_valid() && input_item.key_clean(1)) begin
              //clone and add to ref and rec data fifo
              `uvm_info(`gfn, $sformatf("\n\t ----| OK to clone"), UVM_HIGH)
              ok_to_fwd = 1;
            end
          end
        end

        AES_CBC: begin
          if(aes_from_rst) begin
            // verify that all 4 data_in and all 8 key and all 4 IV have been updated
            if(input_item.data_in_valid() && input_item.key_clean(0) && input_item.iv_clean(0)) begin
              //clone and add to ref and rec data fifo
              ok_to_fwd    = 1;
              aes_from_rst = 0;
              `uvm_info(`gfn, $sformatf("\n\t ----| First ITEM created  OK to clone"), UVM_HIGH)
            end
          end else begin
            // verify that all 4 data_in and all 8 key  and all 4 IV are clean
            `uvm_info(`gfn, $sformatf("\n\t ----|data_inv_vld?  %b, key clean ? %b",
                              input_item.data_in_valid(), input_item.key_clean(1) ), UVM_HIGH)

            if(input_item.data_in_valid() && input_item.key_clean(1) && input_item.iv_clean(1)) begin
              //clone and add to ref and rec data fifo
              `uvm_info(`gfn, $sformatf("\n\t ----| OK to clone"), UVM_HIGH)
              ok_to_fwd = 1;
            end
          end
        end

        AES_CTR: begin
          if(aes_from_rst) begin
            // verify that all 4 data_in and all 8 key and all 4 IV have been updated
            if(input_item.data_in_valid() && input_item.key_clean(0) && input_item.iv_clean(0)) begin
              //clone and add to ref and rec data fifo
              ok_to_fwd    = 1;
              aes_from_rst = 0;
              `uvm_info(`gfn, $sformatf("\n\t ----| First ITEM created  OK to clone"), UVM_HIGH)
            end
          end else begin
            // verify that all 4 data_in and all 8 and all 4 IV  key are clean
            `uvm_info(`gfn, $sformatf("\n\t ----|data_inv_vld?  %b, key clean ? %b",input_item.data_in_valid(), input_item.key_clean(1) ), UVM_HIGH)
            if(input_item.data_in_valid() && input_item.key_clean(1) && input_item.iv_clean(1)) begin
              //clone and add to ref and rec data fifo
              `uvm_info(`gfn, $sformatf("\n\t ----| OK to clone"), UVM_HIGH)
              ok_to_fwd = 1;
            end
          end
        end
        default: begin
          `uvm_fatal(`gfn, $sformatf("\n\t ----| I AM IN DEFAULT CASE I SHOULD NOT BE HERE"))
        end
      endcase // case (input_item.mode)

      // forward item to receive side
      if(ok_to_fwd ) begin
        ok_to_fwd = 0;
        `downcast(input_clone, input_item.clone());
        `uvm_info(`gfn, $sformatf("\n\t AES INPUT ITEM RECEIVED - \n %s", input_clone.convert2string()), UVM_HIGH)
        rcv_item_q.push_front(input_clone);
        input_item.clean();
      end
    end


    //////////////////////////////////////////////////////////////////////////////
    // get an item from the rcv queue and wait for all output data to be received
    //////////////////////////////////////////////////////////////////////////////

    `uvm_info(`gfn, $sformatf("\n\t ---| channel  %h", channel), UVM_HIGH)
    if (!write && channel == DataChannel) begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
      `uvm_info(`gfn, $sformatf("\n\t ----| SAW READ - %s data %02h",csr.get_name(),  item.d_data)
                , UVM_HIGH)

      case (csr.get_name())
        "data_out0": begin
          output_item.data_out[0]     = item.d_data;
          output_item.data_out_vld[0] = 1;
        end
        "data_out1": begin
          output_item.data_out[1]     = item.d_data;
          output_item.data_out_vld[1] = 1;
        end
        "data_out2": begin
          output_item.data_out[2]     = item.d_data;
          output_item.data_out_vld[2] = 1;
        end
        "data_out3": begin
          output_item.data_out[3]     = item.d_data;
          output_item.data_out_vld[3] = 1;
        end
      endcase // case (csr.get_name())

      if (output_item.data_out_valid()) begin
        if( rcv_item_q.size() == 0) begin
          `uvm_fatal(`gfn, $sformatf("\n\t ----| TRIED TO READ EMPTY RECEIVE QUEUE |----"))
        end

        complete_item              = rcv_item_q.pop_back();
        complete_item.data_out     = output_item.data_out;

        `downcast(complete_clone, complete_item.clone());
        item_fifo.put(complete_clone);

        output_item                = new();
        complete_item              = new();
        `uvm_info(`gfn,
          $sformatf("\n\t ----|added data to item_fifo (output received) fifo entries %d", 
                   item_fifo.num()), UVM_HIGH)
      end
    end
  endtask // process_tl_access


  // takes items from the item queue and builds full aes_messages with both input data and output data.
  task rebuild_message();
    typedef enum { MSG_START,MSG_RUN } aes_message_stat_t;

    aes_message_item   message, msg_clone;
    aes_seq_item       full_item;
    aes_message_stat_t msg_state;

    message = new();

    fork
      begin
        forever begin
          case(msg_state)
            MSG_START: begin
              full_item = new();
              item_fifo.get(full_item);
              `uvm_info(`gfn, $sformatf("\n\t ----| got item from item fifo"), UVM_FULL)
              if(!full_item.message_start()) begin
                `uvm_fatal(`gfn,
                 $sformatf("\n\t ----| FIRST ITEM DID NOT HAVE MESSAGE START/CONFIG SETTINGS"))
              end
              message.add_start_msg_item(full_item);
              msg_state = MSG_RUN;
            end

            MSG_RUN: begin
              full_item = new();
              item_fifo.get(full_item);
              `uvm_info(`gfn, $sformatf("\n\t ----| got item from item fifo"), UVM_FULL)
              if(full_item.message_start() ) begin
                `uvm_info(`gfn, $sformatf("\n\t ----| adding message item to mg_fifo"), UVM_FULL)
                `downcast(msg_clone, message.clone());
                msg_fifo.put(msg_clone);
                message = new();
                message.add_start_msg_item(full_item);
              end else begin
                message.add_data_item(full_item);
              end
            end
          endcase // case (msg_state)
        end
      end

      begin
        wait( finish_message )
        `uvm_info(`gfn, $sformatf("\n\t ----|Finish test received adding message item to mg_fifo")
         , UVM_HIGH)

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

      `uvm_info(`gfn, $sformatf("\n\t ----| TRYING to get item "), UVM_HIGH)
      msg_fifo.get(msg);

      `uvm_info(`gfn, $sformatf("\n\t ----| GOT item "), UVM_HIGH)
      `uvm_info(`gfn, $sformatf("model %b, operation: %b, mode %03b, IV %h, key_len %03b, key %h ",
                                cfg.ref_model, msg.aes_operation, msg.aes_mode, msg.aes_iv, msg.aes_keylen, msg.aes_key)
                , UVM_HIGH)

      msg.alloc_predicted_msg();
      //ref-model      / opration     / chipher mode /    IV   / key_len    / key /data i /data o //
      c_dpi_aes_crypt_message(cfg.ref_model, msg.aes_operation, msg.aes_mode, msg.aes_iv, 
                              msg.aes_keylen, msg.aes_key, msg.input_msg, msg.predicted_msg);

      `uvm_info(`gfn, $sformatf("\n\t ----| printing MESSAGE %s", msg.convert2string() )
                , UVM_HIGH)
      txt = "";
      foreach(msg.input_msg[i]) begin
        txt = { txt, $sformatf("\n\t  %h \t %h \t %h",
                               msg.input_msg[i],msg.output_msg[i], msg.predicted_msg[i])};
      end

      `uvm_info(`gfn, $sformatf("\n\t input \t output \t predicted %s",txt), UVM_HIGH)

      for( int n =0 ; n < msg.input_msg.size(); n++) begin
        if( msg.output_msg[n] != msg.predicted_msg[n]) begin
          txt = "\t TEST FAILED MESSAGES DID NOT MATCH";

          txt = {txt,  $sformatf("\n\t ----| ACTUAL OUTPUT DID NOT MATCH PREDICTED OUTPUT |----")};
          txt = {txt, $sformatf("\n\t ----| FAILED AT BLOCK #%d \t ACTUAL: %h \t PREDICTED: %h, ", 
                                n, msg.output_msg[n], msg.predicted_msg[n] )};
          `uvm_fatal(`gfn, $sformatf(" # %d  \n\t %s \n",message_cnt, txt))
        end
      end
      `uvm_info(`gfn, $sformatf("\n\t ----|   MESSAGE #%d MATCHED    |-----",message_cnt), UVM_HIGH)
      message_cnt++;
    end
  endtask

  // TODO get rid of this and do EOP checks in monitor
  virtual function void phase_ready_to_end(uvm_phase phase);
    if (phase.get_name() != "run") return;

    // the message currently being reassembled is should be sent for scoring
    finish_message = 1;
    `uvm_info(`gfn, $sformatf("Finish message: %b", finish_message), UVM_HIGH)

    // AEs needs this objection - because PHASE READY TO END
    // is the only way to know that the very last message is now complete
    phase.raise_objection(this, "need time to finish last item");
    fork begin
      wait_fifo_empty();
      phase.drop_objection(this);
    end
    join_none
  endfunction


  virtual task wait_fifo_empty();
    `uvm_info(`gfn, $sformatf("item fifo entries %d", item_fifo.num()), UVM_HIGH)
    wait (rcv_item_q.size() == 0 );
    wait (item_fifo.num()   == 0 );
    wait (msg_fifo.num()    == 0 );
  endtask


  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    // reset local fifos queues and variables
  endfunction


  function void check_phase(uvm_phase phase);
    string txt =  "";
    if (cfg.en_scb) begin
      `uvm_info(`gfn, $sformatf(" RASMUS JUST CHECKING"), UVM_LOW)
      super.check_phase(phase);
      `DV_EOT_PRINT_MAILBOX_CONTENTS(aes_message_item, msg_fifo)
      `DV_EOT_PRINT_MAILBOX_CONTENTS(aes_seq_item, item_fifo)
      `DV_EOT_PRINT_Q_CONTENTS(aes_seq_item, rcv_item_q)
      if(message_cnt != cfg.num_messages) begin
        txt = "\n\t ----| NO FAILURES BUT DIDN*T SEE ALL EXPECTED MESSAGES";
        txt = { txt, $sformatf(" \n\t ----| expected %d, seen: %d", cfg.num_messages, message_cnt ) };
        `uvm_fatal(`gfn, $sformatf("%s", txt) )
      end
    end

  endfunction


  function void report_phase(uvm_phase phase);
    uvm_report_server rpt_srvr;
    string txt="";

    super.report_phase(phase);
    txt = $sformatf("\n\t ----|        TEST FINISHED        |----");
    txt = {   txt, $sformatf("\n\t SAW %d Good messages ", message_cnt)};
    txt = {   txt, $sformatf("\n\t Expected %d messages ", cfg.num_messages)};
    rpt_srvr = uvm_report_server::get_server();
    if(rpt_srvr.get_severity_count(UVM_FATAL)+rpt_srvr.get_severity_count(UVM_ERROR)>0) begin
      `uvm_info(`gfn, $sformatf("%s", cfg.convert2string()), UVM_LOW)
      txt = { txt,"\n\t---------------------------------------"};
      txt = { txt,"\n\t----            TEST FAILED        ----"};
      txt = { txt,"\n\t---------------------------------------"};
    end else begin
      txt = {txt, "\n\t---------------------------------------"};
      txt = { txt,"\n\t----            TEST PASSED        ----"};
      txt = { txt,"\n\t---------------------------------------"};
    end
    `uvm_info(`gfn, $sformatf("%s", txt), UVM_HIGH)

  endfunction // report_phase
endclass
