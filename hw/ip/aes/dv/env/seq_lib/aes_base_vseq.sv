// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class aes_base_vseq extends cip_base_vseq #(
  .CFG_T               (aes_env_cfg),
  .RAL_T               (aes_reg_block),
  .COV_T               (aes_env_cov),
  .VIRTUAL_SEQUENCER_T (aes_virtual_sequencer)
  );

  `uvm_object_utils(aes_base_vseq)
  `uvm_object_new

  aes_reg2hw_t       aes_reg;
  aes_seq_item       aes_item;
  aes_seq_item       aes_item_queue[$];
  aes_message_item   aes_message;
  aes_message_item   message_queue[$];

  // various knobs to enable certain routines
  bit                do_aes_init = 1'b1;

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_aes_init) aes_init();
    aes_item = new();
    aes_message_init();
    `uvm_info(`gfn, $sformatf("\n TL delay: [%d:%d] \n zero delay %d",
              cfg.m_tl_agent_cfg.d_ready_delay_min,cfg.m_tl_agent_cfg.d_ready_delay_max,
              cfg.zero_delays  ), UVM_HIGH)
  endtask

  virtual task dut_shutdown();
    // check for pending aes operations and wait for them to complete
    // TODO
  endtask

  // setup basic aes features
  virtual task aes_init();

    bit [31:0] aes_ctrl    = '0;
    bit [31:0] aes_trigger = '0;

    `uvm_info(`gfn, $sformatf("\n\t ----| CHECKING FOR IDLE"), UVM_HIGH)
     // Wait for DUT ready
    csr_spinwait(.ptr(ral.status.idle) , .exp_data(1'b1));

    // initialize control register
    aes_ctrl[0]    = 0;                  // set to encryption
    aes_ctrl[6:1]  = aes_pkg::AES_ECB;   // 6'b00_0001
    aes_ctrl[9:7]  = aes_pkg::AES_128;   // set to 128b key
    csr_wr(.csr(ral.ctrl_shadowed), .value(aes_ctrl), .en_shadow_wr(1'b1), .blocking(1));
  endtask // aes_init


  virtual task trigger();
      csr_wr(.csr(ral.trigger), .value(32'h00000001));
  endtask // trigger


  virtual task clear_regs(clear_t clr_vector);
    string txt="";
    bit [TL_DW:0] reg_val = '0;

    txt = $sformatf("\n data_out: \t %0b", clr_vector.data_out);
    txt = {txt, $sformatf("\n data_in: \t %0b", clr_vector.data_in)};
    txt = {txt, $sformatf("\n data_iv: \t %0b", clr_vector.iv)};
    txt = {txt, $sformatf("\n data_key: \t %0b", clr_vector.key)};
    txt = {txt, $sformatf("\n vector: \t %0b", clr_vector)};
    `uvm_info(`gfn, $sformatf("%s",txt), UVM_MEDIUM)

    ral.trigger.set(0);
    ral.trigger.key_iv_data_in_clear.set(|clr_vector[2:0]);
    ral.trigger.data_out_clear.set(clr_vector.data_out);
    csr_update(ral.trigger);
  endtask // clear_registers


  virtual task prng_reseed();
    bit [TL_DW:0] reg_val = '0;
    reg_val[5] = 1'b1;
    csr_wr(.csr(ral.trigger), .value(reg_val));
  endtask // prng_reseed


  virtual task set_operation(bit operation);
    ral.ctrl_shadowed.operation.set(operation);
    csr_update(.csr(ral.ctrl_shadowed), .en_shadow_wr(1'b1), .blocking(1));
  endtask // set_operation


  virtual task set_mode(bit [5:0] mode);
    ral.ctrl_shadowed.mode.set(mode);
    csr_update(.csr(ral.ctrl_shadowed), .en_shadow_wr(1'b1), .blocking(1));
  endtask


  virtual task set_key_len(bit [2:0] key_len);
    ral.ctrl_shadowed.key_len.set(key_len);
    `uvm_info(`gfn, $sformatf("Writing Key LEN: %b", key_len), UVM_LOW)
    csr_update(.csr(ral.ctrl_shadowed), .en_shadow_wr(1'b1), .blocking(1));
  endtask


  virtual task set_manual_operation(bit manual_operation);
    ral.ctrl_shadowed.manual_operation.set(manual_operation);
    csr_update(.csr(ral.ctrl_shadowed), .en_shadow_wr(1'b1), .blocking(1));
  endtask


  virtual task write_key(bit [7:0][31:0] key [2], bit do_b2b);
    `uvm_info(`gfn, $sformatf("\n\t --- back to back transactions : %b", do_b2b), UVM_MEDIUM)
    // Share 0 (the masked key share = key ^ mask)
    csr_wr(.csr(ral.key_share0_0), .value(key[0][0]), .blocking(~do_b2b));
    csr_wr(.csr(ral.key_share0_1), .value(key[0][1]), .blocking(~do_b2b));
    csr_wr(.csr(ral.key_share0_2), .value(key[0][2]), .blocking(~do_b2b));
    csr_wr(.csr(ral.key_share0_3), .value(key[0][3]), .blocking(~do_b2b));
    csr_wr(.csr(ral.key_share0_4), .value(key[0][4]), .blocking(~do_b2b));
    csr_wr(.csr(ral.key_share0_5), .value(key[0][5]), .blocking(~do_b2b));
    csr_wr(.csr(ral.key_share0_6), .value(key[0][6]), .blocking(~do_b2b));
    csr_wr(.csr(ral.key_share0_7), .value(key[0][7]), .blocking(~do_b2b));
    // Share 1 (the mask share)
    csr_wr(.csr(ral.key_share1_0), .value(key[1][0]), .blocking(~do_b2b));
    csr_wr(.csr(ral.key_share1_1), .value(key[1][1]), .blocking(~do_b2b));
    csr_wr(.csr(ral.key_share1_2), .value(key[1][2]), .blocking(~do_b2b));
    csr_wr(.csr(ral.key_share1_3), .value(key[1][3]), .blocking(~do_b2b));
    csr_wr(.csr(ral.key_share1_4), .value(key[1][4]), .blocking(~do_b2b));
    csr_wr(.csr(ral.key_share1_5), .value(key[1][5]), .blocking(~do_b2b));
    csr_wr(.csr(ral.key_share1_6), .value(key[1][6]), .blocking(~do_b2b));
    csr_wr(.csr(ral.key_share1_7), .value(key[1][7]), .blocking(~do_b2b));
  endtask // write_key


  virtual task write_iv(bit  [3:0][31:0] iv, bit do_b2b);
    csr_wr(.csr(ral.iv_0), .value(iv[0]), .blocking(~do_b2b));
    csr_wr(.csr(ral.iv_1), .value(iv[1]), .blocking(~do_b2b));
    csr_wr(.csr(ral.iv_2), .value(iv[2]), .blocking(~do_b2b));
    csr_wr(.csr(ral.iv_3), .value(iv[3]), .blocking(~do_b2b));
  endtask


  virtual task add_data(ref bit [3:0] [31:0] data, bit do_b2b);
    int write_order[4] = {0,1,2,3};

    `uvm_info(`gfn, $sformatf("\n\t ----| ADDING DATA TO DUT %h ", data),  UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("\n\t ----| DATA_IN_0: %h ", data[0]), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("\n\t ----| DATA_IN_1: %h ", data[1]), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("\n\t ----| DATA_IN_2: %h ", data[2]), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("\n\t ----| DATA_IN_3: %h ", data[3]), UVM_HIGH)

    write_order.shuffle();
    foreach (write_order[i]) begin
      case (write_order[i])
        0: csr_wr(.csr(ral.data_in_0), .value(data[0][31:0]), .blocking(~do_b2b));
        1: csr_wr(.csr(ral.data_in_1), .value(data[1][31:0]), .blocking(~do_b2b));
        2: csr_wr(.csr(ral.data_in_2), .value(data[2][31:0]), .blocking(~do_b2b));
        3: csr_wr(.csr(ral.data_in_3), .value(data[3][31:0]), .blocking(~do_b2b));
      endcase
    end
  endtask


  virtual task read_data(ref bit [3:0] [31:0] cypher_txt, bit do_b2b);
    int read_order[4] = {0,1,2,3};
    // randomize read order
    read_order.shuffle();

    foreach (read_order[i]) begin
      case (read_order[i])
        0: csr_rd(.ptr(ral.data_out_0), .value(cypher_txt[0]), .blocking(~do_b2b));
        1: csr_rd(.ptr(ral.data_out_1), .value(cypher_txt[1]), .blocking(~do_b2b));
        2: csr_rd(.ptr(ral.data_out_2), .value(cypher_txt[2]), .blocking(~do_b2b));
        3: csr_rd(.ptr(ral.data_out_3), .value(cypher_txt[3]), .blocking(~do_b2b));
      endcase // case (read_order)
    end

    `uvm_info(`gfn, $sformatf("\n\t ----| READ OUTPUT DATA"), UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("\n\t ----| DATA FROM DUT %h ", cypher_txt), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("\n\t ----| DATA_OUT_0: %h ", cypher_txt[0][31:0]), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("\n\t ----| DATA_OUT_1: %h ", cypher_txt[1][31:0]), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("\n\t ----| DATA_OUT_2: %h ", cypher_txt[2][31:0]), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("\n\t ----| DATA_OUT_3: %h ", cypher_txt[3][31:0]), UVM_HIGH)
  endtask


  ///////////////////////////////////////
  // ADVANCED TASKS                    //
  ///////////////////////////////////////


  virtual task setup_dut(aes_seq_item item);
    //CTRL reg
    //setup one by one //
    bit setup_mode = 0;
    `DV_CHECK_STD_RANDOMIZE_FATAL(setup_mode)
    if (!setup_mode) begin
      set_operation(item.operation);
      set_mode(item.aes_mode);
      set_key_len(item.key_len);
      set_manual_operation(item.manual_op);
    end else begin
      // or write all at once //
      ral.ctrl_shadowed.operation.set(item.operation);
      ral.ctrl_shadowed.mode.set(item.mode);
      ral.ctrl_shadowed.key_len.set(item.key_len);
      ral.ctrl_shadowed.manual_operation.set(item.manual_op);
      csr_update(.csr(ral.ctrl_shadowed), .en_shadow_wr(1'b1), .blocking(1));
    end

  endtask


  virtual task generate_aes_item_queue(aes_message_item msg_item);
    // init aes item
    aes_item_init(msg_item);
    // generate DUT cfg
    generate_ctrl_item();
    generate_data_stream(msg_item);

    // TODO
    // aes_generate_err_inj();
    // TODO
    // aes_generate_rnd_rst();

    aes_print_item_queue(aes_item_queue);
  endtask

  // Generate the data for a single message based
  // on the configuration in the message Item
  virtual task generate_data_stream(aes_message_item msg_item);
    aes_seq_item item_clone;
    aes_item.item_type = AES_DATA;

    // generate an item for each 128b message block
    `uvm_info(`gfn, $sformatf("\n\t ----| FIXED DATA ENABLED? : %0b", msg_item.fixed_data_en),
              UVM_MEDIUM)
    for (int n = 0; n < msg_item.message_length - 15; n += 16) begin
      if (msg_item.fixed_data_en) begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(aes_item, data_in == msg_item.fixed_data;)
      end else begin
        `DV_CHECK_RANDOMIZE_FATAL(aes_item)
      end

      `uvm_info(`gfn, $sformatf("\n ----| DATA AES ITEM %s", aes_item.convert2string()), UVM_HIGH)
      `downcast(item_clone, aes_item.clone());
      aes_item_queue.push_front(item_clone);
    end

    // check if message length is not divisible by 16bytes
    if (msg_item.message_length[3:0] != 4'd0) begin
      `uvm_info(`gfn, $sformatf("\n ----| generating runt "), UVM_MEDIUM)
      aes_item.data_len = msg_item.message_length[3:0];
      if (msg_item.fixed_data_en) begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(aes_item, data_in == msg_item.fixed_data;)
      end else begin
        `DV_CHECK_RANDOMIZE_FATAL(aes_item)
      end
      aes_item.item_type = AES_DATA;
      `downcast(item_clone, aes_item.clone());
      aes_item_queue.push_front(item_clone);
    end
  endtask // generate_data_stream


  virtual task write_data_key_iv( aes_seq_item item,  bit [3:0] [31:0] data);
    string txt="";
    bit    is_blocking = ~item.do_b2b;
    string interleave_queue[] = '{ "key_share0_0", "key_share0_1", "key_share0_2", "key_share0_3",
                                   "key_share0_4", "key_share0_5", "key_share0_6", "key_share0_7",
                                   "key_share1_0", "key_share1_1", "key_share1_2", "key_share1_3",
                                   "key_share1_4", "key_share1_5", "key_share1_6", "key_share1_7",
                                   "data_in_0", "data_in_1", "data_in_2", "data_in_3"};

    // if non ECB mode add IV to queue
    if (item.mode != AES_ECB) begin
      interleave_queue = {"iv_0", "iv_1", "iv_2", "iv_3", interleave_queue};
    end

    if (|item.clear_reg) begin
      interleave_queue = { interleave_queue, "clear_reg"};
      `uvm_info(`gfn, $sformatf("\n\t ----| Clear reg enabled adding register clear to Queue"),
                 UVM_MEDIUM)
    end


    if (cfg.random_data_key_iv_order) begin
      int q_size = interleave_queue.size();
        interleave_queue.shuffle();
    end


    foreach (interleave_queue[i]) begin
      txt = {txt, $sformatf("\n\t ----| \t %s", interleave_queue[i]) };

      case (interleave_queue[i])
        "key_share0_0": csr_wr(.csr(ral.key_share0_0), .value(item.key[0][0]), .blocking(is_blocking));
        "key_share0_1": csr_wr(.csr(ral.key_share0_1), .value(item.key[0][1]), .blocking(is_blocking));
        "key_share0_2": csr_wr(.csr(ral.key_share0_2), .value(item.key[0][2]), .blocking(is_blocking));
        "key_share0_3": csr_wr(.csr(ral.key_share0_3), .value(item.key[0][3]), .blocking(is_blocking));
        "key_share0_4": csr_wr(.csr(ral.key_share0_4), .value(item.key[0][4]), .blocking(is_blocking));
        "key_share0_5": csr_wr(.csr(ral.key_share0_5), .value(item.key[0][5]), .blocking(is_blocking));
        "key_share0_6": csr_wr(.csr(ral.key_share0_6), .value(item.key[0][6]), .blocking(is_blocking));
        "key_share0_7": csr_wr(.csr(ral.key_share0_7), .value(item.key[0][7]), .blocking(is_blocking));

        "key_share1_0": csr_wr(.csr(ral.key_share1_0), .value(item.key[1][0]), .blocking(is_blocking));
        "key_share1_1": csr_wr(.csr(ral.key_share1_1), .value(item.key[1][1]), .blocking(is_blocking));
        "key_share1_2": csr_wr(.csr(ral.key_share1_2), .value(item.key[1][2]), .blocking(is_blocking));
        "key_share1_3": csr_wr(.csr(ral.key_share1_3), .value(item.key[1][3]), .blocking(is_blocking));
        "key_share1_4": csr_wr(.csr(ral.key_share1_4), .value(item.key[1][4]), .blocking(is_blocking));
        "key_share1_5": csr_wr(.csr(ral.key_share1_5), .value(item.key[1][5]), .blocking(is_blocking));
        "key_share1_6": csr_wr(.csr(ral.key_share1_6), .value(item.key[1][6]), .blocking(is_blocking));
        "key_share1_7": csr_wr(.csr(ral.key_share1_7), .value(item.key[1][7]), .blocking(is_blocking));

        "iv_0": csr_wr(.csr(ral.iv_0), .value(item.iv[0]), .blocking(is_blocking));
        "iv_1": csr_wr(.csr(ral.iv_1), .value(item.iv[1]), .blocking(is_blocking));
        "iv_2": csr_wr(.csr(ral.iv_2), .value(item.iv[2]), .blocking(is_blocking));
        "iv_3": csr_wr(.csr(ral.iv_3), .value(item.iv[3]), .blocking(is_blocking));

        "data_in_0": csr_wr(.csr(ral.data_in_0), .value(data[0][31:0]), .blocking(is_blocking));
        "data_in_1": csr_wr(.csr(ral.data_in_1), .value(data[1][31:0]), .blocking(is_blocking));
        "data_in_2": csr_wr(.csr(ral.data_in_2), .value(data[2][31:0]), .blocking(is_blocking));
        "data_in_3": csr_wr(.csr(ral.data_in_3), .value(data[3][31:0]), .blocking(is_blocking));

        "clear_reg": begin
          clear_regs(item.clear_reg);
          csr_spinwait(.ptr(ral.status.idle) , .exp_data(1'b1));
        end

      endcase // case interleave_queue[i]
    end
    `uvm_info(`gfn, $sformatf("\n\t ----| Configuring the DUT in the following order:  %s, \n\t data 0x%0h", txt, data),
              UVM_MEDIUM)
  endtask // write_data_key_iv


  // TODO
  // virtual task generate_err_inj(ref aes_message_item msg_item);
  // endtask

  // TODO
  // virtual task generate_rnd_rst();
  // endtask


  virtual task send_msg (
     bit manual_operation,                   // use manual operation
     bit unbalanced,                         // uses the probablilites to randomize if we read or write
     int read_prob,                          // chance of reading an availabout output
     int write_prob                          // chance of writing input data to a ready DUT
     );

    status_t     status;                     // AES status
    aes_seq_item cfg_item   = new();         // the configuration for this message
    aes_seq_item data_item  = new();         // the next data to transmit
    aes_seq_item read_item;                  // the read item to store output in
    aes_seq_item clone_item;
    bit  new_msg            = 1;             // set when starting a new msg
    aes_seq_item read_queue[$];              // queue to hold items waiting for output

    bit           read;
    bit           write;


    cfg_item = aes_item_queue.pop_back();

    // TODO when dut is updated to flag output overwritten
    // the manual operation should be included in the unbalanced =1 also
    if (new_msg) setup_dut(cfg_item);
    if (unbalanced == 0 || manual_operation) begin
      while (aes_item_queue.size() > 0) begin
        status_fsm(cfg_item, data_item, new_msg, manual_operation, 0, status);
        if (status.input_ready) begin
          data_item = aes_item_queue.pop_back();
          config_and_transmit(cfg_item, data_item, new_msg, manual_operation, 1);
          new_msg = 0;
        end else if (cfg_item.mode == AES_NONE) begin
          // just write the data - don't expect and output
          config_and_transmit(cfg_item, data_item, new_msg, manual_operation, 0);
        end
      end
    end else begin

      while ((aes_item_queue.size() > 0) || (read_queue.size() > 0)) begin
        // get the status to make sure we can provide data - but don't wait for output //
        status_fsm(cfg_item, data_item, new_msg, manual_operation, 0, status);
        read = $urandom_range(0, 100)  <= read_prob;
        write = $urandom_range(0, 100) <= write_prob;

        if (status.input_ready && (aes_item_queue.size() > 0)) begin
          `uvm_info(`gfn, $sformatf("\n send_queue_size %d", aes_item_queue.size()), UVM_MEDIUM)
          data_item = aes_item_queue.pop_back();
          config_and_transmit(cfg_item, data_item, new_msg, manual_operation, 0);
          `downcast(clone_item, data_item.clone());
          read_queue.push_back(clone_item);
          new_msg = 0;
        end
        if (status.output_valid) begin
          `uvm_info(`gfn, $sformatf("\n read_queue_size %d", read_queue.size()), UVM_MEDIUM)
          if (read_queue.size() > 0)  begin
            read_item = read_queue.pop_front();
            read_data(read_item.data_out, cfg_item.do_b2b);
          end else begin
            `uvm_fatal(`gfn, $sformatf("\n\t ----| DATA READY but no ITEM to add it to! |----"))
          end
        end
      end
    end
  endtask // send_msg


  ////////////////////////////////////////////////////////////////////////////////////////////
  // this task will handle setup and transmition
  // of a message on a block level.
  // it will send one block then return to the caller for the next item.
  // if read output is enabled it will call the status fsm for get the
  // output of the processed block
  // NOTE IT IS UP TO THE CALLER OF THIS TASK
  // TO ENSURE THE DUT IS READY/IDLE
  // this opens up for calling this task in random times
  // to provoke weird behavior
  ////////////////////////////////////////////////////////////////////////////////////////////

  virtual task config_and_transmit (
      aes_seq_item cfg_item,         // sequence item with configuraton
      aes_seq_item data_item,        // sequence item with data to process
      bit          new_msg,          // is this a new msg -> do dut config
      bit          manual_operation, // use manual operation
      bit          read_output       // read output or leave untouched
      );

    status_t              status;
    bit                   is_blocking = cfg_item.do_b2b;

    if (new_msg) begin
      write_data_key_iv(cfg_item, data_item.data_in);
    end else begin
      add_data(data_item.data_in, is_blocking);
    end
    if (manual_operation) trigger();

    if (read_output) status_fsm(cfg_item, data_item, new_msg, manual_operation, read_output, status);
  endtask // config_and_transmit


  ////////////////////////////////////////////////////////////////////////////////////////////
  // the status fsm has two tasks
  // 1 determine the status of the DUT
  //   it will recover from any configurational deadlock
  //   i.e update error / clear error / misconfiguration or missing configuration
  // 2. if wanted it will read output data when ready and return it to the caller
  //
  // the task operates on block level
  ////////////////////////////////////////////////////////////////////////////////////////////

  virtual task status_fsm (
      aes_seq_item        cfg_item,         // sequence item with configuraton
      aes_seq_item        data_item,        // sequence item with data to process
      bit                 new_msg,          // is this a new msg -> do dut config
      bit                 manual_operation, // use manual operation
      bit                 read_output,      // read output or leave untouched
      ref    status_t     status            // the current AES status
      );

    ctrl_reg_t ctrl;
    bit                   is_blocking = ~cfg_item.do_b2b;
    bit                   done        = 0;
    string                txt         = "";

    // enable get status when provided with an empty Item.
    if (data_item.mode === 'X) begin
      csr_rd(.ptr(ral.status), .value(status), .blocking(is_blocking));
    end


    while(!done && (data_item.mode != AES_NONE)) begin
      //read the status register to see that we have triggered the operation
      csr_rd(.ptr(ral.status), .value(status), .blocking(is_blocking));
      // check status and act accordingly //
      if (status.alert_fatal_fault) begin
        // stuck pull reset //
      end else begin
        // state 0
        if (status.idle && status.input_ready) begin
          if (status.output_valid && read_output) begin
            read_data(data_item.data_out, is_blocking);
            txt = {txt, $sformatf("\n\t ----| status state 0 ")};
          end
          done = 1;

        end else if (status.idle && !status.input_ready) begin
          // state 1 //
          // if data ready just read and return
          if (status.output_valid && read_output) begin
            read_data(data_item.data_out, is_blocking);
            done = 1;
          end else begin
            // if data is not ready the DUT is missing
            // KEY and IV - or the configuration
            csr_rd(.ptr(ral.ctrl_shadowed), .value(ctrl), .blocking(is_blocking));
            ral.ctrl_shadowed.operation.set(cfg_item.operation);
            ral.ctrl_shadowed.mode.set(cfg_item.mode);
            ral.ctrl_shadowed.key_len.set(cfg_item.key_len);
            ral.ctrl_shadowed.manual_operation.set(cfg_item.manual_op);

            if (ral.ctrl_shadowed.get_mirrored_value() != ctrl) begin
              `uvm_info(`gfn, $sformatf("\n\t ----| configuration does not match actual - re-confguring"), UVM_LOW)
              txt = { txt, $sformatf("\n\t ----| configuration does not match actual - re-confguring")};
              csr_update(.csr(ral.ctrl_shadowed), .en_shadow_wr(1'b1), .blocking(is_blocking));
            end else begin
              // key and IV missing clear all and rewrite (a soon to come update will merge
              // the clear options into a single bit)
              clear_regs(4'b1111);
              // wait for idle
              csr_spinwait(.ptr(ral.status.idle) , .exp_data(1'b1));
              write_key(cfg_item.key, is_blocking);
              write_iv(cfg_item.iv, is_blocking);
              add_data(data_item.data_in, is_blocking);
              if (manual_operation) trigger();
            end
            txt = {txt, $sformatf("\n\t ----| status state 1 ")};
          end

        end else if (status.output_valid) begin
          // state 2 //
          // data ready to be read out
          // read or return
          done = 1;
          if (read_output) begin
            read_data(data_item.data_out, is_blocking);
            txt = {txt, $sformatf("\n\t ----| status state 2 ")};
          end


        end else if ( !(status.idle || status.stall || status.output_valid)) begin
          // state 3 //
          // if not ready for input and no output ready should only occur after reset
          if (!status.input_ready) begin
          end
          // else DUT is in operation wait for new output
          txt = {txt, $sformatf("\n\t ----| status state 3 ")};


        end else begin
          txt = {txt, $sformatf("\n ----| STATUS RETURNED ILLEGAL STATE |---- ")};
          txt = {txt, $sformatf("\n ----| IDLE %0b",status.idle)};
          txt = {txt, $sformatf("\n ----| STALL %0b",status.stall)};
          txt = {txt, $sformatf("\n ----| INPUT_READY %0b",status.input_ready)};
          txt = {txt, $sformatf("\n ----| OUTPUT_VALID %0b",status.output_valid)};
          `uvm_fatal(`gfn, $sformatf("\n\t %s",txt))
        end
        `uvm_info(`gfn, $sformatf("\n\t %s",txt), UVM_MEDIUM)
      end // else: !if(status.alert_fatal_fault)
    end // while (!done)

  endtask // transmit_fsm


  virtual task send_msg_queue (
     bit unbalanced,                         // uses the probablilites to randomize if we read or write
     int read_prob,                          // chance of reading an availabout output
     int write_prob                          // chance of writing input data to a ready DUT
     );
    // variables
    aes_message_item my_message;

     while (message_queue.size() > 0) begin
      my_message = new();
      my_message = message_queue.pop_back();
      generate_aes_item_queue(my_message);
      send_msg(my_message.manual_operation, unbalanced, read_prob, write_prob);
     end

  endtask // send_msg_queue


  ///////////////////////////////////////////////////////////
  ///////////////        FUNCTIONS       ////////////////////
  ///////////////////////////////////////////////////////////

  // initialize the global sequence item
  // with values from the message item (happens once per message item
  function void aes_item_init(aes_message_item message_item);

    aes_item = new();
    aes_item.operation        = message_item.aes_operation;
    aes_item.mode             = message_item.aes_mode;
    aes_item.key_len          = message_item.aes_keylen;
    aes_item.key              = message_item.aes_key;
    aes_item.iv               = message_item.aes_iv;
    aes_item.manual_op        = message_item.manual_operation;
    aes_item.key_mask         = message_item.keymask;
    aes_item.clear_reg_pct    = cfg.clear_reg_pct;
    aes_item.clear_reg_w_rand = cfg.clear_reg_w_rand;
  endfunction // aes_item_init


  function void generate_ctrl_item();
    aes_seq_item item_clone;

    aes_item.item_type = AES_CFG;

    `DV_CHECK_RANDOMIZE_FATAL(aes_item)
    `uvm_info(`gfn, $sformatf("\n\t ----| CONFIG  AES ITEM %s", aes_item.convert2string()), UVM_HIGH)

    `downcast(item_clone, aes_item.clone());
    aes_item_queue.push_front(item_clone);
  endfunction


  // init the first message - following will rerandomize with the same constraints
  function void aes_message_init();
    aes_message = new();
    aes_message.ecb_weight           = cfg.ecb_weight;
    aes_message.cbc_weight           = cfg.cbc_weight;
    aes_message.ofb_weight           = cfg.ofb_weight;
    aes_message.cfb_weight           = cfg.cfb_weight;
    aes_message.ctr_weight           = cfg.ctr_weight;
    aes_message.key_128b_weight      = cfg.key_128b_weight;
    aes_message.key_192b_weight      = cfg.key_192b_weight;
    aes_message.key_256b_weight      = cfg.key_256b_weight;
    aes_message.message_len_max      = cfg.message_len_max;
    aes_message.message_len_min      = cfg.message_len_min;
    aes_message.config_error_pct     = cfg.config_error_pct;
    aes_message.error_types          = cfg.error_types;
    aes_message.manual_operation_pct = cfg.manual_operation_pct;
    aes_message.keymask              = cfg.key_mask;
    aes_message.fixed_key_en         = cfg.fixed_key_en;
    aes_message.fixed_data_en        = cfg.fixed_data_en;
    aes_message.fixed_operation_en   = cfg.fixed_operation_en;
    aes_message.fixed_operation      = cfg.fixed_operation;
    aes_message.fixed_keylen_en      = cfg.fixed_keylen_en;
    aes_message.fixed_keylen         = cfg.fixed_keylen;
    aes_message.fixed_iv_en          = cfg.fixed_iv_en;
  endfunction


  function void generate_message_queue();
    aes_message_item cloned_message;
    for (int i=0; i < cfg.num_messages; i++) begin
      `DV_CHECK_RANDOMIZE_FATAL(aes_message)
      if (aes_message.cfg_error_type[0] == 1'b1) cfg.num_corrupt_messages += 1;
      `downcast(cloned_message, aes_message.clone());
      message_queue.push_front(cloned_message);
      `uvm_info(`gfn, $sformatf("\n\t ----| MESSAGE # %d \n %s",i, cloned_message.convert2string())
               , UVM_MEDIUM)
    end
  endfunction // generate_message_queue


  function void aes_print_item_queue(aes_seq_item item_queue[$]);
    aes_seq_item print_item;
    `uvm_info(`gfn, $sformatf("----| Item queue size: %d", item_queue.size()), UVM_HIGH)
    for (int n = 0; n < item_queue.size(); n++) begin
      print_item = item_queue[n];
      `uvm_info(`gfn, $sformatf("----|  ITEM #%d", n ), UVM_MEDIUM)
      `uvm_info(`gfn, $sformatf("%s", print_item.convert2string()), UVM_MEDIUM)
    end
  endfunction // aes_print_item_queue
endclass : aes_base_vseq
