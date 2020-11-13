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
    aes_ctrl[0]    = 0;        // set to encryption
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
    reg_val[4:1] = clr_vector;
    csr_wr(.csr(ral.trigger), .value(reg_val));
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
    set_operation(item.operation);
    set_mode(item.aes_mode);
    set_key_len(item.key_len);
    set_manual_operation(item.manual_op);
  endtask


  virtual task generate_aes_item_queue(ref aes_message_item msg_item);

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


  virtual task generate_data_stream(ref aes_message_item msg_item);
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
      `uvm_info(`gfn, $sformatf("\n ----| generating data item %d", n), UVM_MEDIUM)
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


    if (cfg.random_data_key_iv_order) interleave_queue.shuffle();

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

        "data_in_0": csr_wr(.csr(ral.data_in_0), .value(item.data_in[0][31:0]), .blocking(is_blocking));
        "data_in_1": csr_wr(.csr(ral.data_in_1), .value(item.data_in[1][31:0]), .blocking(is_blocking));
        "data_in_2": csr_wr(.csr(ral.data_in_2), .value(item.data_in[2][31:0]), .blocking(is_blocking));
        "data_in_3": csr_wr(.csr(ral.data_in_3), .value(item.data_in[3][31:0]), .blocking(is_blocking));

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


  // This function starts an operation and waits for the result of a block
  // before proceeding with the next block
  virtual task transmit_message_with_rd_back();
    aes_seq_item nxt_item = new();
    aes_seq_item last_item = new();
    nxt_item = aes_item_queue.pop_back();
    setup_dut(nxt_item);

    last_item = nxt_item;
    nxt_item = aes_item_queue.pop_back();
    write_data_key_iv(last_item, nxt_item.data_in);
    if (nxt_item.mode != AES_NONE) begin
      csr_spinwait(.ptr(ral.status.output_valid) , .exp_data(1'b1));    // poll for data valid
      read_data(nxt_item.data_out, nxt_item.do_b2b);
    end

    while (aes_item_queue.size() > 0) begin
      nxt_item = aes_item_queue.pop_back();
      add_data(nxt_item.data_in, nxt_item.do_b2b);
      if (nxt_item.mode != AES_NONE) begin
        `uvm_info(`gfn, $sformatf("\n\t ----| POLLING FOR DATA"), UVM_DEBUG)
        csr_spinwait(.ptr(ral.status.output_valid) , .exp_data(1'b1));    // poll for data valid
        read_data(nxt_item.data_out, nxt_item.do_b2b);
      end
    end

  endtask // transmit_message_with_rd_back

  // transmits data as fast as input ready is set
  // readback happens with random delay
  virtual task transmit_message_with_rand_rd_back();
   // TODO

  endtask // transmit_message_with_rxd_back


  // Transmit using manual mode of operation
  // if errors are enabled it will overwrite output
  // for some blocks (not read the output)
  virtual task transmit_message_manual_op();
    aes_seq_item nxt_item   = new();
    aes_seq_item last_item  = new();
    logic [31:0] status     = 32'd0;
    bit   [31:0] num_blocks = 0;

    if (aes_item_queue.size() < 1) begin
      `uvm_fatal(`gfn, $sformatf("\n\t -| TRYING TO READ FROM AN EMPTY QUEUE |-"))
    end
    num_blocks = aes_item_queue.size() - 1;  // subtract cfg item
    nxt_item   = aes_item_queue.pop_back();

    setup_dut(nxt_item);
    `uvm_info(`gfn, $sformatf("\n\t ....| STARTING MANUAL OPERATION |...."), UVM_MEDIUM)

    last_item   = nxt_item;
    nxt_item    = aes_item_queue.pop_back();
    write_data_key_iv(last_item, nxt_item.data_in);
    trigger();

    while (num_blocks > 0) begin // until all block has been processed and read out
      `uvm_info(`gfn, $sformatf("\n\t ....| missing output from %d blocks |....",num_blocks),
               UVM_MEDIUM)

      csr_rd(.ptr(ral.status), .value(status));
      `uvm_info(`gfn, $sformatf("\n\t ....| POLLED STATUS %h |....",status), UVM_MEDIUM)
      `uvm_info(`gfn, $sformatf("\n\t ....| blocks left in message %d |....",aes_item_queue.size()),
               UVM_MEDIUM)
      // If the DUT is ready new input and also has new output
      // this will produce the two request at the same time
      // and leave it to the sequencer to arbritrate
      // hence randomizing the order
      fork
        begin : write_next_block
           if (status[3] &&  (aes_item_queue.size() >0 )) begin
             nxt_item = aes_item_queue.pop_back();
             add_data(nxt_item.data_in, nxt_item.do_b2b);
             trigger();
           end
        end

        begin : read_output
          if (status[2]) begin
            read_data(nxt_item.data_out, nxt_item.do_b2b);
            num_blocks -= 1;
          end
        end
      join
    end
  endtask // transmit_message_with_rd_back


  virtual task transmit_message_manual_op_w_rd_back();
    aes_seq_item nxt_item   = new();
    aes_seq_item last_item  = new();
    logic [31:0] status     = 32'd0;
    bit [31:0]   num_blocks = 0;

    if (aes_item_queue.size() < 1) begin
      `uvm_fatal(`gfn, $sformatf("\n\t -| TRYING TO READ FROM AN EMPTY QUEUE |-"))
    end
    num_blocks = aes_item_queue.size() -1;  // subtract cfg item
    nxt_item   = aes_item_queue.pop_back();

    setup_dut(nxt_item);
    `uvm_info(`gfn, $sformatf("\n\t ....| STARTING MANUAL OPERATION |...."), UVM_MEDIUM)

    last_item   = nxt_item;
    nxt_item    = aes_item_queue.pop_back();
    num_blocks -= 1;
    write_data_key_iv(last_item, nxt_item.data_in);
    trigger();
    csr_spinwait(.ptr(ral.status.output_valid) , .exp_data(1'b1));    // poll for data valid
    read_data(nxt_item.data_out, nxt_item.do_b2b);

    while (num_blocks > 0) begin // until all block has been processed and read out
      `uvm_info(`gfn, $sformatf("\n\t ....| missing output from %d blocks |....",num_blocks),
                UVM_MEDIUM)

      csr_spinwait(.ptr(ral.status.input_ready) , .exp_data(1'b1));
      `uvm_info(`gfn, $sformatf("\n\t ....| POLLED STATUS %h |....",status), UVM_MEDIUM)
      `uvm_info(`gfn, $sformatf("\n\t ....| blocks left in message %d |....",aes_item_queue.size()),
                UVM_MEDIUM)

      nxt_item = aes_item_queue.pop_back();
      add_data(nxt_item.data_in, nxt_item.do_b2b);
      trigger();

      csr_spinwait(.ptr(ral.status.output_valid) , .exp_data(1'b1));    // poll for data valid
      read_data(nxt_item.data_out, nxt_item.do_b2b);
      num_blocks -= 1;
    end
  endtask // trasnmist_message_manual_op_w_rd_back


  ///////////////////////////////////////////////////////////
  ///////////////        FUNCTIONS       ////////////////////
  ///////////////////////////////////////////////////////////

  // initialize the global sequence item
  // with values from the message item (happens once per message item
  function void aes_item_init(ref aes_message_item message_item);

    aes_item = new();
    aes_item.operation        = message_item.aes_operation;
    aes_item.mode             = message_item.aes_mode;
    aes_item.key_len          = message_item.aes_keylen;
    aes_item.key              = message_item.aes_key;
    aes_item.iv               = message_item.aes_iv;
    aes_item.manual_op        = message_item.manual_operation;
    aes_item.key_mask         = message_item.keymask;
    aes_item.clear_reg_pct = cfg.clear_reg_pct;
    aes_item.clear_reg_w_rand = cfg.clear_reg_w_rand;
  endfunction // aes_item_init


  // TODO think about how to randomize error objects vs normal that
  // are not randomized at this level!
  function void generate_ctrl_item();
    aes_seq_item item_clone;

    aes_item.item_type = AES_CFG;

    `DV_CHECK_RANDOMIZE_FATAL(aes_item)
    `uvm_info(`gfn, $sformatf("\n\t ----| CONFIG  AES ITEM %s", aes_item.convert2string()), UVM_FULL)

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
      //`assert($cast(cloned_message, aes_message.clone());
      message_queue.push_front(cloned_message);
      `uvm_info(`gfn, $sformatf("\n\t ----| MESSAGE # %d \n %s",i, cloned_message.convert2string())
               , UVM_MEDIUM)
    end
  endfunction


  function void aes_print_item_queue(ref aes_seq_item item_queue[$]);
    aes_seq_item print_item;
    `uvm_info(`gfn, $sformatf("----| Item queue size: %d", item_queue.size()), UVM_HIGH)
    for (int n = 0; n < item_queue.size(); n++) begin
      print_item = item_queue[n];
      `uvm_info(`gfn, $sformatf("----|  ITEM #%d", n ), UVM_MEDIUM)
      `uvm_info(`gfn, $sformatf("%s", print_item.convert2string()), UVM_MEDIUM)
    end
  endfunction // aes_print_item_queue
endclass : aes_base_vseq
