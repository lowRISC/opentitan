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
  endtask

  virtual task dut_shutdown();
    // check for pending aes operations and wait for them to complete
    // TODO
  endtask

  // setup basic aes features
  virtual task aes_init();

    bit [31:0] aes_ctrl    = '0;
    bit [31:0] aes_trigger = '0;

    // initialize control register
    aes_ctrl[0]    = 0;        // set to encryption
    aes_ctrl[3:1] = aes_pkg::AES_ECB;   //3'b001;   // set to ECB MODE
    aes_ctrl[6:4]  = aes_pkg::AES_128;   // set to 128b key
    csr_wr(.csr(ral.ctrl), .value(aes_ctrl));
    csr_wr(.csr(ral.trigger), .value(aes_trigger));
  endtask


  virtual task set_operation(bit operation);
    ral.ctrl.operation.set(operation);
    csr_update(.csr(ral.ctrl));
  endtask // set_operation


  virtual task set_mode(bit [2:0] mode);
    ral.ctrl.mode.set(mode);
    csr_update(.csr(ral.ctrl));
  endtask


  virtual task set_key_len(bit [2:0] key_len);
    ral.ctrl.key_len.set(key_len);
    csr_update(.csr(ral.ctrl));
  endtask


  virtual task set_manual_operation(bit manual_operation);
    ral.ctrl.manual_operation.set(manual_operation);
    csr_update(.csr(ral.ctrl));
  endtask


  virtual task write_key(bit  [7:0][31:0] key);
    csr_wr(.csr(ral.key0), .value(key[0]));
    csr_wr(.csr(ral.key1), .value(key[1]));
    csr_wr(.csr(ral.key2), .value(key[2]));
    csr_wr(.csr(ral.key3), .value(key[3]));
    csr_wr(.csr(ral.key4), .value(key[4]));
    csr_wr(.csr(ral.key5), .value(key[5]));
    csr_wr(.csr(ral.key6), .value(key[6]));
    csr_wr(.csr(ral.key7), .value(key[7]));
  endtask // write_key


  virtual task write_iv(bit  [3:0][31:0] iv);
    csr_wr(.csr(ral.iv0), .value(iv[0]));
    csr_wr(.csr(ral.iv1), .value(iv[1]));
    csr_wr(.csr(ral.iv2), .value(iv[2]));
    csr_wr(.csr(ral.iv3), .value(iv[3]));
  endtask


  virtual task add_data(ref bit [3:0] [31:0] data);
    `uvm_info(`gfn, $sformatf("\n\t ----| ADDING DATA TO DUT %h ", data), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("\n\t ----| DATA_in0: %h ", data[0][31:0]), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("\n\t ----| DATA_in1: %h ", data[1][31:0]), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("\n\t ----| DATA_in2: %h ", data[2][31:0]), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("\n\t ----| DATA_in3: %h ", data[3][31:0]), UVM_HIGH)     
    csr_wr(.csr(ral.data_in0), .value(data[0][31:0]) );
    csr_wr(.csr(ral.data_in1), .value(data[1][31:0]) );
    csr_wr(.csr(ral.data_in2), .value(data[2][31:0]) );
    csr_wr(.csr(ral.data_in3), .value(data[3][31:0]) );
  endtask


  ///////////////////////////////////////
  // ADVANCED TASKS                    //
  ///////////////////////////////////////

  virtual task read_data(ref bit [3:0] [31:0] cypher_txt);
    bit [3:0] [31:0] rd_txt;

    `uvm_info(`gfn, $sformatf("\n\t ----| POLLING FOR DATA"), UVM_DEBUG)
    csr_spinwait(.ptr(ral.status.output_valid) , .exp_data(1'b1));    // poll for data valid

    csr_rd(.ptr(ral.data_out0), .value(cypher_txt[0][31:0]));
    csr_rd(.ptr(ral.data_out1), .value(cypher_txt[1][31:0]));
    csr_rd(.ptr(ral.data_out2), .value(cypher_txt[2][31:0]));
    csr_rd(.ptr(ral.data_out3), .value(cypher_txt[3][31:0]));

    `uvm_info(`gfn, $sformatf("\n\t ----| READ OUPUT DATA"), UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("\n\t ----| ADDING DATA TO DUT %h ", cypher_txt),  UVM_HIGH)
    `uvm_info(`gfn, $sformatf("\n\t ----| DATA_out0: %h ", cypher_txt[0][31:0]), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("\n\t ----| DATA_out1: %h ", cypher_txt[1][31:0]), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("\n\t ----| DATA_out2: %h ", cypher_txt[2][31:0]), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("\n\t ----| DATA_out3: %h ", cypher_txt[3][31:0]), UVM_HIGH)       
  endtask


  virtual task setup_dut(aes_seq_item item);
    set_operation(item.operation);
    set_mode(item.mode);
    set_key_len(item.key_len);
    write_key(item.key);
    write_iv(item.iv);
  endtask


  // TODO add missing functions
  virtual task generate_aes_item_queue(ref aes_message_item msg_item);
    aes_seq_item item_clone;

    // generate DUT cfg
    aes_ctrl_item_init(msg_item);
    generate_data_stream(msg_item);

    // aes_generate_err_inj();

    // aes_generate_rnd_rst();

    aes_print_item_queue(aes_item_queue);
  endtask


  virtual task generate_data_stream(ref aes_message_item msg_item);
    aes_seq_item item_clone;

    // generate an item for each 128b message block
    for (int n=0; n<msg_item.message_length - 15; n += 16 ) begin
      `DV_CHECK_RANDOMIZE_FATAL(aes_item)
      aes_item.item_type = AES_DATA;
      `uvm_info(`gfn, $sformatf("\n ----| DATA AES ITEM %s", aes_item.convert2string()), UVM_FULL)
      `downcast(item_clone, aes_item.clone());
      aes_item_queue.push_front(item_clone);
      `uvm_info(`gfn, $sformatf("\n ----| generating data item %d", n), UVM_MEDIUM)
    end

    // check if message length is not divisible by 16bytes
    if( msg_item.message_length[3:0] != 4'd0) begin
      `uvm_info(`gfn, $sformatf("\n ----| generating runt "), UVM_MEDIUM)
      aes_item.data_len = msg_item.message_length[3:0];
      `DV_CHECK_RANDOMIZE_FATAL(aes_item)
      aes_item.item_type = AES_DATA;
      `downcast(item_clone, aes_item.clone());
      aes_item_queue.push_front(item_clone);
    end
  endtask


  // TODO
  // virtual task generate_err_inj(ref aes_message_item msg_item);
  // endtask

  // TODO
  // virtual task generate_rnd_rst();
  // endtask


  // this function starst the transmission of items to the dut,
  // while at the same time offloads the output when ready
  virtual task transmit_message_with_rd_back();
    aes_seq_item nxt_item = new();
    nxt_item = aes_item_queue.pop_back();
    setup_dut(aes_item);

    while(aes_item_queue.size() > 0) begin
      nxt_item = aes_item_queue.pop_back();
      add_data(nxt_item.data_in);
      read_data(nxt_item.data_out);
    end

  endtask // transmit_message_with_rd_back


  // TODO think about how to randomize error objects vs normal that
  // are not randomized at this level!
  function void aes_ctrl_item_init(ref aes_message_item message_item);
    aes_seq_item item_clone;
    aes_item = new();

    `uvm_info(`gfn, $sformatf("\n Generating configuration item for message of size %d", message_item.message_length), UVM_MEDIUM)
    `uvm_info(`gfn, $sformatf("\n Message \n %s", message_item.convert2string()), UVM_MEDIUM)

    aes_item.item_type = AES_CFG;
    aes_item.operation = message_item.aes_operation;
    aes_item.mode      = message_item.aes_mode;
    aes_item.key_len   = message_item.aes_keylen;
    aes_item.key       = message_item.aes_key;
    `uvm_info(`gfn, $sformatf("----| CONFIG  AES ITEM %s", aes_item.convert2string()), UVM_MEDIUM)

    `downcast(item_clone, aes_item.clone());
    aes_item_queue.push_front(item_clone);
  endfunction


  // init the first message - following will rerandomize with the same constraints
  function void aes_message_init();
    aes_message = new();
    aes_message.ecb_weight        = cfg.ecb_weight;
    aes_message.cbc_weight        = cfg.cbc_weight;
    aes_message.ctr_weight        = cfg.ctr_weight;
    aes_message.key_128b_weight   = cfg.key_128b_weight;
    aes_message.key_192b_weight   = cfg.key_192b_weight;
    aes_message.key_256b_weight   = cfg.key_256b_weight;
    aes_message.message_len_max   = cfg.message_len_max;
    aes_message.message_len_min   = cfg.message_len_min;
    aes_message.config_error_pct  = cfg.config_error_pct;
    aes_message.errors_en         = cfg.errors_en;
  endfunction


  function void generate_message_queue();
    aes_message_item cloned_message;
    for(int i=0; i < cfg.num_messages; i++) begin
      `DV_CHECK_RANDOMIZE_FATAL(aes_message)
      `downcast(cloned_message, aes_message.clone());
      //`assert($cast(cloned_message, aes_message.clone());
      message_queue.push_front(cloned_message);
      `uvm_info(`gfn, $sformatf("\n message # %d \n %s",i, cloned_message.convert2string()), UVM_MEDIUM)
    end
  endfunction


  function void aes_print_item_queue(ref aes_seq_item item_queue[$]);
    aes_seq_item print_item;
    `uvm_info(`gfn, $sformatf("----| Item queue size: %d", item_queue.size()), UVM_MEDIUM)
    for(int n = 0; n<item_queue.size(); n++) begin
      print_item = item_queue[n];
      `uvm_info(`gfn, $sformatf("----|  ITEM #%d", n ), UVM_MEDIUM)
      `uvm_info(`gfn, $sformatf("%s", print_item.convert2string()), UVM_MEDIUM)
    end
  endfunction
endclass : aes_base_vseq
