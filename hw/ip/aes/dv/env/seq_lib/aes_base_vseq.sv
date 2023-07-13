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
  key_sideload_set_seq sideload_seq, req_key_seq;


  // various knobs to enable certain routines
  bit                do_aes_init   = 1'b1;
  bit                global_reset  = 1'b0;


  // handshake with key manager
  bit                key_used      = 0;
  bit                key_rdy       = 0;
  bit                new_key       = 0;

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();

    if (do_aes_init) aes_init();
    aes_item = new();
    aes_message_init();
    `uvm_info(`gfn, $sformatf("\n TL delay: [%d:%d] \n zero delay %d",
              cfg.m_tl_agent_cfg.d_ready_delay_min,cfg.m_tl_agent_cfg.d_ready_delay_max,
              cfg.zero_delays  ), UVM_MEDIUM)
  endtask


  virtual task aes_reset(string kind = "HARD");
    global_reset = 1;
    wait(global_reset == 0); // make seq is ready for rest
    apply_reset(kind);
    #1ps; // workaround for race condition in dv_lib
    wait(!cfg.clk_rst_vif.rst_n); // under reset will not work here..
    wait(cfg.clk_rst_vif.rst_n);
  endtask // aes_reset


  // setup basic aes features
  virtual task aes_init();
    bit [31:0] aes_ctrl = '0;
    bit [31:0] aes_ctrl_aux = '0;
    bit [31:0] aes_trigger = '0;
    // Lock and check locking of auxiliary control register (1) or not (0).
    bit lock_ctrl_aux = $urandom_range(0, 1);
    `uvm_info(`gfn, $sformatf("\n\t ----| CHECKING FOR IDLE"), UVM_HIGH)
    csr_spinwait(.ptr(ral.status.idle) , .exp_data(1'b1));
    // initialize control register
    aes_ctrl[1:0]  = aes_pkg::AES_ENC;   // 2'b01
    aes_ctrl[7:2]  = aes_pkg::AES_ECB;   // 6'b00_0001
    aes_ctrl[10:8] = aes_pkg::AES_128;   // 3'b001
    csr_wr(.ptr(ral.ctrl_shadowed), .value(aes_ctrl), .en_shadow_wr(1'b1), .blocking(1));
    // Write auxiliary control register and make sure the update went through, i.e., the register
    // isn't locked already.
    csr_wr(.ptr(ral.ctrl_aux_shadowed.key_touch_forces_reseed), .value(cfg.do_reseed),
        .en_shadow_wr(1'b1), .blocking(1));
    csr_rd(.ptr(ral.ctrl_aux_shadowed), .value(aes_ctrl_aux), .blocking(1));
    `DV_CHECK_FATAL(aes_ctrl_aux[0] == cfg.do_reseed);
    // Lock auxiliary control register and try overwriting it afterwards.
    if (lock_ctrl_aux) begin
      `uvm_info(`gfn, "Locking auxiliary control register", UVM_MEDIUM)
      set_regwen(0);
      `uvm_info(`gfn, "Try overwriting locked auxiliary control register", UVM_MEDIUM)
      csr_wr(.ptr(ral.ctrl_aux_shadowed.key_touch_forces_reseed), .value(!cfg.do_reseed),
          .en_shadow_wr(1'b1), .blocking(1));
      // Read the current value back to ensure the contents of the register didn't change.
      csr_rd(.ptr(ral.ctrl_aux_shadowed), .value(aes_ctrl_aux), .blocking(1));
      `DV_CHECK_FATAL(aes_ctrl_aux[0] == cfg.do_reseed);
      // Try unlocking the auxiliary control register and overwriting it afterwards. This is not
      // possible either as the lock persists until the next reset.
      set_regwen(1);
      csr_wr(.ptr(ral.ctrl_aux_shadowed.key_touch_forces_reseed), .value(!cfg.do_reseed),
          .en_shadow_wr(1'b1), .blocking(1));
      csr_rd(.ptr(ral.ctrl_aux_shadowed), .value(aes_ctrl_aux), .blocking(1));
      `DV_CHECK_FATAL(aes_ctrl_aux[0] == cfg.do_reseed);
    end else begin
      // Don't lock it. This is the default value after reset. The write is mostly for coverage.
      set_regwen(1);
    end
  endtask // aes_init


  virtual task trigger();
      csr_wr(.ptr(ral.trigger), .value(32'h00000001));
  endtask // trigger


  virtual task clear_regs(clear_t clr_vector);
    string txt="";
    bit [TL_DW:0] reg_val = '0;
    txt = {txt, $sformatf("\n data_out: \t %0b", clr_vector.dataout)};
    txt = {txt, $sformatf("\n key_iv_data_in: \t %0b", clr_vector.key_iv_data_in)};
    txt = {txt, $sformatf("\n vector: \t %0b", clr_vector)};
    `uvm_info(`gfn, $sformatf("%s",txt), UVM_MEDIUM)

    ral.trigger.set(0);
    ral.trigger.key_iv_data_in_clear.set(clr_vector.key_iv_data_in);
    ral.trigger.data_out_clear.set(clr_vector.dataout);
    csr_update(ral.trigger);
  endtask // clear_registers


  virtual task prng_reseed();
    bit [TL_DW:0] reg_val = '0;
    reg_val[3] = 1'b1;
    csr_wr(.ptr(ral.trigger), .value(reg_val));
  endtask // prng_reseed


  virtual task set_regwen(bit val);
    ral.ctrl_aux_regwen.set(val);
    csr_wr(.ptr(ral.ctrl_aux_regwen), .value(val), .blocking(1));
  endtask // set_regwen


  virtual task set_operation(bit [1:0] operation);
      ral.ctrl_shadowed.operation.set(operation);
      csr_update(.csr(ral.ctrl_shadowed), .en_shadow_wr(1'b1), .blocking(1));
  endtask // set_operation


  virtual task set_mode(bit [5:0] mode);
    if (ral.ctrl_shadowed.mode.get_mirrored_value() != mode) begin
      ral.ctrl_shadowed.mode.set(mode);
      csr_update(.csr(ral.ctrl_shadowed), .en_shadow_wr(1'b1), .blocking(1));
    end
  endtask


  virtual task set_key_len(bit [2:0] key_len);
    if (ral.ctrl_shadowed.key_len.get_mirrored_value() != key_len) begin
      ral.ctrl_shadowed.key_len.set(key_len);
      csr_update(.csr(ral.ctrl_shadowed), .en_shadow_wr(1'b1), .blocking(1));
    end
  endtask // set_key_len


  virtual task set_sideload(bit sideload);
    if (ral.ctrl_shadowed.sideload.get_mirrored_value() != sideload) begin
      ral.ctrl_shadowed.sideload.set(sideload);
      csr_update(.csr(ral.ctrl_shadowed), .en_shadow_wr(1'b1), .blocking(1));
    end
  endtask


  virtual task set_prng_reseed_rate(prs_rate_e reseed_rate);
    if (ral.ctrl_shadowed.prng_reseed_rate.get_mirrored_value() != reseed_rate) begin
      ral.ctrl_shadowed.prng_reseed_rate.set(reseed_rate);
      csr_update(.csr(ral.ctrl_shadowed), .en_shadow_wr(1'b1), .blocking(1));
    end
  endtask


  virtual task set_manual_operation(bit manual_operation);
    if (ral.ctrl_shadowed.manual_operation.get_mirrored_value() != manual_operation) begin
      ral.ctrl_shadowed.manual_operation.set(manual_operation);
      csr_update(.csr(ral.ctrl_shadowed), .en_shadow_wr(1'b1), .blocking(1));
    end
  endtask


  virtual task write_key(bit [7:0][31:0] key [2], bit do_b2b);
    `uvm_info(`gfn, $sformatf("\n\t --- back to back transactions : %b", do_b2b), UVM_MEDIUM)
    // Share 0/1 (the masked key share = key ^ mask)
    foreach (key[0][i]) csr_wr(.ptr(ral.key_share0[i]), .value(key[0][i]), .blocking(~do_b2b));
    foreach (key[1][i]) csr_wr(.ptr(ral.key_share1[i]), .value(key[1][i]), .blocking(~do_b2b));
  endtask // write_key


  virtual task write_iv(bit  [3:0][31:0] iv, bit do_b2b);
    foreach (iv[i]) csr_wr(.ptr(ral.iv[i]), .value(iv[i]), .blocking(~do_b2b));
  endtask // write_iv


  virtual task read_iv(ref bit [3:0] [31:0] iv, bit do_b2b);
    int read_order[4] = {0,1,2,3};
    // randomize read order
    read_order.shuffle();

    foreach (read_order[i]) begin
      int idx = read_order[i];
      csr_rd(.ptr(ral.iv[idx]), .value(iv[idx]), .blocking(~do_b2b));
      `uvm_info(`gfn, $sformatf("\n\t ----| IV_%0d: %h ",idx,  iv[idx]), UVM_HIGH)
    end
  endtask


  virtual task add_data(ref bit [3:0] [31:0] data, bit do_b2b);
    int write_order[4] = {0,1,2,3};

    `uvm_info(`gfn, $sformatf("\n\t ----| ADDING DATA TO DUT %h ", data),  UVM_MEDIUM)

    write_order.shuffle();
    foreach (write_order[i]) begin
      int idx = write_order[i];

      `uvm_info(`gfn, $sformatf("\n\t ----| DATA_IN_%0d: %h ",idx,  data[idx]), UVM_HIGH)
      csr_wr(.ptr(ral.data_in[idx]), .value(data[idx][31:0]), .blocking(~do_b2b));
    end
  endtask


  virtual task read_data(ref bit [3:0] [31:0] cypher_txt, bit do_b2b);
    int read_order[4] = {0,1,2,3};
    // randomize read order
    read_order.shuffle();

    foreach (read_order[i]) begin
      int idx = read_order[i];
      csr_rd(.ptr(ral.data_out[idx]), .value(cypher_txt[idx]), .blocking(~do_b2b));
      `uvm_info(`gfn, $sformatf("\n\t ----| DATA_OUT_%0d: %h ",idx,  cypher_txt[idx]), UVM_HIGH)
    end
  endtask // read_data


  ///////////////////////////////////////
  // ADVANCED TASKS                    //
  ///////////////////////////////////////


  virtual task setup_dut(aes_seq_item item);
    // Write the shadwoed CTRL register.
    status_t status;
    // Setup fields one by one (0) or all fields together (1).
    bit setup_mode = 0;
    // Trigger a control update error (1) or not (0). Only applicable if setup_mode = 1.
    bit control_update_error = 0;
    // Index of the field which shall trigger the control update error.
    int idx_error_field = 0;
    `DV_CHECK_STD_RANDOMIZE_FATAL(setup_mode)
    if ($urandom_range(1, 100) > 95) control_update_error = 1;
    idx_error_field = $urandom_range(0, 5);
    csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
    // Any successful update to the shadowed control register marks the start of a new message. If
    // sideload is enabled and a valid sideload key is available, it may be latched upon the second
    // write and - depending on KEY_TOUCH_FORCES_RESEED - trigger a reseed operation which prevents
    // further updates to the control register untile AES becomes idle again. For simplicity, we
    // just disable sideload here and then update the sideload bit last.
    ral.ctrl_shadowed.sideload.set(0);
    if (!setup_mode) begin
      set_operation(item.operation);
      set_mode(item.aes_mode);
      set_key_len(item.key_len);
      set_manual_operation(item.manual_op);
      set_prng_reseed_rate(prs_rate_e'(item.reseed_rate));
      set_sideload(item.sideload_en);
    end else begin
      // Assemble the intended value.
      ral.ctrl_shadowed.operation.set(item.operation);
      ral.ctrl_shadowed.mode.set(item.mode);
      ral.ctrl_shadowed.key_len.set(item.key_len);
      ral.ctrl_shadowed.sideload.set(item.sideload_en);
      ral.ctrl_shadowed.manual_operation.set(item.manual_op);
      ral.ctrl_shadowed.prng_reseed_rate.set(item.reseed_rate);
      // Trigger a control update error.
      if (control_update_error) begin
        `uvm_info(`gfn, $sformatf("Triggering control update error in field %0d", idx_error_field),
            UVM_MEDIUM)
        // Perform the first write using the correct data.
        csr_update(.csr(ral.ctrl_shadowed), .en_shadow_wr(1'b0), .blocking(1));
        // Make sure at least one field is flipped.
        begin
          unique case (idx_error_field)
            0: ral.ctrl_shadowed.operation.set(item.operation == AES_DEC ? AES_ENC : AES_DEC);
            1: ral.ctrl_shadowed.mode.set(item.mode == AES_ECB ? AES_NONE : AES_ECB);
            2: ral.ctrl_shadowed.key_len.set(item.key_len == AES_128 ? AES_256 : AES_128);
            3: ral.ctrl_shadowed.sideload.set(item.sideload_en ? 1'b0 : 1'b1);
            4: ral.ctrl_shadowed.manual_operation.set(item.manual_op ? 1'b0 : 1'b1);
            5: ral.ctrl_shadowed.prng_reseed_rate.set(item.reseed_rate == PER_64 ? PER_8K : PER_64);
            default:;
          endcase
        end
        // Perform the second write.
        csr_update(.csr(ral.ctrl_shadowed), .en_shadow_wr(1'b0), .blocking(1));
        // Check that we get the recoverable alert. It's possible that DV inserted a fatal error
        // condition before the second write could go through. The recovery from the fatal alert
        // is handled separately.
        csr_rd(.ptr(ral.status), .value(status), .blocking(1));
        `DV_CHECK_FATAL(status.alert_recov_ctrl_update_err == 1'b1 ||
                        status.alert_fatal_fault == 1'b1);
        // Re-assemble the intended value.
        ral.ctrl_shadowed.operation.set(item.operation);
        ral.ctrl_shadowed.mode.set(item.mode);
        ral.ctrl_shadowed.key_len.set(item.key_len);
        ral.ctrl_shadowed.sideload.set(item.sideload_en);
        ral.ctrl_shadowed.manual_operation.set(item.manual_op);
        ral.ctrl_shadowed.prng_reseed_rate.set(item.reseed_rate);
      end
      // Perform the register update without control update error. This will resolve potential
      // previous update errors.
      csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
      csr_update(.csr(ral.ctrl_shadowed), .en_shadow_wr(1'b1), .blocking(1));
      // Make sure the update went through and there wasn't an update error. It's possible that DV
      // inserted a fatal error condition before the second write could go through. In this case,
      // the recoverable alert condition may still be visilbe together with the fatal alert. The
      // fatal alert is handled separately.
      csr_rd(.ptr(ral.status), .value(status), .blocking(1));
      `DV_CHECK_FATAL(status.alert_recov_ctrl_update_err == 1'b0 ||
                      status.alert_fatal_fault == 1'b1);
    end
  endtask


  virtual task generate_aes_item_queue(aes_message_item msg_item);
    // init aes item
    aes_item_init(msg_item);
    // generate DUT cfg
    generate_ctrl_item();
    generate_data_stream(msg_item);
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


  virtual task write_data_key_iv(
    aes_seq_item item,         // sequence item with configuraton
    aes_seq_item data_item,        // sequence item with data to process
    bit          new_msg,          // is this a new msg -> do dut config
    bit          manual_operation, // use manual operation
    bit          sideload_en,      // we are currently using sideload key
    bit          read_output,      // read output or leave untouched
    ref  bit     rst_set           // reset was forced - restart message
    );

    status_t status;
    bit      return_on_idle   = 1;
    bit [3:0] [7:0] data      = data_item.data_in;
    string   txt              ="";
    bit      is_blocking      = ~item.do_b2b;
    int      wait_on_reseed   = 16;
    string interleave_queue[$] = '{ "key_share0_0", "key_share0_1", "key_share0_2", "key_share0_3",
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

    txt = {txt, $sformatf("\n\t IS blocking %b", is_blocking) };

    for (int i = 0;  i < interleave_queue.size(); i++) begin
      string csr_name = interleave_queue[i];
      txt = {txt, $sformatf("\n\t ----| \t %s",csr_name )};

      case (1)
        (!uvm_re_match("key_share0_*", csr_name)): begin
          int idx = get_multireg_idx(csr_name);
          csr_wr(.ptr(ral.key_share0[idx]), .value(item.key[0][idx]), .blocking(is_blocking));
          wait_on_reseed -= 1;
        end
        (!uvm_re_match("key_share1_*", csr_name)): begin
          int idx = get_multireg_idx(csr_name);
          csr_wr(.ptr(ral.key_share1[idx]), .value(item.key[1][idx]), .blocking(is_blocking));
          wait_on_reseed -= 1;
        end
        (!uvm_re_match("iv_*", csr_name)): begin
          int idx = get_multireg_idx(csr_name);
          csr_wr(.ptr(ral.iv[idx]), .value(item.iv[idx]), .blocking(is_blocking));
        end
        (!uvm_re_match("data_in_*", csr_name)): begin
          int idx = get_multireg_idx(csr_name);
          csr_wr(.ptr(ral.data_in[idx]), .value(data[idx]), .blocking(is_blocking));
        end
        (csr_name == "clear_reg"): begin
          clear_regs(item.clear_reg);
          csr_spinwait(.ptr(ral.status.idle) , .exp_data(1'b1));
          // manual mode requries all to be written again
          if (manual_operation) begin
            //remove clear from queue
            interleave_queue.delete(i);
            i = -1;
            wait_on_reseed = 16;
          end
        end
      endcase // case interleave_queue[i]

      if (wait_on_reseed == 0) begin
        // inject write to reg if enabled 25% of the time
        if (cfg.error_types.mal_inject && $urandom(3)==0 && !manual_operation) begin
          int wr_reg = $urandom_range(3,1);
          case (wr_reg)
            1: csr_wr(.ptr(ral.key_share0[$urandom(7)]), .value($urandom()),
                      .blocking(is_blocking));
            2: csr_wr(.ptr(ral.iv[$urandom(3)]), .value($urandom()), .blocking(is_blocking));
            3: csr_wr(.ptr(ral.data_in[$urandom(3)]), .value($urandom()), .blocking(is_blocking));
            default: `uvm_fatal(`gfn, $sformatf("UNREACHABLE BUT NEEDED DUE TO SYNTAX CHECK"))
          endcase
        end
        status_fsm(item, data_item, new_msg,
                   manual_operation, sideload_en, return_on_idle, read_output, status, rst_set);
        wait_on_reseed = 16;
      end
      if (rst_set) break;
    end

    `uvm_info(`gfn,
              $sformatf("\n\t  Configuring the DUT in the following order:  %s, \n\t data 0x%0h",
                        txt, data), UVM_MEDIUM)
  endtask // write_data_key_iv



  // enable sideload sequence
  // and get it to generate a key a random times
  task start_sideload_seq();
    sideload_seq = key_sideload_set_seq#(keymgr_pkg::hw_key_req_t)::type_id::create("sideload_seq");
    `DV_CHECK_RANDOMIZE_FATAL(sideload_seq)
    sideload_seq.start(p_sequencer.key_sideload_sequencer_h);
    forever begin
      `DV_CHECK_RANDOMIZE_FATAL(sideload_seq)
      // send to sequencer with low priority so we can overwrite
      `uvm_send_pri(sideload_seq, 100)

    end
  endtask

  task req_sideload_key();
    req_key_seq = key_sideload_set_seq#(keymgr_pkg::hw_key_req_t)::type_id::create("req_key_seq");
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req_key_seq, sideload_key.valid == 1;)
    req_key_seq.start(p_sequencer.key_sideload_sequencer_h);
    while (!key_used) begin
      // if a clear is triggered, Dut will be reprogrammed
      // but the key agent will not send a new key unless
      // the key is different than prev.
      if (new_key) begin
        `DV_CHECK_RANDOMIZE_WITH_FATAL(req_key_seq, sideload_key.valid == 1;)
        new_key = 0;
      end
      `uvm_send_pri(req_key_seq, 400)
      key_rdy = 1;
    end
    key_used = 0;
  endtask // req_sideload_key


  // the index of multi-reg is at the last char of the name
  virtual function int get_multireg_idx(string name);
    string s = name.getc(name.len - 1);
    return s.atoi();
  endfunction

  virtual task send_msg (
     bit manual_operation,                   // use manual operation
     bit sideload_en,                        // use sideoad key
     bit unbalanced,                         // randomize if we read or write
     int read_prob,                          // chance of reading an availabout output
     int write_prob,                         // chance of writing input data to a ready DUT
     ref bit rst_set                         // reset was forced - restart message
     );

    status_t     status;                     // AES status
    aes_seq_item cfg_item   = new();         // the configuration for this message
    aes_seq_item data_item  = new();         // the next data to transmit
    aes_seq_item read_item;                  // the read item to store output in
    aes_seq_item clone_item;
    bit  new_msg            = 1;             // set when starting a new msg
    aes_seq_item read_queue[$];              // queue to hold items waiting for output

    bit read;
    bit write;
    bit return_on_idle = 1;
    rst_set = 0;
    cfg_item = aes_item_queue.pop_back();

    // Make sure the DUT is idle before setting it up. Writes to the main control register are only
    // accpeted when idle.
    status_fsm(cfg_item, data_item, new_msg, manual_operation, sideload_en, 1, 0, status, rst_set);
    // Configure the main control register.
    setup_dut(cfg_item);
    // For some reason DV just waits for the DUT to be idle but not necessarily for it to accept
    // new input data before providing the first block. But at the beginning of a message, the DUT
    // is always ready to accept new input data anyway. Waiting for the DUT to be idle is required
    // to provide IV and initial key.
    return_on_idle = 1;
    if (unbalanced == 0 || manual_operation) begin
       data_item = new();
      while ((aes_item_queue.size() > 0) && !rst_set) begin
        status_fsm(cfg_item, data_item, new_msg, manual_operation,
                   sideload_en, return_on_idle, 0, status, rst_set);
        // From now on, DV always waits for the DUT to be idle and to accept new input data.
        return_on_idle = 0;
        if (status.input_ready && status.idle) begin
          // The DUT is ready to accept new input data, as well as updates to IV and initial key
          // registers (only allowed when idle). The first config_and_transmit() call configures
          // key and IV.
          data_item = aes_item_queue.pop_back();
          config_and_transmit(cfg_item, data_item, new_msg,
                              manual_operation, sideload_en, 1, rst_set);
          new_msg = 0;
        end else if (cfg_item.mode == AES_NONE) begin
          // The DUT won't produce any output when this mode is configured. Just write the new
          // input data.
          data_item = aes_item_queue.pop_back();
          config_and_transmit(cfg_item, data_item, new_msg,
                              manual_operation, sideload_en, 0, rst_set);
        end
      end

    end else begin
      while (((aes_item_queue.size() > 0) || (read_queue.size() > 0)) && !rst_set) begin
        // get the status to make sure we can provide data - but don't wait for output //
        if (aes_item_queue.size() > 0 ) data_item = new();
        status_fsm(cfg_item, data_item, new_msg,
                   manual_operation, sideload_en, return_on_idle, 0, status, rst_set);
        return_on_idle = 0;
        read  = ($urandom_range(0, 100) <= read_prob);
        write = ($urandom_range(0, 100) <= write_prob);

        if ( (($countones(cfg_item.mode) != 1) || cfg_item.mode == AES_NONE)
            && (aes_item_queue.size() > 0)) begin
          // just write the data - don't expect and output
          data_item = aes_item_queue.pop_back();
          config_and_transmit(cfg_item, data_item, new_msg,
                               manual_operation, sideload_en, 0, rst_set);
        end else if (status.input_ready && (aes_item_queue.size() > 0) && write) begin
          data_item = aes_item_queue.pop_back();
          config_and_transmit(cfg_item, data_item, new_msg,
                              manual_operation, sideload_en, 0, rst_set);
          `downcast(clone_item, data_item.clone());
          read_queue.push_back(clone_item);
        end
        if (write) new_msg = 0;
        if (status.output_valid && read) begin
          if (read_queue.size() > 0)  begin
            read_item = read_queue.pop_front();
            read_data(read_item.data_out, cfg_item.do_b2b);
          end else begin
            `uvm_fatal(`gfn, $sformatf("\n\t ----| DATA READY but no ITEM to add it to! |----"))
          end
        end
      end
    end // else: !if(unbalanced == 0 || manual_operation)
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
      bit          sideload_en,      // we are currently using sideload key
      bit          read_output,      // read output or leave untouched
      ref  bit     rst_set           // reset was forced - restart message
      );

    bit                   is_blocking = ~cfg_item.do_b2b;
    status_t              status;
    rst_set = 0;
    if (new_msg) begin
      write_data_key_iv(cfg_item, data_item, new_msg,
                   manual_operation, sideload_en, 0, rst_set);
    end else begin
      add_data(data_item.data_in, cfg_item.do_b2b);
      // sometimes randomly write a reg while busy
      if (!manual_operation && cfg.error_types.mal_inject && ($urandom(3) == 1)) begin
        int wr_reg = $urandom_range(3,1);
        case (wr_reg)
          1: csr_wr(.ptr(ral.key_share0[$urandom(7)]), .value($urandom()), .blocking(is_blocking));
          2: csr_wr(.ptr(ral.iv[$urandom(3)]), .value($urandom()), .blocking(is_blocking));
          3: csr_wr(.ptr(ral.data_in[$urandom(3)]), .value($urandom()), .blocking(is_blocking));
          default: `uvm_fatal(`gfn, $sformatf("UNREACHABLE BUT NEEDED DUE TO SYNTAX CHECK"))
        endcase
      end
    end
    if (manual_operation && !rst_set) trigger();
    if (read_output && !rst_set) begin
       status_fsm(cfg_item, data_item, new_msg,
                   manual_operation, sideload_en, 0, read_output, status, rst_set);
    end
  endtask // config_and_transmit


  virtual task wait_for_fatal_alert_and_reset ();
    // According to spec, check period will append an 'hFF from the LSF. Add 10 cycle buffers for
    // register updates
    int check_wait_cycles = 6 << 8 + 10;

    // Check for the fatal alert on the alert interface.
    `DV_SPINWAIT_EXIT(
        wait(cfg.m_alert_agent_cfgs["fatal_fault"].vif.alert_tx_final.alert_p);,
        cfg.clk_rst_vif.wait_clks(check_wait_cycles);,
        $sformatf("Timeout waiting for alert %0s", "fatal_check_error"))
    check_fatal_alert_nonblocking("fatal_fault");
    // Reset and re-initialize the DUT.
    // To avoid assertions firing erroneously due to resetting AES prior to the EDN
    // interface, pull all resets concurrently. See
    // https://github.com/lowRISC/opentitan/issues/13573 for details.
    apply_resets_concurrently();
    dut_init("HARD");
  endtask


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
      bit                 sideload_en,      // currently using sideload key
      bit                 return_on_idle,   // return if DUT status is idle
      bit                 read_output,      // read output or leave untouched
      ref  status_t       status,           // the current AES status
      ref  bit            rst_set           // we forced a reset - abort current message and restart
      );

    ctrl_reg_t ctrl;
    bit                   is_blocking       = ~cfg_item.do_b2b;
    bit                   done              = 0;
    string                txt               = "";
    int                   not_idle_cnt      = 0;

    txt     = "\n Entering FSM";
    rst_set = 0;


    // enable get status when provided with an empty Item.
    if (data_item.mode === 'X) begin
      csr_rd(.ptr(ral.status), .value(status), .blocking(1));
    end

    while(!done && !global_reset) begin
      //read the status register to see that we have triggered the operation
      wait(!cfg.under_reset)
      csr_rd(.ptr(ral.status), .value(status), .blocking(1));
      txt = {txt, "\n ----|reading STATUS", status2string(status)};
      // check status and act accordingly //
      if (status.alert_fatal_fault) begin
        // stuck pull reset //
        if (cfg.error_types.mal_inject || cfg.error_types.lc_esc) begin
          `uvm_info(`gfn,
                  $sformatf("\n\t ----| Saw expected Fatal alert - trying to recover \n\t ----| %s",
                              status2string(status)), UVM_MEDIUM)
          try_recover(cfg_item, data_item, manual_operation, sideload_en);
          csr_rd(.ptr(ral.status), .value(status), .blocking(1));
          if ( !status.alert_fatal_fault) begin
            `uvm_fatal(`gfn, $sformatf("\n\t Was able to clear FATAL ALERT without reset \n\t %s",
                       status2string(status)))
          end else begin
            wait_for_fatal_alert_and_reset();
            rst_set = 1;
            done    = 1;
          end
        end else begin
          `uvm_fatal(`gfn, $sformatf("\n\t Unexpected Fatal alert in AES FSM \n\t %s",
             status2string(status)))
        end
      end else if (cfg_item.mode == AES_NONE) begin
        // In this mode, the DUT is not ever supposed to accept input data or provide output data.
        // But it can for example trigger a reseed operation upon loading a new initial key. Here,
        // we just need to wait for the DUT to be idle.
        if (status.idle) begin
          done = 1;
        end
      end else begin
        // state 0
        if (status.idle && status.input_ready) begin
          if (status.output_valid && read_output) begin
            read_data(data_item.data_out, is_blocking);
            txt = {txt, $sformatf("\n\t ----| status state 0 ")};
            done = 1;
          end else if (!read_output) begin
            done = 1; // get more data
          end else begin
            try_recover(cfg_item, data_item, manual_operation, sideload_en);
          end
        end else if (status.idle && !status.input_ready) begin
          // state 1 //
          // if data ready just read and return
          if (status.output_valid && read_output) begin
            read_data(data_item.data_out, is_blocking);
            done = 1;
          end else if (return_on_idle) begin
            // We expect dut to be IDLE
            done = 1;
          end else begin
            // if data is not ready the DUT is missing
            // KEY and IV - or the configuration
            try_recover(cfg_item, data_item, manual_operation, sideload_en);
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


        end else if (!(status.idle || status.stall || status.output_valid)) begin
          // state 3 //
          // Not idle, not stalling, not ready for input and no valid output should only occur when
          // requesting entropy for reseeding the PRNGs which for example happens directly after
          // reset.
          if (!(status.input_ready || aes_requesting_entropy())) begin
            not_idle_cnt++;
            if (not_idle_cnt == 1000) begin
              txt = "\nFor 1000 consecutive reads, AES";
              txt = {txt, $sformatf("\n- neither reported IDLE, STALL, OUTPUT_VALID, INPUT_READY")};
              txt = {txt, $sformatf("\n- nor did it fetch entropy")};
              `uvm_fatal(`gfn, $sformatf("%s", txt))
            end
          end else begin
            not_idle_cnt = 0;
          end
          if (!read_output && !return_on_idle) done = 1;
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
      end // else: !if(status.alert_fatal_fault)
    end // while (!done)


    if (global_reset) begin
      rst_set = 1;
    end
    `uvm_info(`gfn, $sformatf("\n\t %s",txt), UVM_MEDIUM)
  endtask


  virtual task try_recover(
    aes_seq_item        cfg_item,         // sequence item with configuraton
    aes_seq_item        data_item,        // sequence item with data to process
    bit                 manual_operation,
    bit                 sideload_en
    );
    // if data is not ready the DUT is missing
    // KEY and IV - or the configuration
    ctrl_reg_t            ctrl;
    status_t              status;         // the current AES status
    bit                   is_blocking = ~cfg_item.do_b2b;

    csr_rd(.ptr(ral.ctrl_shadowed), .value(ctrl), .blocking(1));
    ral.ctrl_shadowed.operation.set(cfg_item.operation);
    ral.ctrl_shadowed.mode.set(cfg_item.mode);
    ral.ctrl_shadowed.key_len.set(cfg_item.key_len);
    ral.ctrl_shadowed.manual_operation.set(cfg_item.manual_op);
    ral.ctrl_shadowed.sideload.set(cfg_item.sideload_en);
    // key and IV missing clear all and rewrite (a soon to come update will merge
    // the clear options into a single bit)
    clear_regs(2'b11);
    // when using sideload we need to generate
    // new key for agent to send new key item
    if (sideload_en) begin
      new_key = 1;
      key_rdy = 0;
      wait(key_rdy);
    end


    // check for fatal
    csr_rd(.ptr(ral.status), .value(status), .blocking(1));
    if (!status.alert_fatal_fault) begin
      // wait for idle
      if (!status.idle)  csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
      csr_update(.csr(ral.ctrl_shadowed), .en_shadow_wr(1'b1), .blocking(is_blocking));
      csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
    end else begin
      // if alert just try to update ctrl and everything else
      csr_update(.csr(ral.ctrl_shadowed), .en_shadow_wr(1'b1), .blocking(is_blocking));
    end

    write_key(cfg_item.key, is_blocking);
    // wait for reseed but check for fatal
    // if fatal idle will never come
    csr_rd(.ptr(ral.status), .value(status), .blocking(1));
    if (!status.alert_fatal_fault && !status.idle) begin
      if (cfg.reseed_en) csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
    end
    write_iv(cfg_item.iv, is_blocking);
    add_data(data_item.data_in, cfg_item.do_b2b);
    if (manual_operation) trigger();
  endtask // try_recover


  virtual task send_msg_queue (
     bit unbalanced, // uses the probablilites to randomize if we read or write
     int read_prob,  // chance of reading an availabout output
     int write_prob  // chance of writing input data to a ready DUT
     );
    // variables
    aes_message_item my_message;
    bit  rst_set = 0;
    while (message_queue.size() > 0 ) begin
      `uvm_info(`gfn, $sformatf("Starting New Message - messages left %d",
                                 message_queue.size() ), UVM_MEDIUM)
      my_message = new();
      my_message = message_queue.pop_back();
      generate_aes_item_queue(my_message);
      fork
        begin
          if (my_message.sideload_en) begin
            req_sideload_key();
          end else begin
            key_rdy = 1;
          end
        end
        // stay in for until a valid key is ready
        wait(key_rdy);
      join_any
      send_msg(my_message.manual_operation, my_message.sideload_en,
               unbalanced, read_prob, write_prob, rst_set);
      if (my_message.sideload_en) begin
        // release sideload
        key_used = 1;
        csr_spinwait(.ptr(ral.status.idle) , .exp_data(1'b1));
        clear_regs(2'b11);
        csr_spinwait(.ptr(ral.status.idle) , .exp_data(1'b1));
      end

      // when using sideload we need to wait for sequence to release key
      // before starting a new message
      wait(!key_used);
      key_rdy = 0;


      if (rst_set) begin
        aes_item_queue.delete();
        message_queue.delete();
        // send a few msg to make sure
        // everything still works
        cfg.num_messages = 2;
        generate_message_queue();
        // if process was halted from the outside //
        if (global_reset) begin
          global_reset = 0;
          // wait for resset to get set
          wait(cfg.under_reset);
          `uvm_info(`gfn, $sformatf("WAITING FOR RESET RELEASE"), UVM_MEDIUM)
          wait(cfg.clk_rst_vif.rst_n);
          #1ps;
          dut_init("HARD");
        end
      end
    end
  endtask // send_msg_queue

  virtual task post_body();

    // AES indicates when it's done with processing individual blocks but not when it's done
    // with processing an entire message. To detect the end of a message, the DV environment
    // does the following:
    // - It tracks writes to the main control register. If two successfull writes to this
    //   shadowed register are observed, this marks the start of a new message.
    // - DV then knows that the last output data retrieved marks the end of the previous
    //   message.
    // This works fine except for the very last message before the sequence ends. To mark the
    // end of the last message, and trigger its scoring, the `finish_message` variable is set.
    // It gets read by the `rebuild_message()` task in the scoreboard.
    //
    // Before doing this, wait for the DUT to become idle and final output to be read.
    `uvm_info(`gfn, "waiting for DUT to become idle and final output to be read", UVM_MEDIUM)
    csr_spinwait(.ptr(ral.status.idle), .exp_data(1'b1));
    csr_spinwait(.ptr(ral.status.output_valid), .exp_data(1'b0));
    `uvm_info(`gfn, "sending finish_message", UVM_MEDIUM)
    cfg.finish_message = 1;

    super.post_body();

  endtask


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
    aes_item.sideload_en      = message_item.sideload_en;
    aes_item.reseed_rate      = message_item.reseed_rate;
    aes_item.clear_reg_pct    = cfg.clear_reg_pct;
    aes_item.clear_reg_w_rand = cfg.clear_reg_w_rand;
  endfunction // aes_item_init


  function void generate_ctrl_item();
    aes_seq_item item_clone;

    aes_item.item_type = AES_CFG;

    `DV_CHECK_RANDOMIZE_FATAL(aes_item)
    `uvm_info(`gfn, $sformatf("\n\t ----| CONFIG  AES ITEM %s",
                                aes_item.convert2string()), UVM_HIGH)

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
    aes_message.config_error_type_en = cfg.config_error_type;
    aes_message.manual_operation_pct = cfg.manual_operation_pct;
    aes_message.keymask              = cfg.key_mask;
    aes_message.fixed_key_en         = cfg.fixed_key_en;
    aes_message.fixed_data_en        = cfg.fixed_data_en;
    aes_message.fixed_operation_en   = cfg.fixed_operation_en;
    aes_message.fixed_operation      = cfg.fixed_operation;
    aes_message.fixed_keylen_en      = cfg.fixed_keylen_en;
    aes_message.fixed_keylen         = cfg.fixed_keylen;
    aes_message.fixed_iv_en          = cfg.fixed_iv_en;
    aes_message.sideload_pct         = cfg.sideload_pct;
    aes_message.per8_weight          = cfg.per8_weight;
    aes_message.per64_weight         = cfg.per64_weight;
    aes_message.per8k_weight         = cfg.per8k_weight;
  endfunction


  function void generate_message_queue();
    aes_message_item cloned_message;
    for (int i=0; i < cfg.num_messages; i++) begin
      `DV_CHECK_RANDOMIZE_FATAL(aes_message)
      if (aes_message.cfg_error_type[1] == 1'b1) cfg.num_corrupt_messages += 1;
      `downcast(cloned_message, aes_message.clone());
      message_queue.push_front(cloned_message);
      `uvm_info(`gfn, $sformatf("\n\t ----| MESSAGE # %d \n %s",i, cloned_message.convert2string())
               , UVM_MEDIUM)
    end
  endfunction // generate_message_queue


  function void aes_print_item_queue(aes_seq_item item_queue[$]);
    aes_seq_item print_item;
    `uvm_info(`gfn, $sformatf("----| Item queue size: %d", item_queue.size()), UVM_MEDIUM)
    for (int n = 0; n < item_queue.size(); n++) begin
      print_item = item_queue[n];
      `uvm_info(`gfn, $sformatf("----|  ITEM #%d", n ), UVM_MEDIUM)
      `uvm_info(`gfn, $sformatf("%s", print_item.convert2string()), UVM_MEDIUM)
    end
  endfunction // aes_print_item_queue


  function string status2string(status_t status);
    string txt="";
    txt ={txt, $sformatf("\n\t ---| Idle:          %0b", status.idle)};
    txt ={txt, $sformatf("\n\t ---| Stall:         %0b", status.stall)};
    txt ={txt, $sformatf("\n\t ---| Output Lost:   %0b", status.output_lost)};
    txt ={txt, $sformatf("\n\t ---| Output Valid:  %0b", status.output_valid)};
    txt ={txt, $sformatf("\n\t ---| Input Ready:   %0b", status.input_ready)};
    txt ={txt, $sformatf("\n\t ---| Alert - Recov: %0b", status.alert_recov_ctrl_update_err)};
    txt ={txt, $sformatf("\n\t ---| Alert - Fatal: %0b", status.alert_fatal_fault)};
    return txt;
  endfunction // status2string


  function automatic bit aes_requesting_entropy();
    bit requesting_entropy;
    if ((cfg.aes_reseed_vif.entropy_clearing_req == 1'b1) ||
        (cfg.aes_reseed_vif.entropy_masking_req == 1'b1)) begin
      requesting_entropy = 1'b1;
    end else begin
      requesting_entropy = 1'b0;
    end
    return requesting_entropy;
  endfunction

endclass : aes_base_vseq
