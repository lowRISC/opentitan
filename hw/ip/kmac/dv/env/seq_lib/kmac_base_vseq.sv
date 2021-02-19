// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_base_vseq extends cip_base_vseq #(
    .RAL_T               (kmac_reg_block),
    .CFG_T               (kmac_env_cfg),
    .COV_T               (kmac_env_cov),
    .VIRTUAL_SEQUENCER_T (kmac_virtual_sequencer)
  );

  `uvm_object_utils(kmac_base_vseq)
  `uvm_object_new

  // used to randomly enable interrupts
  rand bit [TL_DW-1:0] enable_intr;

  // enable KMAC hashing
  rand bit kmac_en;

  // This bit only applies to KMAC hashing operation.
  //
  // KMAC has two operation modes, one with known output length,
  // and with an unknown output length (as an XOF).
  //
  // When output length is known we write `right_encode(len)` to msgfifo
  // after the input message, but to enable the XOF mode we must write `right_encode(0)`
  // to the msgfifo after the input message.
  //
  // This bit enables the XOF mode of operation, and causes the correct output length
  // encoding to be written into the msgfifo.
  rand bit xof_en;

  // bit-length of the incoming key
  rand kmac_pkg::key_len_e key_len;

  // hashing mode (sha3/shake/cshake)
  rand sha3_pkg::sha3_mode_e hash_mode;

  // security strength
  rand sha3_pkg::keccak_strength_e strength;

  // endianness of message and secret key.
  // 0: little endian
  // 1: big endian
  rand bit msg_endian;

  // endianness of output digest.
  // 0: keep state endianness as is
  // 1: convert state to big endian
  rand bit state_endian;

  // set to provide the KMAC with a key through the sideload interface.
  // does not control whether the cfg.sideload field is set.
  rand bit provide_sideload_key;

  // Controls whether to actually enable sideloading functionality
  rand bit en_sideload;

  // entropy mode
  rand kmac_pkg::entropy_mode_e entropy_mode;

  // entropy fast process mode
  rand bit entropy_fast_process;

  // entropy ready
  rand bit entropy_ready;

  // error process
  rand bit err_processed;

  // output length in bytes.
  rand int unsigned output_len;

  // Keccak block size - used only for variable-length output functions.
  // strength128 -> 168
  // strength256 -> 136
  rand int unsigned keccak_block_size;

  // Function name and customization string length in bytes (1 char = 1 byte).
  // Since we cannot create random strings, we simplify by controlling the length of the fname.
  rand int unsigned fname_len;
  rand int unsigned custom_str_len;

  // Used to store N and S after encoding them
  rand byte fname_arr[];
  rand byte custom_str_arr[];

  // input msg - assume this is little endian
  rand bit [7:0] msg[];

  // 2 key shares - are XORed together to produce intended secret key
  //
  // max key length is 512 bits
  rand bit [KMAC_NUM_SHARES-1:0][KMAC_NUM_KEYS_PER_SHARE-1:0][31:0] key_share;

  // address used when writing to message fifo
  rand bit [TL_AW-1:0] fifo_addr;

  // data mask used when accessing TLUL windows (msgfifo, state)
  rand bit [TL_DBW-1:0] data_mask;

  // array to store `right_encode(output_len)`
  bit [7:0] output_len_enc[];

  bit do_kmac_init = 1'b1;

  // constrain xof_en to 0 if not in kmac mode
  constraint xof_en_c {
    (!kmac_en) -> (xof_en == 1'b0);
  }

  // KMAC HWIP only uses CSHAKE mode for KMAC hashing
  constraint hash_mode_c {
    if (kmac_en) {
      hash_mode == sha3_pkg::CShake;
    } else {
      hash_mode != sha3_pkg::CShake;
    }
  }

  // output length constraints when using any SHA3 mode
  constraint output_len_sha3_c {
    if (hash_mode == sha3_pkg::Sha3) {
      (strength == sha3_pkg::L224) -> (output_len == 28);
      (strength == sha3_pkg::L256) -> (output_len == 32);
      (strength == sha3_pkg::L384) -> (output_len == 48);
      (strength == sha3_pkg::L512) -> (output_len == 64);
    }
  }

  constraint strength_c {
    // only 128/256 bit strengths are supported for the XOFs
    (hash_mode inside {sha3_pkg::Shake, sha3_pkg::CShake}) ->
      (strength inside {sha3_pkg::L128, sha3_pkg::L256});

    // SHA3-128 is not supported
    (hash_mode == sha3_pkg::Sha3) -> (strength != sha3_pkg::L128);
  }

  constraint key_len_c {
    (en_sideload) -> key_len == Key256;
  }

  // Set the block size based on the random security strength.
  // This is only relevant for XOF functions (L128 or L256), but will be
  // set for all security strengths.
  //
  // The block size is calculated by:
  // `(1600 - (2 * strength_in_bits)) / 8`
  constraint keccak_block_size_c {
    (strength == sha3_pkg::L128) -> (keccak_block_size == 168);
    (strength == sha3_pkg::L224) -> (keccak_block_size == 144);
    (strength == sha3_pkg::L256) -> (keccak_block_size == 136);
    (strength == sha3_pkg::L384) -> (keccak_block_size == 104);
    (strength == sha3_pkg::L512) -> (keccak_block_size == 72);
  }

  // constrain the range of addresses we can access msg_fifo through
  constraint fifo_addr_c {
    fifo_addr inside {[KMAC_FIFO_BASE : KMAC_FIFO_END]};
  }

  // as per TL-UL spec, data mask must have contiguous 1s.
  //
  // we duplicate this constraint here as we manually write to the msgfifo window
  // via the tl_access() method.
  constraint data_mask_contiguous_c {
    $countones(data_mask ^ {data_mask[TL_DBW-2:0], 1'b0}) <= 2;
  }

  // Bias the data mask to be {TL_DBW{1'b1}} half of the time,
  // to slightly increase simulation speed
  constraint data_mask_c {
    $countones(data_mask) dist {
      [1 : TL_DBW] :/ 1,
      TL_DBW       :/ 1
    };
  }

  // as per spec, len(N+S) can be at most 288 bits (36 bytes).
  constraint prefix_len_c {
    fname_len + custom_str_len <= 36;

    fname_arr.size() == fname_len;
    custom_str_arr.size() == custom_str_len;
  }

  // constrains N and S to only be valid alphabet letters and space [A-Za-z]
  constraint prefix_is_char_c {
    foreach(fname_arr[i]) {
      //                space |  A-Z   |  a-z
      fname_arr[i] inside {32, [65:90], [97:122]};
    }
    foreach(custom_str_arr[i]) {
      //                     space |  A-Z   |  a-z
      custom_str_arr[i] inside {32, [65:90], [97:122]};
    }
  }

  virtual task dut_init(string reset_kind = "HARD");
    super.dut_init();
    if (do_kmac_init) kmac_init();
  endtask

  virtual task dut_shutdown();
    // check for pending kmac operations and wait for them to complete
    // TODO
  endtask

  // setup basic kmac features
  virtual task kmac_init();
    // Wait for KMAC to reach idle state
    wait (cfg.idle_vif.pins == 1);
    `uvm_info(`gfn, "reached idle state", UVM_HIGH)

    // set interrupts
    cfg_interrupts(.interrupts(enable_intr));
    `uvm_info(`gfn, $sformatf("intr[KmacDone] = %0b", enable_intr[KmacDone]), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("intr[KmacFifoEmpty] = %0b", enable_intr[KmacFifoEmpty]), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("intr[KmacErr] = %0b", enable_intr[KmacErr]), UVM_HIGH)

    // setup CFG csr with default random values
    ral.cfg.kmac_en.set(kmac_en);
    ral.cfg.kstrength.set(strength);
    ral.cfg.mode.set(hash_mode);
    ral.cfg.msg_endianness.set(msg_endian);
    ral.cfg.state_endianness.set(state_endian);
    ral.cfg.sideload.set(en_sideload);
    ral.cfg.entropy_mode.set(entropy_mode);
    ral.cfg.entropy_fast_process.set(entropy_fast_process);
    ral.cfg.entropy_ready.set(entropy_ready);
    ral.cfg.err_processed.set(err_processed);
    csr_update(.csr(ral.cfg));

    // setup KEY_LEN csr
    csr_wr(.csr(ral.key_len), .value(key_len));

    // print debug info
    `uvm_info(`gfn, $sformatf("KMAC INITIALIZATION INFO:\n%0s", convert2string()), UVM_HIGH)
  endtask

  virtual function string convert2string();
    return {$sformatf("intr_en[KmacDone]: %0b\n", enable_intr[KmacDone]),
            $sformatf("intr_en[KmacFifoEmpty]: %0b\n", enable_intr[KmacFifoEmpty]),
            $sformatf("intr_en[KmacErr]: %0b\n", enable_intr[KmacErr]),
            $sformatf("kmac_en: %0b\n", kmac_en),
            $sformatf("xof_en: %0b\n", xof_en),
            $sformatf("hash_mode: %0s\n", hash_mode.name()),
            $sformatf("strength: %0s\n", strength.name()),
            $sformatf("msg_length: %0d bytes\n", msg.size()),
            $sformatf("keccak_block_size: %0d\n", keccak_block_size),
            $sformatf("key_len: %0s\n", key_len.name()),
            $sformatf("output_len %0d\n", output_len),
            $sformatf("msg_endian: %0b\n", msg_endian),
            $sformatf("state_endian: %0b\n", state_endian),
            $sformatf("en_sideload: %0b\n", en_sideload),
            $sformatf("provide_sideload_key: %0b\n", provide_sideload_key),
            $sformatf("fname_arr: %0p\n", fname_arr),
            $sformatf("fname: %0s\n", str_utils_pkg::bytes_to_str(fname_arr)),
            $sformatf("custom_str_arr: %0p\n", custom_str_arr),
            $sformatf("custom_str: %0s\n", str_utils_pkg::bytes_to_str(custom_str_arr)),
            $sformatf("entropy_mode: %0s\n", entropy_mode.name()),
            $sformatf("entropy_fast_process: %0b\n", entropy_fast_process),
            $sformatf("entropy_ready: %0b\n", entropy_ready),
            $sformatf("err_processed: %0b", err_processed)};
  endfunction

  // This function implements the bulk of integer encoding specified by NIST.SP.800-185
  //
  // As per spec, this function is valid for any 0 >= x > 2**2040
  //
  // Set `left_right` to 1'b1 for left encoding, and 1'b0 for right encoding
  //
  // Input `q` is assumed to be empty
  function void encode(bit [MAX_ENCODE_WIDTH-1:0] x, bit left_right, ref bit [7:0] q[$]);
    bit [7:0] b_str[$];
    byte b;
    if (x == 0) begin
      q.push_back(8'b0);
    end else begin
      // split the input number into a stream of bytes
      while (x > 0) begin
        b = x[7:0];
        x = x >> 8;
        q.push_back(b);
      end
      // append the size of the queue at the front or back of the queue,
      // depending whether we are left encoding or right encoding
    end
    // reverse bytes of q before prepending/appending q.size().
    {<< byte {q}} = q;
    b = q.size();
    if (left_right) begin
      q.push_front(b);
    end else begin
      q.push_back(b);
    end
  endfunction

  // This function performs the `left_encode(x)` function specified by NIST.SP.800-185
  //
  // As per spec, this function is valid for any 0 >= x > 2**2040
  function void left_encode(bit [MAX_ENCODE_WIDTH-1:0] x, ref bit [7:0] arr[]);
    bit [7:0] q[$];
    encode(x, 1'b1, q);
    arr = q;
  endfunction

  // This function performs the `right_encode(x)` specified by NIST.SP.800-185
  //
  // As per spec, this function is valid for any 0 >= x > 2**2040
  function void right_encode(bit [MAX_ENCODE_WIDTH-1:0] x, ref bit [7:0] arr[]);
    bit [7:0] q[$];
    encode(x, 1'b0, q);
    arr = q;
  endfunction

  // This function implements the `encode_string(S)` function specified by NIST.SP.800-185
  //
  // As per spec, this function is valid for any 0 >= bytes.size() > 2**2040.
  // Undefined behavior may result if this condition is broken.
  function void encode_string(byte bytes[], ref bit [7:0] arr[]);
    bit [7:0] encoded_len[];

    // convert from type `byte` to type `bit [7:0]`
    foreach (bytes[i]) begin
      arr[i] = 8'(bytes[i]);
    end

    left_encode(bytes.size() * 8, encoded_len);
    `uvm_info(`gfn, $sformatf("encoded_str_len: %0p", encoded_len), UVM_HIGH)
    arr = {encoded_len, arr};
  endfunction

  // This task will encode the function name and customization string,
  // and write them to the PREFIX csrs.
  virtual task set_prefix();
    bit [7:0] encoded_fname[] = new[fname_arr.size()];
    bit [7:0] encoded_custom_str[] = new[custom_str_arr.size()];
    bit [7:0] prefix_bytes[] = new[fname_arr.size() + custom_str_arr.size()];

    // PREFIX csr provides 288 bits for N+S, and 64 bits for the encoded lengths
    bit [31:0] prefix_arr[11];

    // encode function name and string
    encode_string(fname_arr, encoded_fname);
    encode_string(custom_str_arr, encoded_custom_str);
    `uvm_info(`gfn, $sformatf("encoded_fname: %0p", encoded_fname), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("encoded_custom_str: %0p", encoded_custom_str), UVM_HIGH)

    // stream into chunks of 32-bits (size of the PREFIX csr)
    prefix_bytes = {encoded_fname, encoded_custom_str};
    for (int i = 0; i < (fname_len + custom_str_len) / 4 + 2 ; i++) begin
      prefix_arr[i] = {<< byte {prefix_bytes with [i*4 +: 4]}};
    end
    `uvm_info(`gfn, $sformatf("prefix_arr: %0p", prefix_arr), UVM_HIGH)

    // write to PREFIX csrs
    //
    // We need to overwrite all 10 of them each time we configure the prefix, as the customization
    // string is not guaranteed to be the full 256 bits every time, meaning that we might leave
    // stale information from the previous iteration otherwise.
    foreach (prefix_arr[i]) begin
      string csr_name = $sformatf("prefix_%0d", i);
      uvm_reg csr = ral.get_reg_by_name(csr_name);
      csr_wr(.csr(csr), .value(prefix_arr[i]));
    end
  endtask

  // This task writes the given command to the CMD csr
  virtual task issue_cmd(kmac_cmd_e cmd);
    csr_wr(.csr(ral.cmd), .value(cmd));
  endtask

  // This task commands KMAC to manually squeeze more output data,
  // and blocks until it has completed.
  virtual task squeeze_digest();
    issue_cmd(CmdManualRun);
    csr_spinwait(.ptr(ral.status.sha3_squeeze), .exp_data(1'b1));
  endtask

  // This task writes both key shares to the appropriate CSRs
  virtual task write_key_shares();
    // write keys to both shares by default regardless of masking configuration
    for (int i = 0; i < KMAC_NUM_SHARES; i++) begin
      for (int j = 0; j < KMAC_NUM_KEYS_PER_SHARE; j++) begin
        string csr_name = $sformatf("key_share%0d_%0d", i, j);
        uvm_reg csr = ral.get_reg_by_name(csr_name);
        csr_wr(.csr(csr), .value(key_share[i][j]));
      end
    end

    // debug - print out all keys
    for (int i = 0; i < KMAC_NUM_SHARES; i++) begin
      for (int j = 0; j < KMAC_NUM_KEYS_PER_SHARE; j++) begin
        `uvm_info(`gfn, $sformatf("key_share[%0d][%0d] = 0x%0x", i, j, key_share[i][j]), UVM_HIGH)
      end
    end
  endtask

  virtual task provide_sw_entropy();
    csr_wr(.csr(ral.entropy_seed_lower), .value($urandom()));
    csr_wr(.csr(ral.entropy_seed_upper), .value($urandom()));
  endtask

  // Call this task to initiate a KDF hashing operation
  virtual task send_kdf_req();
    keymgr_kmac_host_seq kdf_seq;
    `uvm_create_on(kdf_seq, p_sequencer.kdf_sequencer_h);
    `DV_CHECK_RANDOMIZE_FATAL(kdf_seq)
    kdf_seq.msg_size_bytes = msg.size();
    `uvm_send(kdf_seq)
  endtask

  // This task writes a generic byte array into the msg_fifo
  //
  // The general flow of this task is this:
  //
  // - Read STATUS csr to make sure there is enough room in the msgfifo
  //   - If not, csr_spinwait until there is room
  //
  // - Pick a random address in the FIFO window.
  //
  // - Pick a random write mask, making sure that if there are M<4 bytes in the message then there
  //   are at most M enabled bits in the write mask.
  //   This behavior only applies
  //
  // - Pick a random write mask:
  //
  //   - If message is little endian, we can fully randomize the mask, making sure that
  //     if there are M<4 bytes left in the message then there are at most M enabled bits
  //     in the mask. This allows us to write <=4 bytes at a time which is ok since
  //     little endian ordering will be preserved.
  //
  //   - If message is big endian, things get more complicated.
  //     Since KMAC only endian-swaps the bytes in each word, and leaves word order alone,
  //     we need to write a full word at a time to the msgfifo (or the remainder of the message
  //     if M<4 bytes remain).
  //     This is because writing partial words with the big-endian scheme used by KMAC will mess up
  //     byte ordering and cause incorrect message to be accumulated.
  //
  // - Pull N bytes from the message queue, where N is the number of enable bits in the data mask
  //
  // - Stitch these N bytes together into a data word based off of the write mask
  //   - Bytes from the message are only placed in locations corresponding to
  //     an enabled bit in the mask
  //   - All other bytes in the word are randomized
  //
  // - Perform a TLUL access to the msgfifo with the random data/addr/mask, relying on tl_agent
  //   to correctly align the final address and data size
  virtual task write_msg(bit [7:0] msg_arr[], bit blocking = $urandom_range(0, 1));

    bit [TL_DW-1:0] data_word;
    bit [7:0] msg_q[$];

    `uvm_info(`gfn, $sformatf("msg_arr: %0p", msg_arr), UVM_HIGH)
    if (msg_endian) dv_utils_pkg::endian_swap_byte_arr(msg_arr);
    `uvm_info(`gfn, $sformatf("msg_arr_swapped: %0p", msg_arr), UVM_HIGH)

    // Use a queue for the msgfifo writes to make life in the TB way easier.
    msg_q = msg_arr;

    `uvm_info(`gfn, $sformatf("initial msg: %0p", msg_q), UVM_HIGH)

    // iterate through the message queue and pop off bytes to write to msgfifo
    while (msg_q.size() > 0) begin
      // check that there is actually room in the fifo before we start writing anything
      wait_fifo_has_capacity();

      `DV_CHECK_MEMBER_RANDOMIZE_FATAL(fifo_addr)

      // If message is written in little-endian format, we ensure there are at most the same number
      // of enable bits in the data mask as there are bytes remaining in the message queue.
      // This allows us to perform partial word writes to the msgfifo, and handles scenarios where
      // less than 4 bytes of message remain.
      //
      // If message is written in big-endian format, we ensure that we write a full word at a time
      // to the msgfifo (or the remainder of the message queue if <4 bytes remain).
      // This is due to KMAC expecting that big-endian messages preserve word ordering and only
      // endian-swap the bytes in each word.
      `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(data_mask, $countones(data_mask) <= msg_q.size();
                                                       if (msg_endian) {
                                                         if (msg_q.size() < TL_DBW) {
                                                           soft $countones(data_mask) == msg_q.size();
                                                         } else {
                                                           soft $countones(data_mask) == TL_DBW;
                                                         }
                                                       })

      // Randomize the data word to write into the message fifo.
      // Valid byte positions will be overwritten with bytes from the actual message.
      `DV_CHECK_STD_RANDOMIZE_FATAL(data_word)

      // Replace valid bytes in the data_word with bytes from the message queue.
      for (int i = 0; i < TL_DBW; i++) begin
        if (data_mask[i]) begin
          data_word[i*8 +: 8] = msg_q.pop_front();
          `uvm_info(`gfn, $sformatf("intermediate data_word: 0x%0x", data_word), UVM_HIGH)
        end
      end

      // print some debug info before performing the TLUL write
      `uvm_info(`gfn, $sformatf("msg_size: %0d", msg_q.size()), UVM_HIGH)
      `uvm_info(`gfn, $sformatf("fifo_addr = 0x%0x", fifo_addr), UVM_HIGH)
      `uvm_info(`gfn, $sformatf("data_word = 0x%0x", data_word), UVM_HIGH)
      `uvm_info(`gfn, $sformatf("data_mask = 0x%0x", data_mask), UVM_HIGH)

      // Write to the msgfifo
      //
      // TODO: randomize non/blocking?
      tl_access(.addr(ral.get_addr_from_offset(fifo_addr)),
                .write(1),
                .data(data_word),
                .mask(data_mask),
                .blocking(blocking));
    end

    // wait for all msgfifo accesses to complete
    wait_no_outstanding_access();

    // TODO: final csr checks might be needed
  endtask

  // This task burst writes 32-bit chunks of the message into the msgfifo
  virtual task burst_write_msg(bit [7:0] msg_arr[]);
    bit [TL_DW-1:0] data_word;
    bit [7:0] msg_q[$];

    if (msg_endian) dv_utils_pkg::endian_swap_byte_arr(msg_arr);

    msg_q = msg_arr;

    `uvm_info(`gfn, $sformatf("initial msg: %0p", msg_q), UVM_HIGH)

    while (msg_q.size() > 0) begin
      `uvm_info(`gfn, $sformatf("msg size: %0d", msg_q.size()), UVM_HIGH)

      if (msg_q.size() >= KMAC_FIFO_NUM_BYTES) begin
        repeat (KMAC_FIFO_NUM_WORDS) begin
          `DV_CHECK_MEMBER_RANDOMIZE_FATAL(fifo_addr)
          `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(data_mask, data_mask == '1;)

          for (int i = 0; i < TL_DBW; i++) begin
            data_word[i*8 +: 8] = msg_q.pop_front();
            `uvm_info(`gfn, $sformatf("intermediate data_word: 0x%0x", data_word), UVM_HIGH)
          end

          // print some debug info before performing the TLUL write
          `uvm_info(`gfn, $sformatf("msg_size: %0d", msg_q.size()), UVM_HIGH)
          `uvm_info(`gfn, $sformatf("fifo_addr = 0x%0x", fifo_addr), UVM_HIGH)
          `uvm_info(`gfn, $sformatf("data_word = 0x%0x", data_word), UVM_HIGH)
          `uvm_info(`gfn, $sformatf("data_mask = 0x%0x", data_mask), UVM_HIGH)

          tl_access(.addr(ral.get_addr_from_offset(fifo_addr)),
                    .write(1),
                    .data(data_word),
                    .mask(data_mask),
                    .blocking($urandom_range(0, 1)));
        end
        // wait for the fifo to be empty before writing more msg
        //
        // spinwait instead of checking the interrupt because it's not guaranteed
        // that the interrupt will remain high after writing the last word,
        // depending on how long the input message is.
        csr_spinwait(.ptr(ral.status.fifo_empty), .exp_data(1));
      end else begin
        // if we reach this case, means that the remaining message
        // is smaller in size than the fifo, so we can just write it normally
        // using `write_msg()`.
        write_msg(msg_q);
        break;
      end
    end
    // wait for all fifo accesses to complete
    wait_no_outstanding_access();
  endtask

  // This task checks the fifo_empty interrupt (if enabled) and clears it,
  // then waits for STATUS.fifo_full to be 0.
  virtual task wait_fifo_has_capacity();
    bit [TL_DW-1:0] irq_data;

    // read out interrupt state and clear any set interrupts (fifo_empty).
    //
    // TODO: might need a way to determine when to check fifo-related state in the scoreboard
    csr_rd(.ptr(ral.intr_state), .value(irq_data));
    csr_wr(.csr(ral.intr_state), .value(irq_data));

    csr_spinwait(.ptr(ral.status.fifo_full), .exp_data(1'b0));
  endtask

  // This task waits for the kmac_done interrupt to trigger,
  // or waits for ral.intr_state.kmac_done to be high if interrupts are disabled.
  virtual task wait_for_kmac_done();
    bit [TL_DW-1:0] intr_state;
    if (enable_intr[KmacDone]) begin
      wait(cfg.intr_vif.pins[KmacDone] == 1'b1);
      check_interrupts(.interrupts(1 << KmacDone),
                       .check_set(1'b1));
    end else begin
      csr_spinwait(.ptr(ral.intr_state.kmac_done), .exp_data(1'b1));
    end
    // read and clear intr_state
    csr_rd(.ptr(ral.intr_state), .value(intr_state));
    csr_wr(.csr(ral.intr_state), .value(intr_state));
  endtask

  // This task reads a chunk of data from the STATE window and appends it to the `digest`
  // array byte by byte.
  // This task can read at most `keccak_block_size` bytes from the digest window.
  // The `chunk_size` input is assumed to be greater than 0.
  //
  // The general idea is:
  // - Read 4-byte words from the STATE window
  // - Add each byte to a queue, decrementing the total output_len each time
  virtual task read_digest_chunk(bit [TL_AW-1:0] state_addr, int unsigned chunk_size,
                                 ref bit [7:0] digest[]);
    bit [TL_DW-1:0] digest_word;
    bit [7:0] digest_byte;

    while (chunk_size > 0) begin
      // Get a random mask for the state window read, keeping it as TL_DBW'(1'b1) whenever possible
      `DV_CHECK_MEMBER_RANDOMIZE_WITH_FATAL(data_mask, $countones(data_mask) <= chunk_size;
                                                       data_mask[0] == 1;
                                                       if (chunk_size < TL_DBW) {
                                                         soft $countones(data_mask) == chunk_size;
                                                       } else {
                                                         soft $countones(data_mask) == TL_DBW;
                                                       })
      `uvm_info(`gfn, $sformatf("state read mask: 0b%0b", data_mask), UVM_HIGH)
      if (state_endian) begin
        data_mask = {<< bit {data_mask}};
        `uvm_info(`gfn, $sformatf("swapped state read mask: 0b%0b", data_mask), UVM_HIGH)
      end

      tl_access(.addr(ral.get_addr_from_offset(state_addr)),
                .write(1'b0),
                .mask(data_mask),
                .data(digest_word));

      `uvm_info(`gfn, $sformatf("digest_word: 0x%0x", digest_word), UVM_HIGH)

      // This section of code is used to return the read digest to the virtual sequence for any
      // checks.
      // This is only actually used for the NIST vector tests.
      if (state_endian) begin
        data_mask = {<< bit {data_mask}};
        digest_word = {<< byte {digest_word}};
      end
      for (int i = 0; i < TL_DBW; i++) begin
        if (chunk_size == 0) break;
        if (data_mask[i]) begin
          digest_byte = digest_word[i*8 +: 8];
          digest = {digest, digest_byte};
          chunk_size -= 1;
        end
      end

      state_addr = state_addr + 4;

    end

  endtask

  // This task reads the full `output_len` bytes from the digest window,
  // using the helper task `read_digest_chunk()` to read a block at a time
  // from the digest window.
  // More data is squeezed as necessary.
  //
  // Note: if masking is disabled we read the full 200 bytes from SHARE1,
  //       this is so we can check that it has been zeroed.
  virtual task read_digest_shares(int unsigned full_output_len, bit en_masking,
                                  ref bit [7:0] share0[], ref bit [7:0] share1[]);

    int unsigned remaining_output_len = full_output_len;

    int unsigned cur_chunk_size = 0;

    while (remaining_output_len > 0) begin
      cur_chunk_size = (remaining_output_len <= keccak_block_size) ? remaining_output_len : keccak_block_size;

      read_digest_chunk(KMAC_STATE_SHARE0_BASE, cur_chunk_size, share0);
      read_digest_chunk(KMAC_STATE_SHARE1_BASE, en_masking ? cur_chunk_size : 200, share1);

      `uvm_info(`gfn, $sformatf("read a %0d byte chunk of digest", cur_chunk_size), UVM_HIGH)

      remaining_output_len -= cur_chunk_size;

      if (remaining_output_len > 0) begin
        squeeze_digest();
      end

      `uvm_info(`gfn, $sformatf("remaining_output_len: %0d", remaining_output_len), UVM_HIGH)
    end

  endtask

endclass : kmac_base_vseq
