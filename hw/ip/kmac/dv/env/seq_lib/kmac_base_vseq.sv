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

  // data mask used when writing to message fifo
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

    // setup CFG csr
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
    return {$sformatf("enable_intr: %0p\n", enable_intr),
            $sformatf("kmac_en: %0b\n", kmac_en),
            $sformatf("xof_en: %0b\n", xof_en),
            $sformatf("hash_mode: %0s\n", hash_mode.name()),
            $sformatf("strength: %0s\n", strength.name()),
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

  // helper function - takes in the key_len_e enum, and returns
  // its size in bytes.
  // e.g. if key is 128 bits long, this function will return 16.
  function int get_key_size_bytes(kmac_pkg::key_len_e len);
    case (len)
      Key128: return 16;
      Key192: return 24;
      Key256: return 32;
      Key384: return 48;
      Key512: return 64;
      default: `uvm_fatal(`gfn, $sformatf("%0s is an invalid key length!", len))
    endcase
  endfunction

  // Returns the key size in 32-bit words.
  function int get_key_size_words(kmac_pkg::key_len_e len);
    return (get_key_size_bytes(len) / 4);
  endfunction

  // Returns the key size in 64-bit blocks.
  function int get_key_size_blocks(kmac_pkg::key_len_e len);
    return (get_key_size_words(len) / 2);
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
    prefix_bytes = {<< byte {encoded_fname, encoded_custom_str}};
    prefix_arr = {<< 32 {prefix_bytes}};
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
  virtual task write_msg(bit [7:0] msg_arr[]);

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
                .mask(data_mask));
    end

    // wait for all msgfifo accesses to complete
    //
    // TODO: uncomment once nonblocking TL accesses are enabled.
    // wait_no_outstanding_access();

    // TODO: final csr checks might be needed
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

  // This task reads the contents of the STATE window and populates the contents of `digest` with
  // the output data.
  //
  // The general idea is:
  // - Read 4-byte words from the STATE window
  // - Add each byte to a queue, decrementing the total output_len each time
  //
  // TODO: Support squeezing output data for >keccak_block_size B output.
  //       Smoke test constrains output length to be below keccak_block_size.
  virtual task read_digest(bit [TL_AW-1:0] state_addr,
                           int unsigned output_len,
                           ref bit [7:0] digest[]);
    bit [TL_DW-1:0] digest_word;
    bit [7:0] digest_byte;

    while (output_len > 0) begin
      // TODO: randomize non/blocking?
      tl_access(.addr(ral.get_addr_from_offset(state_addr)),
                .write(1'b0),
                .data(digest_word));

      `uvm_info(`gfn, $sformatf("digest_word: 0x%0x", digest_word), UVM_HIGH)

      // If endianness is swapped for the state digest, byte-swap each word that is read.
      if (state_endian) begin
        digest_word = {<< byte {digest_word}};
        `uvm_info(`gfn, $sformatf("digest_word after endian swap: 0x%0x", digest_word), UVM_HIGH)
      end

      for (int i = 0; i < TL_DW / 8; i++) begin
        // safety check - if the output length has reached 0 due to being decremented,
        // it indicates that we've finished reading the full digest and need to exit immediately.
        if (output_len == 0) break;

        digest_byte = digest_word[i*8 +: 8];

        digest = {digest, digest_byte};

        // decrement the output_len, as we've just popped off a byte
        output_len = output_len - 1;
      end

      // Increment the address into the state window to read the next word
      state_addr = state_addr + 4;
    end

  endtask

  // This task reads the output digest and compares it to digest produced by reference model
  virtual task check_digest();
    // Note that all three of these will be the same length
    bit [7:0] digest_share0[];
    bit [7:0] digest_share1[];
    bit [7:0] unmasked_digest[] = new[output_len];

    // # of 32-bit entries in the key
    int key_word_len = get_key_size_words(key_len);
    // # of bytes in the key
    int key_byte_len = get_key_size_bytes(key_len);

    // if masking is enabled, need to XOR both key shares to get "actual" key
    bit [31:0] unmasked_key[$];
    // DPI model needs to take in a byte-stream for the key
    bit [7:0] dpi_key_arr[];
    // Intermediate array for streaming `unmasked_key` into `dpi_key_arr`
    //bit [7:0] unmasked_key_bytes[] = new[get_key_size_bytes(key_len)];
    bit [7:0] unmasked_key_bytes[];

    // output digest from DPI model
    bit [7:0] dpi_digest[] = new[output_len];

    `uvm_info(`gfn, $sformatf("key_word_len: %0d", key_word_len), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("key_byte_len: %0d", key_byte_len), UVM_HIGH)

    // Read out both digest shares
    read_digest(KMAC_STATE_SHARE0_BASE, output_len, digest_share0);
    `uvm_info(`gfn, $sformatf("digest_share0: %0p", digest_share0), UVM_HIGH)
    // if masking disabled, read the full share1 digest so we can check it is 0.
    read_digest(KMAC_STATE_SHARE1_BASE, (cfg.enable_masking) ? output_len : 200, digest_share1);
    `uvm_info(`gfn, $sformatf("digest_share1: %0p", digest_share1), UVM_HIGH)

    `uvm_info(`gfn, $sformatf("msg input to DPI: %0p", msg), UVM_HIGH)

    ////////////////////////////////////////////////////
    // Below logic should eventually go in scoreboard //
    ////////////////////////////////////////////////////

    // If masking is enabled, we need to XOR both shares of the digest and key
    // to get the "actual" unmasked versions.
    //
    // If masking is disabled, share1 of the digest must be 0, and
    // we will only care about share0 of the key.
    if (cfg.enable_masking) begin
      // XOR the digest
      for (int i = 0; i < output_len; i++) begin
        unmasked_digest[i] = digest_share0[i] ^ digest_share1[i];
      end
      // XOR the key
      for (int i = 0; i < key_word_len; i++) begin
        unmasked_key.push_back(key_share[0][i] ^ key_share[1][i]);
      end
    end else begin
      // check that share1 of digest is 0 - 200 bytes in total.
      for (int i = 0; i < 200; i++) begin
        `DV_CHECK_EQ_FATAL(digest_share1[i], 0,
          $sformatf("digest_share1[%0d] is not 0!", i))
      end
      // the digest is just share0
      unmasked_digest = digest_share0;
      // the "actual" key is just share0 of the key
      for (int i = 0; i < key_word_len; i++) begin
        unmasked_key.push_back(key_share[0][i]);
      end
    end

    // Based on random settings, determine which DPI function to call
    case (hash_mode)
      sha3_pkg::Sha3: begin
        case (strength)
          sha3_pkg::L224: begin
            digestpp_dpi_pkg::c_dpi_sha3_224(msg, msg.size(), dpi_digest);
          end
          sha3_pkg::L256: begin
            digestpp_dpi_pkg::c_dpi_sha3_256(msg, msg.size(), dpi_digest);
          end
          sha3_pkg::L384: begin
            digestpp_dpi_pkg::c_dpi_sha3_384(msg, msg.size(), dpi_digest);
          end sha3_pkg::L512: begin
            digestpp_dpi_pkg::c_dpi_sha3_512(msg, msg.size(), dpi_digest);
          end
          default: begin
            `uvm_fatal(`gfn, $sformatf("strength[%0s] is not allowed for sha3!", strength.name()))
          end
        endcase
      end
      sha3_pkg::Shake: begin
        case (strength)
          sha3_pkg::L128: begin
            digestpp_dpi_pkg::c_dpi_shake128(msg, msg.size(), output_len, dpi_digest);
          end
          sha3_pkg::L256: begin
            digestpp_dpi_pkg::c_dpi_shake256(msg, msg.size(), output_len, dpi_digest);
          end
          default: begin
            `uvm_fatal(`gfn, $sformatf("strength[%0s] is not allowed for shake!", strength.name()))
          end
        endcase
      end
      sha3_pkg::CShake: begin
        `uvm_info(`gfn, $sformatf("fname_str: %0s", str_utils_pkg::bytes_to_str(fname_arr)), UVM_HIGH)
        `uvm_info(`gfn, $sformatf("custom_str: %0s", str_utils_pkg::bytes_to_str(custom_str_arr)), UVM_HIGH)
        if (kmac_en) begin
          // Convert the key array into a byte array for the DPI model
          unmasked_key_bytes = {<< 32 {unmasked_key}};
          dpi_key_arr = {<< byte {unmasked_key_bytes}};
          `uvm_info(`gfn, $sformatf("dpi_key_arr.size(): %0d", dpi_key_arr.size()), UVM_HIGH)
          `uvm_info(`gfn, $sformatf("dpi_key_arr: %0p", dpi_key_arr), UVM_HIGH)
          case (strength)
            sha3_pkg::L128: begin
              if (xof_en) begin
                digestpp_dpi_pkg::c_dpi_kmac128_xof(msg, msg.size(),
                                                    dpi_key_arr, dpi_key_arr.size(),
                                                    str_utils_pkg::bytes_to_str(custom_str_arr),
                                                    output_len, dpi_digest);
              end else begin
                digestpp_dpi_pkg::c_dpi_kmac128(msg, msg.size(),
                                                dpi_key_arr, dpi_key_arr.size(),
                                                str_utils_pkg::bytes_to_str(custom_str_arr),
                                                output_len, dpi_digest);
              end
            end
            sha3_pkg::L256: begin
              if (xof_en) begin
                digestpp_dpi_pkg::c_dpi_kmac256_xof(msg, msg.size(),
                                                    dpi_key_arr, dpi_key_arr.size(),
                                                    str_utils_pkg::bytes_to_str(custom_str_arr),
                                                    output_len, dpi_digest);
              end else begin
                digestpp_dpi_pkg::c_dpi_kmac256(msg, msg.size(),
                                                dpi_key_arr, dpi_key_arr.size(),
                                                str_utils_pkg::bytes_to_str(custom_str_arr),
                                                output_len, dpi_digest);
              end
            end
            default: begin
              `uvm_fatal(`gfn, $sformatf("strength[%0s] is not allowed for kmac!", strength.name()))
            end
          endcase
        end else begin
          case (strength)
            sha3_pkg::L128: begin
              digestpp_dpi_pkg::c_dpi_cshake128(msg, str_utils_pkg::bytes_to_str(fname_arr),
                                                str_utils_pkg::bytes_to_str(custom_str_arr),
                                                msg.size(), output_len, dpi_digest);
            end
            sha3_pkg::L256: begin
              digestpp_dpi_pkg::c_dpi_cshake256(msg, str_utils_pkg::bytes_to_str(fname_arr),
                                                str_utils_pkg::bytes_to_str(custom_str_arr),
                                                msg.size(), output_len, dpi_digest);
            end
            default: begin
              `uvm_fatal(`gfn, $sformatf("strength[%0s] is not allowed for cshake!", strength.name()))
            end
          endcase
        end
      end
    endcase

    `uvm_info(`gfn, $sformatf("unmasked_digest: %0p", unmasked_digest), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("dpi_digest: %0p", dpi_digest), UVM_HIGH)

    // Compare outputs from DPI model and DUT
    for (int i = 0; i < unmasked_digest.size(); i++) begin
      `DV_CHECK_EQ_FATAL(unmasked_digest[i], dpi_digest[i],
        $sformatf("Mismatch between unmasked_digest[%0d] and dpi_digest[%0d]", i, i))
    end
  endtask

endclass : kmac_base_vseq
