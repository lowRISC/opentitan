// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class kmac_scoreboard extends cip_base_scoreboard #(
    .CFG_T(kmac_env_cfg),
    .RAL_T(kmac_reg_block),
    .COV_T(kmac_env_cov)
  );
  `uvm_component_utils(kmac_scoreboard)

  // local variables

  // this bit is set if a KDF transaction is being performed
  bit in_kdf;

  // CFG fields
  bit kmac_en;
  sha3_pkg::sha3_mode_e hash_mode;
  sha3_pkg::keccak_strength_e strength;

  // CMD fields
  kmac_cmd_e kmac_cmd = CmdNone;

  // FIFO status/intr empty bit
  bit fifo_empty;

  // key length enum
  key_len_e key_len;

  // error reporting
  bit kmac_err;

  keymgr_pkg::hw_key_req_t sideload_key;

  // secret keys
  //
  // max key size is 512-bits
  bit [KMAC_NUM_SHARES-1:0][KMAC_NUM_KEYS_PER_SHARE-1:0][31:0] keys;
  bit [KMAC_NUM_SHARES-1:0][KMAC_NUM_KEYS_PER_SHARE-1:0][31:0] keymgr_keys;

  // prefix words
  bit [31:0] prefix[KMAC_NUM_PREFIX_WORDS];

  // input message
  bit [7:0] msg[$];

  // input message from keymgr
  byte kdf_msg[$];

  // output digest from KDF (256 bits each)
  bit [keymgr_pkg::KeyWidth-1:0] kdf_digest_share0;
  bit [keymgr_pkg::KeyWidth-1:0] kdf_digest_share1;

  // output digests
  bit [7:0] digest_share0[];
  bit [7:0] digest_share1[];

  // This mask is used to mask reads from the state windows.
  // We need to make this a class variable as we set the mask value
  // during the address read phase, but then need its value to persist
  // through the data read phase.
  bit [TL_DBW-1:0] state_mask;

  // TLM fifos
  uvm_tlm_analysis_fifo #(keymgr_kmac_item) kdf_req_fifo;
  uvm_tlm_analysis_fifo #(keymgr_kmac_item) kdf_rsp_fifo;

  `uvm_component_new

  function void build_phase(uvm_phase phase);
    super.build_phase(phase);
    kdf_req_fifo = new("kdf_req_fifo", this);
    kdf_rsp_fifo = new("kdf_rsp_fifo", this);
  endfunction

  function void connect_phase(uvm_phase phase);
    super.connect_phase(phase);
  endfunction

  task run_phase(uvm_phase phase);
    super.run_phase(phase);
    fork
      process_sideload_key();
      process_kdf_req_fifo();
      process_kdf_rsp_fifo();
    join_none
  endtask

  // This task will check for any sideload keys that have been provided
  virtual task process_sideload_key();
    forever begin
      // Wait for a valid sideloaded key
      cfg.sideload_vif.wait_valid(logic'(1'b1));

      // Once valid sideload keys have been seen, update scoreboard state.
      //
      // Note: max size of sideloaded key is keymgr_pkg::KeyWidth

      sideload_key = cfg.sideload_vif.sideload_key;

      `uvm_info(`gfn, $sformatf("detected valid sideload_key: %0p", sideload_key), UVM_HIGH)

      for (int i = 0; i < keymgr_pkg::KeyWidth / 32; i++) begin
        keymgr_keys[0][i] = sideload_key.key_share0[i*32 +: 32];
        keymgr_keys[1][i] = sideload_key.key_share1[i*32 +: 32];
      end

      // Sequence will drop the sideloaded key after scb can process the digest
      cfg.sideload_vif.wait_valid(logic'(1'b0));
    end
  endtask

  // This task continuously checks the `kdf_req_fifo`.
  //
  // This fifo is populated once a full KDF request has been detected,
  // and is used by the scoreboard to store the input KDF message and set
  // some internal state.
  virtual task process_kdf_req_fifo();
    keymgr_kmac_item kdf_req;
    forever begin
      kdf_req_fifo.get(kdf_req);
      `uvm_info(`gfn, $sformatf("Detected a KDF request:\n%0s", kdf_req.sprint()), UVM_HIGH)

      // signal to the rest of the scoreboard that we are now in KDF mode
      in_kdf = 1'b1;

      // store the input KDF message locally
      kdf_msg = kdf_req.byte_data_q;
      `uvm_info(`gfn, $sformatf("kdf_msg: %0p", kdf_msg), UVM_HIGH)
    end
  endtask

  // This task processes the `kdf_rsp_fifo`.
  //
  // This fifo is populated once the KMAC has sent the response digest to
  // complete the KDF request.
  // As such, `in_kdf` must always be 1 when a response item is seen, otherwise
  // something has gone horribly wrong.
  //
  // It is important to note that when in KDF mode, any messages/keys/commands sent
  // to the CSRs will not be considered as valid, so this task needs to take care of checking
  // the KDF digest and clearing internal state for the next hash operation.
  virtual task process_kdf_rsp_fifo();
    keymgr_kmac_item kdf_rsp;
    forever begin
      kdf_rsp_fifo.get(kdf_rsp);
      `uvm_info(`gfn, $sformatf("Detected a KDF response:\n%0s", kdf_rsp.sprint()), UVM_HIGH)

      // safety check that things are working properly and no random KDF operations are seen
      `DV_CHECK_FATAL(in_kdf == 1, "in_kdf is not set, scoreboard has not picked up KDF request")

      // TODO error checks

      // assign digest values
      kdf_digest_share0 = kdf_rsp.rsp_digest_share0;
      kdf_digest_share1 = kdf_rsp.rsp_digest_share1;

      check_digest();

      in_kdf = 1'b0;
    end
  endtask

  virtual task process_tl_access(tl_seq_item item, tl_channels_e channel = DataChannel);
    uvm_reg csr;
    dv_base_reg check_locked_reg;

    string csr_name = "";

    bit msgfifo_access;
    bit share0_access;
    bit share1_access;

    bit     do_read_check         = 1'b1;
    bit     write                 = item.is_write();
    uvm_reg_addr_t csr_addr       = ral.get_word_aligned_addr(item.a_addr);
    bit [TL_AW-1:0] csr_addr_mask = ral.get_addr_mask();

    bit addr_phase_read   = (!write && channel == AddrChannel);
    bit addr_phase_write  = (write && channel == AddrChannel);
    bit data_phase_read   = (!write && channel == DataChannel);
    bit data_phase_write  = (write && channel == DataChannel);

    // if access was to a valid csr, get the csr handle
    if (csr_addr inside {cfg.csr_addrs}) begin
      csr = ral.default_map.get_reg_by_offset(csr_addr);
      `DV_CHECK_NE_FATAL(csr, null)
      `downcast(check_locked_reg, csr)

      csr_name = csr.get_name();

      // if incoming access is a write to valid csr, immediately make updates
      if (addr_phase_write) begin

        // following csrs are locked by CFG_REGWEN:
        // - cfg
        // - entropy_period
        // - entropy_seed_lower
        // - entropy_seed_upper
        // - key_len
        // if writes to these csrs are seen, must check that they are not locked first.
        if (ral.cfg_regwen.locks_reg_or_fld(check_locked_reg) &&
            `gmv(ral.cfg_regwen) == 0) return;

        void'(csr.predict(.value(item.a_data), .kind(UVM_PREDICT_WRITE), .be(item.a_mask)));
      end
    end else if ((csr_addr & csr_addr_mask) inside {[KMAC_FIFO_BASE:KMAC_FIFO_END]}) begin
      // msgfifo window
      msgfifo_access = 1;
    end else if ((csr_addr & csr_addr_mask) inside {[KMAC_STATE_SHARE0_BASE:KMAC_STATE_SHARE0_END]}) begin
      // state window 0
      share0_access = 1;
    end else if ((csr_addr & csr_addr_mask) inside {[KMAC_STATE_SHARE1_BASE:KMAC_STATE_SHARE1_END]}) begin
      // state window 1
      share1_access = 1;
    end else begin
      `uvm_fatal(`gfn, $sformatf("Access unexpected addr 0x%0h", csr_addr))
    end

    // process the csr req
    // for write, update local variable and fifo at address phase
    // for read, update predication at address phase and compare at data phase
    case (csr_name)
      // add individual case item for each csr
      "intr_state": begin
        do_read_check = 1'b0;
        // TODO
      end
      "intr_enable": begin
        // no need to do anything here, functionality is tested in the automated intr tests,
        // and any issues here will become known if any checks on `intr_state` fail
      end
      "intr_test": begin
        // Predict intr_state and sample coverage
        bit [TL_DW-1:0] exp_state = `gmv(ral.intr_state) | item.a_data;
        void'(ral.intr_state.predict(.value(exp_state), .kind(UVM_PREDICT_DIRECT)));
        // TODO sample coverage
      end
      "cfg_regwen": begin
        // do nothing
      end
      "cfg": begin
        if (addr_phase_write) begin
          // don't continue if the KMAC is currently operating
          //
          // TODO this is an error case that needs to be handled
          if (!(kmac_cmd inside {CmdNone, CmdDone})) begin
            return;
          end

          kmac_en = item.a_data[KmacEn];
          hash_mode = sha3_pkg::sha3_mode_e'(item.a_data[5:4]);
          strength = sha3_pkg::keccak_strength_e'(item.a_data[3:1]);

          // TODO - sample coverage
        end
      end
      "cmd": begin
        // Writing to CMD will always result in the KMAC doing something
        //
        // TODO unless in KDF mode...need to handle errors
        if (addr_phase_write) begin
          case (kmac_cmd_e'(item.a_data))
            CmdStart: begin
              // msgfifo will now be written
              kmac_cmd = CmdStart;
            end
            CmdProcess: begin
              // kmac will now compute the digest
              kmac_cmd = CmdProcess;
            end
            CmdManualRun: begin
              // kmac will now squeeze more output data
              kmac_cmd = CmdManualRun;
            end
            CmdDone: begin
              kmac_cmd = CmdDone;
              // Calculate the digest using DPI and check for correctness
              check_digest();
              // Flush all scoreboard state to prepare for the next hash operation
              clear_state();
            end
            CmdNone: begin
              // RTL internal value, doesn't actually do anything
            end
            default: begin
              `uvm_fatal(`gfn, $sformatf("%0d is an illegal CMD value", item.a_data))
            end
          endcase
        end
      end
      "status": begin
        // STATUS is read only
        do_read_check = 1'b0;

        // TODO - in addr_phase_read update the mirror value (need to model fifo...)
        //      - in data_phase_read sample coverage
      end
      "key_len": begin
        // TODO need to do error checking
        if (addr_phase_write) begin
          key_len = key_len_e'(item.a_data);
        end
      end
      "err_code": begin
        // TODO don't do anything rn, need implement the error checking
      end
      // TODO - entropy csrs
      default: begin
        // regex match the key_share csrs
        string full_idx;
        string split_idx[$];
        string key_share;
        string key_idx;

        // KEY_SHARE csrs
        if (!uvm_re_match("key_share*", csr_name)) begin
          full_idx = csr_name.substr(9, csr_name.len()-1);
          str_utils_pkg::str_split(full_idx, split_idx, "_");
          // safety check that the regex is working correctly
          `DV_CHECK_FATAL(split_idx.size() == 2,
              $sformatf("%0s does not contain a correct key index!", full_idx))
          key_share = split_idx.pop_front();
          key_idx = split_idx.pop_front();

          // If keys are being written, update the scoreboard state
          if (addr_phase_write) begin
            keys[key_share.atoi()][key_idx.atoi()] = item.a_data;
          end
        // PREFIX csrs
        end else if (!uvm_re_match("prefix_*", csr_name)) begin
          str_utils_pkg::str_split(csr_name, split_idx, "_");
          full_idx = split_idx.pop_back();

          if (addr_phase_write) begin
            prefix[full_idx.atoi()] = item.a_data;
          end
        end
      end
    endcase

    ////////////////////////////////////////////
    // Process incoming writes to the msgfifo //
    ////////////////////////////////////////////
    //
    // One problem with the scoreboard only having access to the data written to the msgfifo
    // is that the message is post-fixed with the encoded output length if KMAC mode is used.
    //
    // However there is no way to access it other than to calculate the length of the seen digest.
    // Even though it is somewhat hacky, this is the approach we'll take.
    // If the length of the calculated output is incorrect for whatever reason (scoreboard error
    // or RTL error), then passing this value into the DPI model will result in an incorrect
    // digest comparison.
    if (msgfifo_access) begin
      if (addr_phase_write) begin
        if (kmac_cmd != CmdStart) begin
          // TODO
          //
          // If we get here we are writing to the msgfifo in an invalid state.
          // Implement error checking here.
        end else if (!cfg.under_reset) begin
          bit [7:0] full_data[4];
          bit [7:0] masked_data[];

          {<< byte {full_data}} = item.a_data;

          `uvm_info(`gfn, $sformatf("item.a_data: 0x%0x", item.a_data), UVM_HIGH)
          `uvm_info(`gfn, $sformatf("item.a_mask: 0b%0b", item.a_mask), UVM_HIGH)
          `uvm_info(`gfn, $sformatf("full_data: %0p", full_data), UVM_HIGH)

          // All writes in big-endian order will be full-word,
          // so we can generalize this to a for-loop that reverses the byte order of each word.
          // This way we can also preserve little-endian ordering.
          for (int i = 0; i < TL_DBW; i++) begin
            if (item.a_mask[i]) begin
              masked_data = `gmv(ral.cfg.msg_endianness) ? {full_data[i], masked_data} :
                                                           {masked_data, full_data[i]};
            end
          end
          msg = {msg, masked_data};

          `uvm_info(`gfn, $sformatf("masked_data: %0p", masked_data), UVM_HIGH)
          `uvm_info(`gfn, $sformatf("msg: %0p", msg), UVM_HIGH)
        end
      end
      // indicate that the msgfifo access is now over
      msgfifo_access = 0;
    end

    ///////////////////////////////////////////////////
    // Process incoming reads from the digest window //
    ///////////////////////////////////////////////////

    if (share0_access || share1_access) begin
      bit [TL_DW-1:0] digest_word;
      bit [7:0] digest_byte;
      bit  [TL_DBW-1:0] state_mask;

      `uvm_info(`gfn, $sformatf("share0: %0d", share0_access), UVM_HIGH)
      `uvm_info(`gfn, $sformatf("share1: %0d", share1_access), UVM_HIGH)

      if (data_phase_read) begin
        state_mask = item.a_mask;
        digest_word = item.d_data;

        `uvm_info(`gfn, $sformatf("state read mask: 0b%0b", state_mask), UVM_HIGH)
        `uvm_info(`gfn, $sformatf("digest_word: 0x%0x", digest_word), UVM_HIGH)

        if (`gmv(ral.cfg.state_endianness)) begin
          digest_word = {<< byte {digest_word}};
          state_mask = {<< bit {state_mask}};

          `uvm_info(`gfn, $sformatf("endian-swapped digest word: 0x%0x", digest_word), UVM_HIGH)
          `uvm_info(`gfn, $sformatf("endian-swapped read mask: 0b%0b", state_mask), UVM_HIGH)
        end
        for (int i = 0; i < TL_DBW; i++) begin
          if (state_mask[i]) begin
            digest_byte = digest_word[i*8 +: 8];
            `uvm_info(`gfn, $sformatf("digest_byte: 0x%0x", digest_byte), UVM_HIGH)

            if (share0_access) begin
              digest_share0 = {digest_share0, digest_byte};
              `uvm_info(`gfn, $sformatf("intermediate digest_share0: %0p", digest_share0), UVM_HIGH)
            end else if (share1_access) begin
              digest_share1 = {digest_share1, digest_byte};
              `uvm_info(`gfn, $sformatf("intermediate digest_share1: %0p", digest_share1), UVM_HIGH)
            end
          end
        end
      end

      // If we read the state digest in either CmdStart or CmdDone states,
      // we should read back all zeroes.
      // Check immediately and clear the digest arrays.
      if (kmac_cmd inside {CmdNone, CmdStart, CmdDone}) begin
        foreach (digest_share0[i]) begin
          `DV_CHECK_EQ_FATAL(digest_share0[i], '0,
              $sformatf("Share 0 should be zero in state %0s", kmac_cmd.name()))
          digest_share0 = {};
        end
        foreach (digest_share1[i]) begin
          `DV_CHECK_EQ_FATAL(digest_share1[i], '0,
              $sformatf("Share 1 should be zero in state %0s", kmac_cmd.name()))
          digest_share1 = {};
        end
      end
      share0_access = 0;
      share1_access = 0;
    end

    // On reads, if do_read_check, is set, then check mirrored_value against item.d_data
    if (data_phase_read && csr_name != "") begin
      if (do_read_check) begin
        `DV_CHECK_EQ(csr.get_mirrored_value(), item.d_data,
                     $sformatf("reg name: %0s", csr.get_full_name()))
      end
      void'(csr.predict(.value(item.d_data), .kind(UVM_PREDICT_READ)));
    end
  endtask : process_tl_access

  virtual function void reset(string kind = "HARD");
    super.reset(kind);
    clear_state();
  endfunction

  // This function should be called to reset internal state to prepare for a new hash operation
  virtual function void clear_state();
    msg.delete();
    kdf_msg.delete();
    keys              = '0;
    keymgr_keys       = '0;
    sideload_key      = '0;
    prefix            = '{default:0};
    digest_share0     = {};
    digest_share1     = {};
    kdf_digest_share0 = '0;
    kdf_digest_share1 = '0;
  endfunction

  // This function is called whenever a CmdDone command is issued to KMAC,
  // and will compare the seen digest against the digest calculated from the DPI model.
  //
  // Though we don't have direct access to the specified output length for XOF functions,
  // the last byte written to the msgfifo (only for XOFs) will be the number of preceding bytes
  // that encode the requested output length.
  // From this we can decode what the initially requested output length is.
  //
  // We also need to decode what the prefix is (only for KMAC), as only the encoded values
  // are written to the CSRs.  virtual function void check_digest();
  virtual function void check_digest();

    // Cast to an array so we can pass this into the DPI functions
    bit [7:0] msg_arr[];

    // Determines which kmac variant to use
    bit xof_en;

    // Set this to the calculated output length for XOFs
    int output_len_bytes;

    // Array to hold the digest read from the state windows
    bit [7:0] unmasked_digest[];

    // Array to hold the expected digest calculated by DPI model
    bit [7:0] dpi_digest[];

    // Function name and customization strings for KMAC operations
    string fname;
    string custom_str;

    // Use this to store the correct set of keys (SW-provided or sideloaded)
    bit [KMAC_NUM_SHARES-1:0][KMAC_NUM_KEYS_PER_SHARE-1:0][31:0] exp_keys;

    // The actual key used for KMAC operations
    bit [31:0] unmasked_key[$];

    // key byte-stream for the DPI model
    bit [7:0] dpi_key_arr[];

    // Intermediate array for streaming `unmasked_key` into `dpi_key_arr`
    bit [7:0] unmasked_key_bytes[];

    int key_word_len = get_key_size_words(key_len);
    int key_byte_len = get_key_size_bytes(key_len);

    `uvm_info(`gfn, $sformatf("key_word_len: %0d", key_word_len), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("key_byte_len: %0d", key_byte_len), UVM_HIGH)

    // Calculate:
    // - the expected output length in bytes
    // - if we are using the xof version of kmac
    if (in_kdf) begin
      // KDF output will always be 256 bits (32 bytes)
      output_len_bytes = 32;

      // xof_en is 1 when the padded output length is 0,
      // but this will never happen in KDF
      xof_en = 0;
    end else begin
      get_digest_len_and_xof(output_len_bytes, xof_en, msg);

      // quick check that the calculated output length is the same
      // as the number of bytes read from the digest window
      `DV_CHECK_EQ_FATAL(digest_share0.size(), output_len_bytes,
          $sformatf("Calculated output length doesn't match actual output length!"))
    end

    `uvm_info(`gfn, $sformatf("output_len_bytes: %0d", output_len_bytes), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("xof_en: %0d", xof_en), UVM_HIGH)

    // initialize arrays
    dpi_digest = new[output_len_bytes];
    unmasked_digest = new[output_len_bytes];

    /////////////////////////////////
    // Calculate the actual digest //
    /////////////////////////////////
    if (cfg.enable_masking) begin
      if (in_kdf) begin
        unmasked_digest = {<< byte {kdf_digest_share0 ^ kdf_digest_share1}};
      end else begin
        foreach (unmasked_digest[i]) begin
          unmasked_digest[i] = digest_share0[i] ^ digest_share1[i];
        end
      end
    end else begin
      if (in_kdf) begin
        unmasked_digest = {<< byte {kdf_digest_share0}};
      end else begin
        unmasked_digest = digest_share0;
      end
    end
    `uvm_info(`gfn, $sformatf("unmasked_digest: %0p", unmasked_digest), UVM_HIGH)

    ///////////////////////////////////////////////////////////
    // Calculate the expected digest using the DPI-C++ model //
    ///////////////////////////////////////////////////////////
    if (in_kdf) begin
      // kdf message is a byte array, cast to bit[7:0]
      msg_arr = new[kdf_msg.size()];
      foreach (kdf_msg[i]) begin
        msg_arr[i] = kdf_msg[i];
      end
    end else begin
      msg_arr = msg;
    end
    `uvm_info(`gfn, $sformatf("msg_arr for DPI mode: %0p", msg_arr), UVM_HIGH)

    case (hash_mode)
      ///////////
      // SHA-3 //
      ///////////
      sha3_pkg::Sha3: begin
        case (strength)
          sha3_pkg::L224: begin
            digestpp_dpi_pkg::c_dpi_sha3_224(msg_arr, msg_arr.size(), dpi_digest);
          end
          sha3_pkg::L256: begin
            digestpp_dpi_pkg::c_dpi_sha3_256(msg_arr, msg_arr.size(), dpi_digest);
          end
          sha3_pkg::L384: begin
            digestpp_dpi_pkg::c_dpi_sha3_384(msg_arr, msg_arr.size(), dpi_digest);
          end
          sha3_pkg::L512: begin
            digestpp_dpi_pkg::c_dpi_sha3_512(msg_arr, msg_arr.size(), dpi_digest);
          end
          default: begin
            `uvm_fatal(`gfn, $sformatf("strength[%0s] is not allowed for sha3", strength.name()))
          end
        endcase
      end
      ///////////
      // SHAKE //
      ///////////
      sha3_pkg::Shake: begin
        case (strength)
          sha3_pkg::L128: begin
            digestpp_dpi_pkg::c_dpi_shake128(msg_arr, msg_arr.size(), output_len_bytes, dpi_digest);
          end
          sha3_pkg::L256: begin
            digestpp_dpi_pkg::c_dpi_shake256(msg_arr, msg_arr.size(), output_len_bytes, dpi_digest);
          end
          default: begin
            `uvm_fatal(`gfn, $sformatf("strength[%0s] is not allowed for shake", strength.name()))
          end
        endcase
      end
      ////////////
      // CSHAKE //
      ////////////
      sha3_pkg::CShake: begin
        if (kmac_en) begin
          // Get the fname and custom_str string values from the writes to PREFIX csrs
          get_fname_and_custom_str(fname, custom_str);

          // Calculate the unmasked key
          exp_keys = `gmv(ral.cfg.sideload) ? keymgr_keys : keys;
          for (int i = 0; i < key_word_len; i++) begin
            // Sideloaded keys are treated as two-share masked form by default, need to xor them
            if (cfg.enable_masking || `gmv(ral.cfg.sideload)) begin
              unmasked_key.push_back(exp_keys[0][i] ^ exp_keys[1][i]);
            end else begin
              unmasked_key.push_back(exp_keys[0][i]);
            end
            `uvm_info(`gfn, $sformatf("unmasked_key[%0d] = 0x%0x", i, unmasked_key[i]), UVM_HIGH)
          end

          // Convert the key array into a byte array for the DPI model
          unmasked_key_bytes = {<< 32 {unmasked_key}};
          dpi_key_arr = {<< byte {unmasked_key_bytes}};
          `uvm_info(`gfn, $sformatf("dpi_key_arr.size(): %0d", dpi_key_arr.size()), UVM_HIGH)
          `uvm_info(`gfn, $sformatf("dpi_key_arr: %0p", dpi_key_arr), UVM_HIGH)

          case (strength)
            sha3_pkg::L128: begin
              if (xof_en) begin
                digestpp_dpi_pkg::c_dpi_kmac128_xof(msg_arr, msg_arr.size(),
                                                    dpi_key_arr, dpi_key_arr.size(),
                                                    custom_str,
                                                    output_len_bytes, dpi_digest);
              end else begin
                digestpp_dpi_pkg::c_dpi_kmac128(msg_arr, msg_arr.size(),
                                                dpi_key_arr, dpi_key_arr.size(),
                                                custom_str,
                                                output_len_bytes, dpi_digest);
              end
            end
            sha3_pkg::L256: begin
              if (xof_en) begin
                digestpp_dpi_pkg::c_dpi_kmac256_xof(msg_arr, msg_arr.size(),
                                                    dpi_key_arr, dpi_key_arr.size(),
                                                    custom_str,
                                                    output_len_bytes, dpi_digest);
              end else begin
                digestpp_dpi_pkg::c_dpi_kmac256(msg_arr, msg_arr.size(),
                                                dpi_key_arr, dpi_key_arr.size(),
                                                custom_str,
                                                output_len_bytes, dpi_digest);
              end
            end
            default: begin
              `uvm_fatal(`gfn, $sformatf("strength[%0s] is now allowed for kmac", strength.name()))
            end
          endcase
        end else begin
          // regular cshake
          // TODO - leave this section empty for now, we don't use plain cshake functionality
          case (strength)
            sha3_pkg::L128: begin
            end
            sha3_pkg::L256: begin
            end
            default: begin
              `uvm_fatal(`gfn, $sformatf("strength[%0s] is now allowed for cshake", strength.name()))
            end
          endcase
        end
      end
    endcase

    `uvm_info(`gfn, $sformatf("dpi_digest: %0p", dpi_digest), UVM_HIGH)

    /////////////////////////////////////////
    // Compare actual and expected digests //
    /////////////////////////////////////////
    for (int i = 0; i < output_len_bytes; i++) begin
      `DV_CHECK_EQ_FATAL(unmasked_digest[i], dpi_digest[i],
          $sformatf("Mismatch between unmasked_digest[%0d] and dpi_digest[%0d]", i, i))
    end

  endfunction

  // This function is used to calculate the requested digest length
  virtual function void get_digest_len_and_xof(ref int output_len, ref bit xof_en,
                                               ref bit [7:0] msg[$]);
    xof_en = 0;
    case (hash_mode)
      // For SHA3 hashes, the output length is the same as the security strength.
      sha3_pkg::Sha3: begin
        case (strength)
          sha3_pkg::L224: begin
            output_len = 224 / 8; // 28
          end
          sha3_pkg::L256: begin
            output_len = 256 / 8; // 32
          end
          sha3_pkg::L384: begin
            output_len = 384 / 8; // 48
          end
          sha3_pkg::L512: begin
            output_len = 512 / 8; // 64
          end
          default: begin
            `uvm_fatal(`gfn, $sformatf("strength[%0s] is not allowed for sha3", strength.name()))
          end
        endcase
      end
      // For Shake hashes, the output length isn't encoded anywhere,
      // so we just return the length of the state digest array.
      sha3_pkg::Shake: begin
        output_len = digest_share0.size();
      end
      // CShake is where things get more interesting.
      // We need to essentially decode the encoded output length that is
      // written to the msgfifo as a post-fix to the actual message.
      sha3_pkg::CShake: begin
        bit [MAX_ENCODE_WIDTH-1:0] full_len = '0;
        // the very last byte written to msgfifo is the number of bytes that
        // when put together represent the encoded output length.
        bit [7:0] num_encoded_byte = msg.pop_back();

        for (int i = 0; i < num_encoded_byte; i++) begin
          full_len[i*8 +: 8] = msg.pop_back();
        end

        // We should set xof_en if `right_encode(0)` was written to the msgfifo after the message.
        // right_encode(0) = '{'h0, 'h1}
        if (num_encoded_byte == 1 && full_len == 0) begin
          xof_en = 1;
          // can't set  the output length to 0, so we fall back to the Shake behavior here
          output_len = digest_share0.size();
        end else begin
          output_len = full_len / 8;
        end
      end
    endcase
  endfunction

  // This function is used to calculate the fname and custom_str string values
  // from the data written to the PREFIX csrs
  //
  // Strings are encoded as:
  //  `encode_string(S) = left_encode(len(S)) || S`
  virtual function void get_fname_and_custom_str(ref string fname, ref string custom_str);
    bit [7:0] prefix_bytes[$];
    // The very first byte of each encoded string represents the number of bytes
    // that make up the encoded string's length.
    bit [7:0] num_enc_bytes_of_str_len;

    bit [16:0] str_len;

    byte fname_arr[];
    byte custom_str_arr[];

    prefix_bytes = {<< 32 {prefix}};
    prefix_bytes = {<< byte {prefix_bytes}};

    `uvm_info(`gfn, $sformatf("prefix: %0p", prefix), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("prefix_bytes: %0p", prefix_bytes), UVM_HIGH)

    // fname comes first in the PREFIX registers

    // This value should be 1
    num_enc_bytes_of_str_len = prefix_bytes.pop_front();
    `DV_CHECK_EQ(num_enc_bytes_of_str_len, 1,
        $sformatf("Only one byte should be used to encode len(fname)"))

    // The string length is always in terms of bits, need to convert to byte length
    str_len = prefix_bytes.pop_front() / 8;

    fname_arr  = new[str_len];
    for (int i = 0; i < str_len; i++) begin
      fname_arr[i] = byte'(prefix_bytes.pop_front());
    end

    // custom_str is next

    num_enc_bytes_of_str_len = prefix_bytes.pop_front();

    // convert string length to length in bytes
    for (int i = 0; i < num_enc_bytes_of_str_len; i++) begin
      str_len[(num_enc_bytes_of_str_len  - i - 1)*8 +: 8] = prefix_bytes.pop_front();
    end
    str_len /= 8;

    custom_str_arr = new[str_len];
    for (int i = 0; i < str_len; i++) begin
      custom_str_arr[i] = byte'(prefix_bytes.pop_front());
    end

    // Convert the byte arrays into strings
    fname = str_utils_pkg::bytes_to_str(fname_arr);
    custom_str = str_utils_pkg::bytes_to_str(custom_str_arr);

    `uvm_info(`gfn, $sformatf("decoded fname: %0s", fname), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("decoded custom_str: %0s", custom_str), UVM_HIGH)
  endfunction

  function void check_phase(uvm_phase phase);
    super.check_phase(phase);
    // post test checks - ensure that all local fifos and queues are empty
  endfunction

endclass
