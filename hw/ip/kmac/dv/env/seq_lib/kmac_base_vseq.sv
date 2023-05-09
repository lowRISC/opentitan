// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// This base sequence consists of common kmac tasks and functions.
// In this sequence, when it uses a plain `csr_rd` without checking, the read value should be
// predicted and checked in the kmac scoreboard.
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

  // Controls whether to actually enable sideloading functionality via cfg_shadowed register.
  rand bit reg_en_sideload;

  // entropy mode
  rand kmac_pkg::entropy_mode_e entropy_mode = EntropyModeSw;
  // We do not want to change the value of `entropy_mode` in between hashing iterations.
  //
  // So we use a static entropy mode value to hold the same mode through the whole test,
  // and constrain `entropy_mode` accordingly.
  kmac_pkg::entropy_mode_e static_entropy_mode = EntropyModeSw;

  // entropy fast process mode
  rand bit entropy_fast_process;

  // entropy ready
  rand bit entropy_ready;

  // process the digest when mode strength does not match
  rand bit en_unsupported_modestrength;

  // Message masking
  rand bit msg_mask;

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

  // Error control fields
  rand kmac_pkg::err_code_e kmac_err_type;
  // When creating errors by issue the wrong SW command, we need to have access
  // to what operational state to send an erroneous command in,
  // as well as the proper random incorrect command to send.
  rand sha3_pkg::sha3_st_e err_sw_cmd_seq_st;
  rand kmac_pkg::kmac_cmd_e err_sw_cmd_seq_cmd;

  // Entropy related variables
  rand bit [9:0] hash_threshold;
  rand bit hash_cnt_clr;
  rand bit entropy_req;
  rand bit entropy_timer_en;
  rand bit [EntropyPeriodReserved-1:0] prescaler_val;
  rand bit [TL_DW-KmacWaitTimer-1:0] entropy_wait_timer;

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

  // Constrain valid and invalid mode/strength combinations based on the following:
  // - only 128/256 bit strengths are supported for Shake/CShake
  // - 128 bit strength is not supported for Sha3
  constraint strength_c {
    solve kmac_err_type before hash_mode;
    solve kmac_err_type before strength;

    if (kmac_err_type == kmac_pkg::ErrUnexpectedModeStrength) {
      (hash_mode inside {sha3_pkg::Shake, sha3_pkg::CShake}) ->
        !(strength inside {sha3_pkg::L128, sha3_pkg::L256});

      (hash_mode == sha3_pkg::Sha3) -> (strength == sha3_pkg::L128);
    } else {
      (hash_mode inside {sha3_pkg::Shake, sha3_pkg::CShake}) ->
        (strength inside {sha3_pkg::L128, sha3_pkg::L256});

      (hash_mode == sha3_pkg::Sha3) -> (strength != sha3_pkg::L128);
    }
  }

  constraint key_len_c {
    (reg_en_sideload) -> key_len == Key256;
  }

  constraint entropy_mode_c {
    if (kmac_err_type == kmac_pkg::ErrIncorrectEntropyMode) {
      !(entropy_mode inside {EntropyModeSw, EntropyModeEdn});
    } else {
      entropy_mode == static_entropy_mode;
    }
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

  // Create an appropriate incorrect command based on what state to send an error in
  constraint err_sw_cmd_seq_c {
    solve err_sw_cmd_seq_st before err_sw_cmd_seq_cmd;
    if (kmac_err_type == kmac_pkg::ErrSwCmdSequence) {
      if (err_sw_cmd_seq_st == sha3_pkg::StIdle) {
        err_sw_cmd_seq_cmd inside {CmdProcess, CmdManualRun, CmdDone};
      } else if (err_sw_cmd_seq_st == sha3_pkg::StAbsorb) {
        err_sw_cmd_seq_cmd inside {CmdStart, CmdManualRun, CmdDone};
      } else if (err_sw_cmd_seq_st == sha3_pkg::StSqueeze) {
        err_sw_cmd_seq_cmd inside {CmdStart, CmdProcess};
      } else if (err_sw_cmd_seq_st inside {sha3_pkg::StManualRun, sha3_pkg::StFlush}) {
        err_sw_cmd_seq_cmd != CmdNone;
      }
    }
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

  constraint entropy_period_c {
    if (entropy_mode == EntropyModeEdn && cfg.enable_masking) {
      if (entropy_timer_en) {
        (prescaler_val + 1) * entropy_wait_timer >
          // If zero delay case, the max delay is 0.
          // Kmac requests 4 EDN entropies, and add 10 cycles as extra buffer for domain crossing.
          (cfg.m_edn_pull_agent_cfgs[0].device_delay_max * 4 + 10) *
          (cfg.edn_clk_freq_mhz / cfg.clk_freq_mhz + 1);
      } else {
        entropy_wait_timer == 0;
      }
    }
    solve entropy_mode before prescaler_val, entropy_wait_timer;
  }

  virtual task dut_init(string reset_kind = "HARD");
    // KMAC has dut and edn reset. If assign kmac_vif_init() values after `super.dut_init()`,
    // and if dut reset deasserts earlier than edn reset, some KMAC outputs might remain X or Z
    // when dut clock is running.
    kmac_vif_init();
    super.dut_init();
    if (do_kmac_init) kmac_init();
  endtask

  virtual task pre_start();
    super.pre_start();
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(static_entropy_mode,
        static_entropy_mode inside {EntropyModeSw, EntropyModeEdn};)
  endtask

  virtual task kmac_vif_init();
    // Any value that is not `lc_ctrl_pkg::On` is considered `lc_ctrl_pkg::Off`.
    cfg.kmac_vif.drive_lc_escalate(lc_ctrl_pkg::Off);
  endtask

  // setup basic kmac features
  virtual task kmac_init(bit wait_init = 1, bit keymgr_app_intf = 0);
    // Wait for KMAC to reach idle state
    if (wait_init) begin
      wait (cfg.kmac_vif.idle_o == prim_mubi_pkg::MuBi4True);
      `uvm_info(`gfn, "reached idle state", UVM_HIGH)
    end

    // set interrupts
    cfg_interrupts(.interrupts(enable_intr));
    // For error cases that does not support in scb, predict its value so can be used in
    // `check_err` task.
    if (cfg.en_scb == 0) void'(ral.intr_enable.predict(enable_intr));
    `uvm_info(`gfn, $sformatf("intr[KmacDone] = %0b", enable_intr[KmacDone]), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("intr[KmacFifoEmpty] = %0b", enable_intr[KmacFifoEmpty]), UVM_HIGH)
    `uvm_info(`gfn, $sformatf("intr[KmacErr] = %0b", enable_intr[KmacErr]), UVM_HIGH)

    if (kmac_err_type == ErrWaitTimerExpired && entropy_mode == EntropyModeEdn &&
        cfg.enable_masking) begin
      csr_wr(.ptr(ral.entropy_period), .value(1'b1 << KmacWaitTimer));
    end else begin
      csr_wr(.ptr(ral.entropy_period.wait_timer), .value(entropy_wait_timer));
      csr_wr(.ptr(ral.entropy_period.prescaler), .value(prescaler_val));
    end

    csr_wr(.ptr(ral.entropy_refresh_threshold_shadowed), .value(hash_threshold));
    wr_hash_cnt_clear_cmd();
    wr_entropy_req_cmd();

    // setup CFG csr with default random values
    ral.cfg_shadowed.kmac_en.set(kmac_en);
    ral.cfg_shadowed.kstrength.set(strength);
    ral.cfg_shadowed.mode.set(hash_mode);
    ral.cfg_shadowed.msg_endianness.set(msg_endian);
    ral.cfg_shadowed.state_endianness.set(state_endian);
    ral.cfg_shadowed.entropy_mode.set(entropy_mode);
    ral.cfg_shadowed.entropy_fast_process.set(entropy_fast_process);
    ral.cfg_shadowed.entropy_ready.set(entropy_ready);
    ral.cfg_shadowed.msg_mask.set(msg_mask);
    ral.cfg_shadowed.err_processed.set(1'b0);
    ral.cfg_shadowed.en_unsupported_modestrength.set(en_unsupported_modestrength);
    ral.cfg_shadowed.sideload.set(reg_en_sideload);

    csr_update(.csr(ral.cfg_shadowed));

    // setup KEY_LEN csr
    // The key length will be override to 256 bits if design uses keymgr app interface or the
    // sideload is enabled.
    if (!reg_en_sideload || $urandom_range(0, 1)) csr_wr(.ptr(ral.key_len), .value(key_len));

    // print debug info
    `uvm_info(`gfn, $sformatf("KMAC INITIALIZATION INFO:\n%0s", convert2string()), UVM_HIGH)
  endtask

  virtual task read_regwen_and_rand_write_locked_regs();
    bit [TL_DW-1:0] data;
    csr_rd(.ptr(ral.cfg_regwen), .value(data));
    // Randomly write locked registers only if the cfg_regwen is locked.
    if (data == 0) begin
      csr_wr(.ptr(ral.entropy_period), .value($urandom_range(0, 32'hFFFF_FFFF)));
    end
  endtask

  // This task reads out the STATUS and INTR_STATE csrs so scb can check the status
  virtual task check_state();
    bit [TL_DW-1:0] data;

    csr_rd(.ptr(ral.status), .value(data));

    csr_rd(.ptr(ral.intr_state), .value(data));
    csr_wr(.ptr(ral.intr_state), .value(data));
  endtask

  virtual task check_err(bit clear_err = 1'b1);
    bit [TL_DW-1:0] err_data;
    // wait for several cycles to allow interrupt to propagate
    cfg.clk_rst_vif.wait_clks(10);
    csr_utils_pkg::wait_no_outstanding_access();
    `uvm_info(`gfn, "Starting to check error", UVM_HIGH)
    if (enable_intr[KmacErr]) begin
      bit [TL_DW-1:0] intr_pins;
      // interrupt will take 2 cycles to propagate to the output pins
      cfg.clk_rst_vif.wait_clks(2);
      intr_pins = cfg.intr_vif.sample();
      `uvm_info(`gfn, "checking kmac_err interrupt", UVM_HIGH)
      `DV_CHECK(intr_pins[KmacErr] == 1, "intr_pins[KmacErr] is not set!")
    end
    `uvm_info(`gfn, "checking intr_state csr", UVM_HIGH)
    csr_rd(.ptr(ral.intr_state), .value(err_data));
    csr_wr(.ptr(ral.intr_state), .value(err_data));

    csr_rd(.ptr(ral.err_code), .value(err_data));

    // only clear the error if error is actually set,
    // otherwise we effectively reset the design
    if (cfg.enable_masking && clear_err &&
        kmac_err_type inside {kmac_pkg::ErrIncorrectEntropyMode,
                              kmac_pkg::ErrWaitTimerExpired}) begin
      cfg.clk_rst_vif.wait_clks($urandom_range(10, 50));
      // After entropy related errors, cannot set `err_processed` and `entropy_ready` together.
      // Otherwise design will ignore the `entropy_ready` field.
      csr_wr(.ptr(ral.cfg_shadowed.err_processed), .value(1));
    end else if (kmac_err_type == kmac_pkg::ErrKeyNotValid) begin
      csr_wr(.ptr(ral.cfg_shadowed.err_processed), .value(1));
    end
    `uvm_info(`gfn, "Finished checking error", UVM_HIGH)
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
            $sformatf("en_sideload: %0b\n", reg_en_sideload),
            $sformatf("provide_sideload_key: %0b\n", provide_sideload_key),
            $sformatf("fname_arr: %0p\n", fname_arr),
            $sformatf("fname: %0s\n", str_utils_pkg::bytes_to_str(fname_arr)),
            $sformatf("custom_str_arr: %0p\n", custom_str_arr),
            $sformatf("custom_str: %0s\n", str_utils_pkg::bytes_to_str(custom_str_arr)),
            $sformatf("entropy_mode: %0s\n", entropy_mode.name()),
            $sformatf("entropy_fast_process: %0b\n", entropy_fast_process),
            $sformatf("entropy_ready: %0b\n", entropy_ready),
            $sformatf("en_unsupported_modestrength %0b\n", en_unsupported_modestrength)};
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
      bit [7:0] prefix_word_arr[] = new[4];
      for (int j = i*4; (j < i*4 + 4) && (j < prefix_bytes.size()); j++) begin
        prefix_word_arr[j % 4] = prefix_bytes[j];
      end
      prefix_arr[i] = {<< byte {prefix_word_arr}};
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
      csr_wr(.ptr(csr), .value(prefix_arr[i]));
    end
  endtask

  // This task writes the given command to the CMD csr
  virtual task issue_cmd(kmac_cmd_e cmd);
    csr_wr(.ptr(ral.cmd), .value(cmd));
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
        csr_wr(.ptr(csr), .value(key_share[i][j]));
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
    for (int i = 0; i < kmac_reg_pkg::NumSeedsEntropyLfsr; i++) begin
      csr_wr(.ptr(ral.entropy_seed[i]), .value($urandom()));
    end
  endtask

  // Call this task to initiate a KMAC_APP hashing operation
  virtual task send_kmac_app_req(kmac_app_e mode);
    kmac_app_host_seq kmac_app_seq;
    `uvm_create_on(kmac_app_seq, p_sequencer.kmac_app_sequencer_h[mode]);
    `DV_CHECK_RANDOMIZE_FATAL(kmac_app_seq)
    kmac_app_seq.msg_size_bytes = msg.size();
    `uvm_send(kmac_app_seq)
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
  virtual task write_msg(bit [7:0] msg_arr[],
                         bit blocking = $urandom_range(0, 1),
                         bit wait_for_fifo_has_capacity = 1);

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

      // Check that there is actually room in the fifo before we start writing anything.
      // Will skip this check if it is used in error case, where the fifo full is forced to high.
      if (wait_for_fifo_has_capacity) wait_fifo_has_capacity();

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
      tl_access(.addr(ral.get_addr_from_offset(fifo_addr)),
                .write(1),
                .data(data_word),
                .mask(data_mask),
                .blocking(blocking));
    end

    // wait for all msgfifo accesses to complete
    wait_no_outstanding_access();
    // read out status/intr_state CSRs to check
    check_state();
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
    bit [TL_DW-1:0] status_data;

    // read out interrupt state and clear any set interrupts (fifo_empty).
    csr_rd(.ptr(ral.intr_state), .value(irq_data));
    csr_wr(.ptr(ral.intr_state), .value(irq_data));

    csr_spinwait(.ptr(ral.status.fifo_full), .exp_data(1'b0));
  endtask

  // This task waits for the kmac_done interrupt to trigger,
  // or waits for ral.intr_state.kmac_done to be high if interrupts are disabled.
  virtual task wait_for_kmac_done();
    bit [TL_DW-1:0] intr_state;
    if (enable_intr[KmacDone]) begin
      wait(cfg.intr_vif.pins[KmacDone] == 1'b1);
      // wait a few cycles to slightly loosen timing requirements on scoreboard
      cfg.clk_rst_vif.wait_clks(5);
      check_interrupts(.interrupts(1 << KmacDone),
                       .check_set(1'b1));
    end else begin
      // Loosen up the `kmac_done` checks slightly to ease timing pressure on the cycle accurate
      // model, instead of spinwaiting, we now do a "before" and "after" CSR read.

      // First do a backdoor read to make sure we don't encounter any race conditions with the
      // design.
      csr_rd_check(.ptr(ral.intr_state.kmac_done), .compare_value(1'b0), .backdoor(1'b1));

      // Wait a long time for hashing to finish, then check that `kmac_done` is set
      if (cfg.enable_masking) begin
        // If masked, wait for some time past the max latency of the EDN agent in case
        // an EDN request is sent right as CmdProcess is seen by the KMAC.
        cfg.edn_clk_rst_vif.wait_clks(2 * cfg.m_edn_pull_agent_cfgs[0].device_delay_max);
        cfg.clk_rst_vif.wait_clks(1000);
      end else begin
        cfg.clk_rst_vif.wait_clks(150);
      end

      csr_rd_check(.ptr(ral.intr_state.kmac_done), .compare_value(1'b1));
    end
    // read and clear intr_state
    csr_rd(.ptr(ral.intr_state), .value(intr_state));
    csr_wr(.ptr(ral.intr_state), .value(intr_state));
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
        // send an incorrect SW command, this will be dropped internally,
        // so need to send the correct command afterwards.
        if (kmac_err_type == kmac_pkg::ErrSwCmdSequence &&
            err_sw_cmd_seq_st == sha3_pkg::StSqueeze) begin
          issue_cmd(err_sw_cmd_seq_cmd);
          check_err();
        end

        squeeze_digest();
        wr_hash_cnt_clear_cmd();
        wr_entropy_req_cmd();
      end

      `uvm_info(`gfn, $sformatf("remaining_output_len: %0d", remaining_output_len), UVM_HIGH)
    end

  endtask

  virtual task check_hash_cnt();
    bit [TL_DW-1:0] val;
    csr_rd(.ptr(ral.entropy_refresh_hash_cnt), .value(val));
  endtask

  // The hash_cnt_clr is `r0w1c` field.
  // If user wants to set `hash_cnt_clr`, this task will always write 1 to the register.
  // If user do not want to set `hash_cnt_clr`, this task has 10% possibility to write 0 to the
  // register.
  virtual task wr_hash_cnt_clear_cmd();
    if (hash_cnt_clr || $urandom_range(0, 9) == 9) begin
      csr_wr(.ptr(ral.cmd.hash_cnt_clr), .value(hash_cnt_clr));
    end
  endtask

  // The entropy_req is `r0w1c` field.
  // If user wants to set `entropy_req`, this task will always write 1 to the register.
  // If user do not want to set `entropy_req`, this task has 10% possibility to write 0 to the
  // register.
  virtual task wr_entropy_req_cmd();
    if (entropy_req || $urandom_range(0, 9) == 9) begin
      csr_wr(.ptr(ral.cmd.entropy_req), .value(entropy_req));
    end
  endtask

  // This task checks after a local or global escalation, the KMAC is locked and cannot process any
  // more kmac SW operation.
  virtual task kmac_sw_lock_check();
    kmac_pkg::kmac_cmd_e rand_cmd;
    bit [7:0] share[];
    `DV_CHECK_STD_RANDOMIZE_FATAL(rand_cmd)
    `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(msg, msg.size() inside {[1:100]};)

    kmac_init(0);
    set_prefix();
    write_key_shares();
    provide_sw_entropy();
    issue_cmd(rand_cmd);
    write_msg(msg, .wait_for_fifo_has_capacity(0));
    read_digest_chunk(KMAC_STATE_SHARE0_BASE, keccak_block_size, share);
    foreach (share[i]) `DV_CHECK_EQ_FATAL(share[i], '0)
    read_digest_chunk(KMAC_STATE_SHARE1_BASE, keccak_block_size, share);
    foreach (share[i]) `DV_CHECK_EQ_FATAL(share[i], '0)
  endtask

  // This task send requests to all app interfaces and expect none of them to response until reset.
  virtual task kmac_app_lock_check();
    kmac_app_e mode = mode.first;

    do begin
      `DV_CHECK_STD_RANDOMIZE_WITH_FATAL(msg, msg.size() inside {[1:100]};)
      fork begin
        automatic kmac_app_e kmac_app_mode = mode;
        fork
          send_kmac_app_req(kmac_app_mode);
          wait (cfg.under_reset);
        join_any
        p_sequencer.kmac_app_sequencer_h[kmac_app_mode].stop_sequences();
        disable fork;
        `DV_CHECK_EQ_FATAL(cfg.under_reset, 1,
            $sformatf("App interface %0s should not response during fatal error", mode.name))
      end join_none
       // Add #0 to ensure that this thread starts executing before any subsequent call
      #0;
     mode = mode.next;
    end while (mode != mode.first);

    // Wait to make sure no valid data comes back.
    cfg.clk_rst_vif.wait_clks($urandom_range(100, 2000));
  endtask

endclass : kmac_base_vseq
