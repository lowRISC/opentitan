// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sequence that probes into AES to verify that the masking can be switched off if
// these four conditions are met together:
// - The corresponding Sec parameter is enabled.
// - The force_masks configuration bit is set.
// - EDN produces the correct seed for the AES masking PRNG to output an all-zero vector.
// - Share 1 of the initial key is an all-zero vector.
class chip_sw_aes_masking_off_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_sw_aes_masking_off_vseq)

  `uvm_object_new

  string aes_cipher_core_path;
  int unsigned block_ctr;
  int unsigned num_blocks;

  function automatic bit hdl_read_bit(string path, string failure_msg);
    bit val;
    `DV_CHECK_FATAL(uvm_hdl_read(path, val), failure_msg)
    return val;
  endfunction

  function automatic logic hdl_read_logic(string path);
    logic val;
    `DV_CHECK_FATAL(uvm_hdl_read(path, val))
    return val;
  endfunction

  function automatic aes_pkg::sp2v_e hdl_read_sp2v(string path);
    logic [aes_pkg::Sp2VWidth-1:0] val;
    `DV_CHECK_FATAL(uvm_hdl_read(path, val))
    return aes_pkg::sp2v_e'(val);
  endfunction

  function automatic logic [aes_pkg::WidthPRDMasking-1:0] hdl_read_prd(string path);
    logic [aes_pkg::WidthPRDMasking-1:0] val;
    `DV_CHECK_FATAL(uvm_hdl_read(path, val))
    return val;
  endfunction

  function automatic logic [255:0] hdl_read_aes_key_share(string path);
    logic [255:0] val;
    `DV_CHECK_FATAL(uvm_hdl_read(path, val))
    return val;
  endfunction

  function automatic logic [127:0] hdl_read_aes_state_share(string path);
    logic [127:0] val;
    `DV_CHECK_FATAL(uvm_hdl_read(path, val))
    return val;
  endfunction

  task check_masking_prng();

    string aes_masking_prng_path;
    bit allow_forcing_masks;
    logic force_masks;
    logic reseed_req;
    logic reseed_ack;
    logic [aes_pkg::WidthPRDMasking-1:0] prd;

    // Set path to masking PRNG.
    aes_masking_prng_path =
        $sformatf("%s.gen_masks.u_aes_prng_masking", aes_cipher_core_path);

    // Check parameter value.
    allow_forcing_masks = hdl_read_bit($sformatf("%s.SecAllowForcingMasks", aes_masking_prng_path),
        "Could not read SecAllowForcingMasks parameter value.");
    `DV_CHECK_EQ_FATAL(allow_forcing_masks, 1'b1,
        "SecAllowForcingMasks parameter seems not to be enabled.")

    // Wait for config bit to be set.
    `uvm_info(`gfn, "Waiting for force_masks config bit to be set.", UVM_LOW)
    `DV_SPINWAIT(
      forever begin
        force_masks = hdl_read_logic($sformatf("%s.force_masks_i", aes_masking_prng_path));
        if (force_masks == 1'b1) break;
        @(cfg.chip_vif.cpu_clk_rst_if.cbn);
      end
    )

    // Wait for masking PRNG reseed to finish.
    `uvm_info(`gfn, "Waiting for AES masking PRNG reseed to finish.", UVM_LOW)
    `DV_SPINWAIT(
      forever begin
        reseed_req = hdl_read_logic($sformatf("%s.reseed_req_i", aes_masking_prng_path));
        reseed_ack = hdl_read_logic($sformatf("%s.reseed_ack_o", aes_masking_prng_path));
        @(cfg.chip_vif.cpu_clk_rst_if.cbn);
        if (reseed_req == 1'b1 && reseed_ack == 1'b1) break;
      end
    )

    // Verify that PRNG output remains zero while doing some AES encryptions.
    `uvm_info(`gfn, "Verifying that AES masking PRNG outputs zero.", UVM_LOW)
    while (block_ctr < num_blocks) begin
      prd = hdl_read_prd($sformatf("%s.data_o", aes_masking_prng_path));
      `DV_CHECK_EQ_FATAL(prd, '0, "PRNG output not equal zero.")
      @(cfg.chip_vif.cpu_clk_rst_if.cbn);
    end
  endtask

  task check_cipher_core();

    bit masking;
    aes_pkg::sp2v_e in_valid;
    aes_pkg::sp2v_e in_ready;
    aes_pkg::sp2v_e crypt;
    aes_pkg::sp2v_e sub_bytes_en;
    aes_pkg::sp2v_e sub_bytes_out_req;
    aes_pkg::sp2v_e state_we;
    aes_pkg::sp2v_e out_valid;
    aes_pkg::sp2v_e out_ready;
    logic [255:0] key_init_share1;
    logic [127:0] state_init_share1;
    logic [127:0] state_d_share1;
    logic [127:0] state_o_share1;
    logic [127:0] sb_in_mask;
    logic [127:0] sb_out_mask;

    // Check parameter value.
    masking = hdl_read_bit($sformatf("%s.SecMasking", aes_cipher_core_path),
        "Could not read SecMasking parameter value.");
    `DV_CHECK_EQ_FATAL(masking, 1'b1,
        "SecMasking parameter seems not to be enabled.")

    // Wait for first encryption to start.
    `uvm_info(`gfn, "Waiting for first encryption to start.", UVM_LOW)
    `DV_SPINWAIT(
      forever begin
        in_valid = hdl_read_sp2v($sformatf("%s.in_valid_i", aes_cipher_core_path));
        in_ready = hdl_read_sp2v($sformatf("%s.in_ready_o", aes_cipher_core_path));
        crypt = hdl_read_sp2v($sformatf("%s.crypt_i", aes_cipher_core_path));
        if (in_valid == aes_pkg::SP2V_HIGH && in_ready == aes_pkg::SP2V_HIGH &&
            crypt == aes_pkg::SP2V_HIGH) break;
        @(cfg.chip_vif.cpu_clk_rst_if.cbn);
      end
    )

    // Verify that the masking is off for the next couple of encryptions.
    `uvm_info(`gfn, "Verifying that AES masking is switched off.", UVM_LOW)
    while (block_ctr < num_blocks) begin
      // Probe handshake and control signals.
      in_valid = hdl_read_sp2v($sformatf("%s.in_valid_i", aes_cipher_core_path));
      in_ready = hdl_read_sp2v($sformatf("%s.in_ready_o", aes_cipher_core_path));
      crypt = hdl_read_sp2v($sformatf("%s.crypt_o", aes_cipher_core_path));
      sub_bytes_en = hdl_read_sp2v($sformatf("%s.sub_bytes_en", aes_cipher_core_path));
      sub_bytes_out_req = hdl_read_sp2v($sformatf("%s.sub_bytes_out_req", aes_cipher_core_path));
      state_we = hdl_read_sp2v($sformatf("%s.state_we", aes_cipher_core_path));
      out_valid = hdl_read_sp2v($sformatf("%s.out_valid_o", aes_cipher_core_path));
      out_ready = hdl_read_sp2v($sformatf("%s.out_ready_i", aes_cipher_core_path));

      // Check Share 1 of the initial key and input.
      if (in_valid == aes_pkg::SP2V_HIGH) begin
        key_init_share1 = hdl_read_aes_key_share($sformatf("%s.key_init_i[1]",
          aes_cipher_core_path));
        `DV_CHECK_EQ_FATAL(key_init_share1, '0, "Share 1 of the initial key not equal zero.")
        state_init_share1 = hdl_read_aes_state_share($sformatf("%s.state_init_i[1]",
          aes_cipher_core_path));
        `DV_CHECK_EQ_FATAL(state_init_share1, '0, "Share 1 of the input not equal zero.")
      end

      // Check mask input and output of SubBytes.
      if (sub_bytes_en == aes_pkg::SP2V_HIGH) begin
        sb_in_mask = hdl_read_aes_state_share($sformatf("%s.sb_in_mask", aes_cipher_core_path));
        `DV_CHECK_EQ_FATAL(sb_in_mask, '0, "SubBytes mask input not equal zero.")
      end
      if (sub_bytes_out_req == aes_pkg::SP2V_HIGH) begin
        sb_out_mask = hdl_read_aes_state_share($sformatf("%s.sb_out_mask", aes_cipher_core_path));
        `DV_CHECK_EQ_FATAL(sb_out_mask, '0, "SubBytes mask output not equal zero.")
      end

      // Check Share 1 of the value written to the state register when doing an encryption unless
      // we're in the last round.
      if (crypt == aes_pkg::SP2V_HIGH &&
          state_we == aes_pkg::SP2V_HIGH &&
          out_valid != aes_pkg::SP2V_HIGH) begin
        state_d_share1 = hdl_read_aes_state_share($sformatf("%s.state_d[1]",
            aes_cipher_core_path));
        `DV_CHECK_EQ_FATAL(state_d_share1, '0, "Share 1 of the state register not equal zero.")
      end

      // Check Share 1 of the output.
      if (out_valid == aes_pkg::SP2V_HIGH) begin
        state_o_share1 = hdl_read_aes_state_share($sformatf("%s.state_o[1]",
            aes_cipher_core_path));
        `DV_CHECK_EQ_FATAL(state_o_share1, '0, "Share 1 of the output not equal zero.")
      end

      // Advance the block counter.
      if (out_valid == aes_pkg::SP2V_HIGH && out_ready == aes_pkg::SP2V_HIGH) begin
        block_ctr++;
      end
      @(cfg.chip_vif.cpu_clk_rst_if.cbn);
    end
  endtask

  virtual task body();
    super.body();

    // Set path to the AES cipher core.
    aes_cipher_core_path = "tb.dut.top_earlgrey.u_aes.u_aes_core.u_aes_cipher_core";

    // Initialize block counter. We will do 4 blocks.
    block_ctr = 0;
    num_blocks = 4;

    fork
      check_masking_prng();
      check_cipher_core();
    join

    // Wait for the SW test to finish with pass/fail status.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status inside {SwTestStatusPassed, SwTestStatusFailed})
  endtask
endclass
