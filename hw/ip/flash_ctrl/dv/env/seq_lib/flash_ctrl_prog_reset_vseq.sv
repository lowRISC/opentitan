// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

class flash_ctrl_prog_reset_vseq extends flash_ctrl_otf_base_vseq;
  `uvm_object_utils(flash_ctrl_prog_reset_vseq)
  `uvm_object_new
  typedef enum logic [10:0] {
    StIdle          = 11'b11111111110,
    StPrePack       = 11'b00001110111, // 53.648 us
    StPackData      = 11'b10100100011, // 5.586 us
    StPostPack      = 11'b11010000101, // 53.922
    StCalcPlainEcc  = 11'b01101011011, // 5.677
    StReqFlash      = 11'b01010110010, // 5.814
    StWaitFlash     = 11'b00100111000, // 13.246
    StCalcMask      = 11'b00000001110, // 5.7
    StScrambleData  = 11'b00011101001, // 5.745
    StCalcEcc       = 11'b00111010100, // 5.791
    StDisabled      = 11'b10001000000,
    StInvalid       = 11'b10010011011
  } reset_state_e;

  typedef enum {
    DVStIdle          = 0,
    DVStPrePack       = 1,    //
    DVStPackData      = 2,    //
    DVStPostPack      = 3,    //
    DVStCalcPlainEcc  = 4,    //
    DVStReqFlash      = 5,
    DVStWaitFlash     = 6,
    DVStCalcMask      = 7,    //
    DVStScrambleData  = 8,    //
    DVStCalcEcc       = 9,    //
    DVStDisabled      = 10,
    DVStInvalid       = 11
                } reset_index_e;

  virtual task body();
    flash_op_t ctrl;
    int num, bank, iter;
    int state_long_timeout_ns = 50_000_000; // 50ms
    int state_timeout_ns = 100000; // 100us

    // Don't select a partition defined as read-only
    cfg.seq_cfg.avoid_ro_partitions = 1'b1;

    cfg.m_tl_agent_cfg.check_tl_errs = 0;
    cfg.m_tl_agent_cfgs["flash_ctrl_eflash_reg_block"].check_tl_errs = 0;

    flash_program_data_c.constraint_mode(0);
    iter = 0;
    fork begin
      fork
        begin
          while (iter < 100) begin
            `DV_CHECK_MEMBER_RANDOMIZE_FATAL(rand_op)
            ctrl = rand_op;
            if (ctrl.partition == FlashPartData) begin
              num = $urandom_range(1, 32);
            end else begin
              num = $urandom_range(1, InfoTypeSize[rand_op.partition >> 1]);
              // Max transfer size of info is 512Byte.
              if (num * fractions > 128) begin
                num = 128 / fractions;
              end
            end
            bank = rand_op.addr[OTFBankId];
            prog_flash(ctrl, bank, num, fractions);
            iter++;
          end // while (iter < 100)
        end
        begin
          string path1, path2;
          reset_index_e reset_index = $urandom_range(DVStPrePack, DVStCalcEcc);
          `uvm_info("Test", $sformatf("reset_idx: %s", reset_index.name), UVM_MEDIUM)
          `DV_SPINWAIT(wait(cfg.flash_ctrl_vif.prog_state0 == dv2rtl_st(reset_index) ||
                            cfg.flash_ctrl_vif.prog_state1 == dv2rtl_st(reset_index));,
                       $sformatf("Timed out waiting for %s", reset_index.name),
                       // Use long time out.
                       // Some unique state does not always guarantee to reach.
                       // In that case, let test finish gracefully.
                       state_long_timeout_ns)
        end
      join_any
      disable fork;
    end join
    `uvm_info(`gfn, "RESET", UVM_LOW)
    cfg.seq_cfg.disable_flash_init = 1;
    cfg.seq_cfg.en_init_keys_seeds = 0;
    // Clean up scoreboard before the next round.
    cfg.otf_scb_h.clear_fifos();
    cfg.otf_scb_h.stop = 1;
    apply_reset();
    csr_wr(.ptr(ral.init), .value(1));
    `uvm_info("Test","OTP",UVM_LOW)
    otp_model();
    `DV_SPINWAIT(wait(cfg.flash_ctrl_vif.rd_buf_en == 1);,
                 "Timed out waiting for rd_buf_en",
                 state_timeout_ns)

  endtask

  function reset_state_e dv2rtl_st(reset_index_e idx);
    case(idx)
      DVStIdle        : return StIdle;
      DVStPrePack     : return StPrePack;
      DVStPackData    : return StPackData;
      DVStPostPack    : return StPostPack;
      DVStCalcPlainEcc: return StCalcPlainEcc;
      DVStReqFlash    : return StReqFlash;
      DVStWaitFlash   : return StWaitFlash;
      DVStCalcMask    : return StCalcMask;
      DVStScrambleData: return StScrambleData;
      DVStCalcEcc     : return StCalcEcc;
      DVStDisabled    : return StDisabled;
      DVStInvalid     : return StInvalid;
      default: begin
        `uvm_error("dv2rma_st", $sformatf("unknown index:%0d", idx))
      end
    endcase
  endfunction
endclass // flash_ctrl_prog_reset_vseq
