// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// RRAM CP flow, driven only over JTAG like on a tester.
//
// See the "CP (wafer test)" and "After packaging" flows of the RRAM forming plan.
// The open-source rram_macro has no forming, so the test starts on a formed part.
// The marker page is all zero (+rram_dis_vol_raw_unlock=0), and the OTP image is in RAW.
//
// 1.  RAW under the zero view, check through the LC TAP.
// 2.  Volatile RAW unlock, check TEST_UNLOCKED0, then the straps select the RV TAP.
// 3.  Through RV_DM, enable the RRAM TAP (vendor-specific), set RRAM_JTAG_SEL, and switch the
//     straps to the value 0, which then selects the RRAM TAP.
// 4.  vendor_forming_flow() on the RRAM TAP.
//     The open-source version only reads the TAP IDCODE, a vendor version may do more.
// 5.  Reset: RAW under the zero view.
// 6.  Volatile RAW unlock again, the same way.
// 7.  Through RV_DM, write DIS_VOL_RAW_UNLOCK through rram_ctrl and read it back.
// 8.  Reset: RAW with the real array, the volatile unlock is rejected.
// 9.  Persistent RAW -> TEST_UNLOCKED0, reset.
// 10. Through RV_DM, write the hashed test unlock and test exit tokens into SECRET0 through the
//     otp_ctrl DAI, and lock it with its digest.
// 11. Through RV_DM, write CP_DONE and read it back.
// 12. Optional, see scrap_lc_state0: LC TAP transition TEST_UNLOCKED0 -> SCRAP.
//     lc_ctrl writes SCRAP into the first life cycle copy, which is still selected.
//     CP_DONE only takes effect after the next reset, so steps 13 to 15 are not affected.
// 13. Reset: TEST_LOCKED6 with count 16, from the second life cycle copy.
// 14. TEST_LOCKED6 -> TEST_UNLOCKED7 with the test unlock token.
//     Reset, then TEST_UNLOCKED7 with count 17.
// 15. TEST_UNLOCKED7 -> DEV, PROD or PROD_END with the test exit token.
//     Reset, then the same state with count 18.

// One plain IR or DR shift through the RRAM TAP.
// With reset_tap set, it first resets the TAP FSM through Test-Logic-Reset.
// The RRAM TAP may see arbitrary TMS edges while RRAM_JTAG_SEL switches, and the TSMC TAP
// ignores trst_n.
// Pauses, dummy shifts and skipped IRs are left out, so that each shift is a plain one.
class chip_rram_tap_seq extends jtag_base_seq;
  `uvm_object_utils(chip_rram_tap_seq)
  `uvm_object_new

  bit reset_tap;

  virtual function void randomize_req(jtag_item req);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(req,
        ir_len             == local::ir_len;
        ir                 == local::ir;
        dr_len             == local::dr_len;
        dr                 == local::dr;
        reset_tap_fsm      == local::reset_tap;
        skip_reselected_ir == 0;
        dummy_ir           == 0;
        dummy_dr           == 0;
        ir_pause_count     == 0;
        dr_pause_count     == 0;
        exit_via_pause_ir  == 0;
        exit_via_pause_dr  == 0;)
  endfunction
endclass

class chip_rram_cp_flow_vseq extends chip_sw_base_vseq;
  `uvm_object_utils(chip_rram_cp_flow_vseq)

  `uvm_object_new

  // LC sends two 64-bit msg as input token.
  localparam uint TokenWidthBit  = kmac_pkg::MsgWidth * 2;
  localparam uint TokenWidthByte = TokenWidthBit / 8;

  localparam int unsigned RramBase = top_earlgrey_pkg::TOP_EARLGREY_RRAM_CTRL_CORE_BASE_ADDR;
  localparam int unsigned RramWordBytes = rram_ctrl_pkg::DataWidth / 8;
  localparam int unsigned OtpBase = top_earlgrey_pkg::TOP_EARLGREY_OTP_CTRL_CORE_BASE_ADDR;
  localparam int unsigned PinmuxBase = top_earlgrey_pkg::TOP_EARLGREY_PINMUX_BASE_ADDR;

  // rram_tap_enable() and vendor_forming_flow(), from the open-source or a vendor implementation.
  `include "rram_macro_forming.svh"

  rand bit [7:0] lc_unlock_token[TokenWidthByte];
  rand bit [7:0] lc_exit_token[TokenWidthByte];

  // Step 12 is optional in the CP flow.
  rand bit scrap_lc_state0;
  // The mission state of step 15.
  rand dec_lc_state_e final_lc_state;

  constraint scrap_lc_state0_c {
    scrap_lc_state0 dist {1'b1 :/ 50, 1'b0 :/ 50};
  }

  constraint final_lc_state_c {
    final_lc_state dist {DecLcStDev :/ 30, DecLcStProd :/ 35, DecLcStProdEnd :/ 35};
  }

  virtual task pre_start();
    cfg.chip_vif.tap_straps_if.drive(JtagTapLc);
    // The DMI can ignore a request that follows a write too quickly.
    // This test writes lc_ctrl and RV_DM SBA in quick succession, so it waits for each write.
    cfg.m_jtag_riscv_agent_cfg.wait_for_dmi_write = 1;
    super.pre_start();
  endtask

  // reset jtag interface
  virtual task reset_jtag_tap();
    cfg.m_jtag_riscv_agent_cfg.in_reset = 1;
    #2000ns;
    cfg.m_jtag_riscv_agent_cfg.in_reset = 0;
  endtask

  // Resets the chip with the LC TAP selected, and waits until lc_ctrl is ready.
  virtual task reset_to_lc_tap();
    cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 0;
    cfg.chip_vif.tap_straps_if.drive(JtagTapLc);
    apply_reset();
    reset_jtag_tap();
    wait_rom_check_done();
    wait_lc_ready(1);
  endtask

  virtual task check_lc_state(dec_lc_state_e exp_state, int unsigned exp_cnt);
    bit [TL_DW-1:0] lc_state, lc_cnt;
    jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl_regs.lc_state.get_offset(),
                                        p_sequencer.jtag_sequencer_h, lc_state);
    `DV_CHECK_EQ(lc_state, {DecLcStateNumRep{exp_state}})
    jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl_regs.lc_transition_cnt.get_offset(),
                                        p_sequencer.jtag_sequencer_h, lc_cnt);
    `DV_CHECK_EQ(lc_cnt, exp_cnt)
  endtask

  // Checks the DEVICE_ID that lc_ctrl reads from OTP.
  // Under the zero view it is zero, otherwise it matches the OTP content in the RRAM array.
  virtual task check_device_id(bit zero_view);
    bit [TL_DW-1:0] device_id, exp;
    foreach (ral.lc_ctrl_regs.device_id[i]) begin
      jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl_regs.device_id[i].get_offset(),
                                          p_sequencer.jtag_sequencer_h, device_id);
      exp = zero_view ? 0 :
            cfg.mem_bkdr_util_h[Otp].read32(otp_ctrl_reg_pkg::DeviceIdOffset + i * 4);
      `DV_CHECK_EQ(device_id, exp, $sformatf("DEVICE_ID[%0d]", i))
    end
  endtask

  // Runs a volatile RAW unlock through the LC TAP and checks TEST_UNLOCKED0 with count 1.
  // The straps then select the RV TAP, since they are sampled continuously in TEST_UNLOCKED0.
  virtual task volatile_raw_unlock_to_rv_tap();
    jtag_lc_state_volatile_raw_unlock(.target_strap(JtagTapLc), .expect_success(1));
    check_lc_state(DecLcStTestUnlocked0, 1);
    cfg.chip_vif.tap_straps_if.drive(JtagTapRvDm);
    reset_jtag_tap();
  endtask

  // Requests a volatile RAW unlock through the LC TAP and expects it to be rejected.
  // This leaves lc_ctrl in POST_TRANSITION, so a reset has to follow.
  virtual task expect_volatile_unlock_rejected();
    bit [TL_DW-1:0] status;
    bit [TL_DW-1:0] token_csr_vals[4] = {<< 32 {{>> 8 {RndCnstRawUnlockToken}}}};
    jtag_riscv_agent_pkg::jtag_write_csr(ral.lc_ctrl_regs.claim_transition_if.get_offset(),
                                         p_sequencer.jtag_sequencer_h, prim_mubi_pkg::MuBi8True);
    jtag_riscv_agent_pkg::jtag_write_csr(ral.lc_ctrl_regs.transition_ctrl.get_offset(),
                                         p_sequencer.jtag_sequencer_h, 2);
    foreach (token_csr_vals[i]) begin
      jtag_riscv_agent_pkg::jtag_write_csr(ral.lc_ctrl_regs.transition_token[i].get_offset(),
                                           p_sequencer.jtag_sequencer_h, token_csr_vals[i]);
    end
    jtag_riscv_agent_pkg::jtag_write_csr(ral.lc_ctrl_regs.transition_target.get_offset(),
                                         p_sequencer.jtag_sequencer_h,
                                         {DecLcStateNumRep{DecLcStTestUnlocked0}});
    jtag_riscv_agent_pkg::jtag_write_csr(ral.lc_ctrl_regs.transition_cmd.get_offset(),
                                         p_sequencer.jtag_sequencer_h, 1);
    `DV_SPINWAIT(
      do begin
        jtag_riscv_agent_pkg::jtag_read_csr(ral.lc_ctrl_regs.status.get_offset(),
                                            p_sequencer.jtag_sequencer_h, status);
      end while (!dv_base_reg_pkg::get_field_val(ral.lc_ctrl_regs.status.transition_error,
                                                 status));,
      "waiting for the volatile unlock to be rejected", 10_000_000)
    `DV_CHECK_EQ(dv_base_reg_pkg::get_field_val(ral.lc_ctrl_regs.status.transition_successful,
                                                status), 0)
  endtask

  //////////////
  // RRAM TAP //
  //////////////

  // Resets the TAP FSM, then shifts one IR and one DR through the TAP the straps select.
  // IR and DR are separate items, like the ones of jtag_riscv_driver.
  virtual task rram_tap_shift(uint ir_len, bit [jtag_agent_pkg::JTAG_IRW-1:0] ir,
                              uint dr_len, bit [jtag_agent_pkg::JTAG_DRW-1:0] dr,
                              output bit [jtag_agent_pkg::JTAG_DRW-1:0] dout);
    chip_rram_tap_seq ir_seq = chip_rram_tap_seq::type_id::create("rram_tap_ir_seq");
    chip_rram_tap_seq dr_seq = chip_rram_tap_seq::type_id::create("rram_tap_dr_seq");
    ir_seq.reset_tap = 1'b1;
    `DV_CHECK_RANDOMIZE_WITH_FATAL(ir_seq,
                                   ir_len == local::ir_len;
                                   ir     == local::ir;
                                   dr_len == 0;)
    ir_seq.start(cfg.m_jtag_riscv_agent_cfg.jtag_sequencer_h);
    `DV_CHECK_RANDOMIZE_WITH_FATAL(dr_seq,
                                   ir_len == 0;
                                   dr_len == local::dr_len;
                                   dr     == local::dr;)
    dr_seq.start(cfg.m_jtag_riscv_agent_cfg.jtag_sequencer_h);
    `DV_CHECK_FATAL(dr_seq.rsp != null, "No response for the RRAM TAP DR shift")
    dout = dr_seq.rsp.dout;
    `uvm_info(`gfn, $sformatf("RRAM TAP: IR 0x%0x (%0d bits), DR in 0x%0x, DR out 0x%0x (%0d bits)",
                              ir, ir_len, dr, dout, dr_len), UVM_LOW)
  endtask

  // Sets RRAM_JTAG_SEL through RV_DM SBA, then switches the straps to the value 0.
  // RRAM_JTAG_SEL enables the RRAM TAP on that value, and the other TAPs stay available.
  // The straps are sampled continuously, because lc_dft_en is On after the volatile unlock.
  virtual task select_rram_tap();
    jtag_riscv_agent_pkg::jtag_write_csr(PinmuxBase + pinmux_reg_pkg::PINMUX_RRAM_JTAG_SEL_OFFSET,
                                         p_sequencer.jtag_sequencer_h, prim_mubi_pkg::MuBi4True);
    cfg.chip_vif.tap_straps_if.drive(JtagTapNone);
    cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 0;
    // The riscv JTAG monitor decodes every DR shift on the pads as a DMI access.
    // That doesn't apply to the RRAM TAP, so its errors are ignored until the next chip reset.
    cfg.m_jtag_riscv_agent_cfg.allow_errors = 1'b1;
    // This gives the strap sampling time to switch the TAP.
    reset_jtag_tap();
  endtask

  ////////////////////////////////////////////
  // otp_ctrl DAI operations through RV_DM SBA //
  ////////////////////////////////////////////

  // Runs one DAI command and waits until the DAI is idle again.
  virtual task jtag_otp_dai_cmd(int unsigned addr, bit [TL_DW-1:0] cmd);
    bit [TL_DW-1:0] status, err_mask;
    jtag_riscv_agent_pkg::jtag_write_csr(OtpBase +
                                         ral.otp_ctrl_core.direct_access_address.get_offset(),
                                         p_sequencer.jtag_sequencer_h, addr);
    jtag_riscv_agent_pkg::jtag_write_csr(OtpBase +
                                         ral.otp_ctrl_core.direct_access_cmd.get_offset(),
                                         p_sequencer.jtag_sequencer_h, cmd);
    err_mask = ~((1 << ral.otp_ctrl_core.status.dai_idle.get_lsb_pos()) |
                 (1 << ral.otp_ctrl_core.status.check_pending.get_lsb_pos()));
    `DV_SPINWAIT(
      do begin
        jtag_riscv_agent_pkg::jtag_read_csr(OtpBase + ral.otp_ctrl_core.status.get_offset(),
                                            p_sequencer.jtag_sequencer_h, status);
        `DV_CHECK_EQ(status & err_mask, 0, $sformatf("DAI command 0x%0x at 0x%0x failed", cmd,
                                                     addr))
      end while (!dv_base_reg_pkg::get_field_val(ral.otp_ctrl_core.status.dai_idle, status));,
      "waiting for the DAI to become idle", 10_000_000)
  endtask

  // Writes one 64-bit chunk of a secret partition through the DAI.
  // otp_ctrl scrambles it, and rram_ctrl_otp stores it.
  virtual task jtag_otp_program64(int unsigned addr, bit [63:0] data);
    jtag_riscv_agent_pkg::jtag_write_csr(OtpBase +
                                         ral.otp_ctrl_core.direct_access_wdata[0].get_offset(),
                                         p_sequencer.jtag_sequencer_h, data[31:0]);
    jtag_riscv_agent_pkg::jtag_write_csr(OtpBase +
                                         ral.otp_ctrl_core.direct_access_wdata[1].get_offset(),
                                         p_sequencer.jtag_sequencer_h, data[63:32]);
    jtag_otp_dai_cmd(addr, 1 << ral.otp_ctrl_core.direct_access_cmd.wr.get_lsb_pos());
  endtask

  // Writes the hashed test unlock and test exit tokens into SECRET0 and locks the partition.
  // The tokens only become valid for lc_ctrl after the next reset.
  virtual task jtag_provision_secret0();
    bit [TokenWidthBit-1:0] unlock_hash = dec_otp_token_from_lc_csrs(lc_unlock_token);
    bit [TokenWidthBit-1:0] exit_hash   = dec_otp_token_from_lc_csrs(lc_exit_token);
    for (int unsigned i = 0; i < TokenWidthByte; i += 8) begin
      jtag_otp_program64(otp_ctrl_reg_pkg::TestUnlockTokenOffset + i, unlock_hash[i * 8 +: 64]);
      jtag_otp_program64(otp_ctrl_reg_pkg::TestExitTokenOffset + i, exit_hash[i * 8 +: 64]);
    end
    jtag_otp_dai_cmd(otp_ctrl_reg_pkg::Secret0Offset,
                     1 << ral.otp_ctrl_core.direct_access_cmd.digest.get_lsb_pos());
  endtask

  ///////////////////////////////////////////
  // rram_ctrl operations through RV_DM SBA //
  ///////////////////////////////////////////

  virtual task rram_wr32(int unsigned offset, bit [TL_DW-1:0] data);
    jtag_riscv_agent_pkg::jtag_write_csr(RramBase + offset, p_sequencer.jtag_sequencer_h, data);
  endtask

  virtual task rram_rd32(int unsigned offset, output bit [TL_DW-1:0] data);
    jtag_riscv_agent_pkg::jtag_read_csr(RramBase + offset, p_sequencer.jtag_sequencer_h, data);
  endtask

  virtual task rv_dm_activate();
    jtag_riscv_dm_activation_seq jtag_dm_activation_seq =
        jtag_riscv_dm_activation_seq::type_id::create("jtag_dm_activation_seq");
    jtag_dm_activation_seq.start(p_sequencer.jtag_sequencer_h);
    cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 1;
  endtask

  // Activates RV_DM, initializes rram_ctrl, and enables the marker page.
  // The ROM does not run in RAW, so nothing else initializes rram_ctrl.
  virtual task rram_ctrl_setup();
    bit [TL_DW-1:0] status;
    rv_dm_activate();

    rram_wr32(rram_ctrl_reg_pkg::RRAM_CTRL_INIT_OFFSET, 1);
    `DV_SPINWAIT(
      do begin
        rram_rd32(rram_ctrl_reg_pkg::RRAM_CTRL_STATUS_OFFSET, status);
      end while (!status[4]);,
      "waiting for the rram_ctrl init", 10_000_000)

    // EN, RD_EN and WR_EN of the marker page.
    // rram_ctrl ignores SCRAMBLE_EN and ECC_EN for this page.
    rram_wr32(rram_ctrl_reg_pkg::RRAM_CTRL_INFO_PAGE_CFG_4_OFFSET,
              {4'(prim_mubi_pkg::MuBi4True), 4'(prim_mubi_pkg::MuBi4True),
               4'(prim_mubi_pkg::MuBi4True)});
  endtask

  // Runs a rram_ctrl program or read operation of one 128-bit word on the marker page.
  virtual task rram_marker_op(bit write, int unsigned word,
                              inout bit [rram_ctrl_pkg::DataWidth-1:0] data);
    localparam int unsigned NumBusWords = rram_ctrl_pkg::DataWidth / TL_DW;
    bit [TL_DW-1:0] control, op_status, val;
    control = (NumBusWords - 1) << 16 | (write ? 1 : 0) << 4 | 1 << 8;
    rram_wr32(rram_ctrl_reg_pkg::RRAM_CTRL_CONTROL_OFFSET, control);
    rram_wr32(rram_ctrl_reg_pkg::RRAM_CTRL_ADDR_OFFSET,
              (rram_ctrl_pkg::MarkerInfoPage * rram_ctrl_pkg::WordsPerPage + word) *
              RramWordBytes);
    rram_wr32(rram_ctrl_reg_pkg::RRAM_CTRL_CONTROL_OFFSET, control | 1);
    if (write) begin
      for (int unsigned i = 0; i < NumBusWords; i++) begin
        rram_wr32(rram_ctrl_reg_pkg::RRAM_CTRL_WR_FIFO_OFFSET, data[i * TL_DW +: TL_DW]);
      end
    end
    `DV_SPINWAIT(
      do begin
        rram_rd32(rram_ctrl_reg_pkg::RRAM_CTRL_OP_STATUS_OFFSET, op_status);
      end while (!op_status[0]);,
      "waiting for the rram_ctrl operation", 10_000_000)
    `DV_CHECK_EQ(op_status[1], 0, $sformatf("rram_ctrl operation on marker word %0d failed", word))
    if (!write) begin
      for (int unsigned i = 0; i < NumBusWords; i++) begin
        rram_rd32(rram_ctrl_reg_pkg::RRAM_CTRL_RD_FIFO_OFFSET, val);
        `uvm_info(`gfn, $sformatf("RD_FIFO[%0d] = 0x%08x", i, val), UVM_HIGH)
        data[i * TL_DW +: TL_DW] = val;
      end
    end
    rram_wr32(rram_ctrl_reg_pkg::RRAM_CTRL_OP_STATUS_OFFSET, 0);
  endtask

  // Writes all copies of a marker through rram_ctrl and reads them back.
  virtual task write_marker(bit [rram_ctrl_pkg::WordW-1:0] words[rram_ctrl_pkg::NumMarkerCopies]);
    bit [rram_ctrl_pkg::DataWidth-1:0] data;
    foreach (words[k]) begin
      data = rram_ctrl_pkg::DataWidth'(rram_ctrl_pkg::MarkerMagic);
      rram_marker_op(1'b1, words[k], data);
      `uvm_info(`gfn, $sformatf("Marker word %0d in the array: 0x%032x", words[k],
                cfg.mem_bkdr_util_h[RramInfo].read((rram_ctrl_pkg::MarkerInfoPage *
                rram_ctrl_pkg::WordsPerPage + words[k]) * RramWordBytes)), UVM_HIGH)
      data = '0;
      rram_marker_op(1'b0, words[k], data);
      `DV_CHECK_EQ(data, rram_ctrl_pkg::DataWidth'(rram_ctrl_pkg::MarkerMagic))
    end
  endtask

  virtual task body();
    bit [rram_ctrl_pkg::WordW-1:0] dis_words[rram_ctrl_pkg::NumMarkerCopies] =
        rram_ctrl_pkg::DisVolRawUnlockWords;
    bit [rram_ctrl_pkg::WordW-1:0] cp_words[rram_ctrl_pkg::NumMarkerCopies] =
        rram_ctrl_pkg::CpDoneWords;
    super.body();

    wait_rom_check_done();
    wait_lc_ready(1);

    // Step 1: RAW under the zero view.
    `uvm_info(`gfn, "Step 1: RAW under the zero view", UVM_LOW)
    check_lc_state(DecLcStRaw, 0);
    check_device_id(1'b1);

    // Step 2: volatile RAW unlock, the straps then select the RV TAP.
    `uvm_info(`gfn, "Step 2: volatile RAW unlock", UVM_LOW)
    volatile_raw_unlock_to_rv_tap();

    // Step 3: through RV_DM, enable the RRAM TAP and set RRAM_JTAG_SEL.
    // The straps then select the RRAM TAP.
    `uvm_info(`gfn, "Step 3: select the RRAM TAP", UVM_LOW)
    rv_dm_activate();
    rram_tap_enable();
    select_rram_tap();

    // Step 4: the strap value 0 now reaches the RRAM TAP.
    `uvm_info(`gfn, "Step 4: forming flow on the RRAM TAP", UVM_LOW)
    vendor_forming_flow();

    // Step 5: reset, RAW under the zero view again.
    `uvm_info(`gfn, "Step 5: RAW after the forming", UVM_LOW)
    reset_to_lc_tap();
    cfg.m_jtag_riscv_agent_cfg.allow_errors = 1'b0;
    check_lc_state(DecLcStRaw, 0);

    // Step 6: volatile RAW unlock again.
    `uvm_info(`gfn, "Step 6: volatile RAW unlock", UVM_LOW)
    volatile_raw_unlock_to_rv_tap();

    // Step 7: write DIS_VOL_RAW_UNLOCK through rram_ctrl, while the zero view is still active.
    `uvm_info(`gfn, "Step 7: write DIS_VOL_RAW_UNLOCK", UVM_LOW)
    rram_ctrl_setup();
    write_marker(dis_words);

    // Step 8: RAW with the real array, the volatile unlock is rejected.
    `uvm_info(`gfn, "Step 8: RAW without the zero view", UVM_LOW)
    reset_to_lc_tap();
    check_lc_state(DecLcStRaw, 0);
    check_device_id(1'b0);
    expect_volatile_unlock_rejected();
    reset_to_lc_tap();

    // Step 9: persistent RAW -> TEST_UNLOCKED0.
    `uvm_info(`gfn, "Step 9: persistent RAW unlock", UVM_LOW)
    jtag_lc_state_transition(DecLcStRaw, DecLcStTestUnlocked0);
    cfg.chip_vif.tap_straps_if.drive(JtagTapRvDm);
    apply_reset();
    reset_jtag_tap();
    wait_rom_check_done();
    // RV_DM only becomes active once the CPU runs the ROM, like in chip_tap_straps_vseq.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status inside {SwTestStatusInBootRom,
                                                           SwTestStatusInBootRomHalt})

    // rram_ctrl_setup() also activates RV_DM, which the DAI accesses below need.
    rram_ctrl_setup();

    // Step 10: provision and lock SECRET0 through the otp_ctrl DAI.
    // rram_ctrl_otp stores it in its relocated INFO page.
    `uvm_info(`gfn, "Step 10: provision SECRET0", UVM_LOW)
    jtag_provision_secret0();

    // Step 11: write CP_DONE through rram_ctrl.
    `uvm_info(`gfn, "Step 11: write CP_DONE", UVM_LOW)
    write_marker(cp_words);

    // Step 12: optionally move the first life cycle copy to SCRAP.
    // A complete loss of CP_DONE then falls back to SCRAP instead of TEST_UNLOCKED0.
    // The straps are sampled continuously in TEST_UNLOCKED0, so no reset is needed for the LC TAP.
    if (scrap_lc_state0) begin
      `uvm_info(`gfn, "Step 12: TEST_UNLOCKED0 -> SCRAP in the first life cycle copy", UVM_LOW)
      cfg.chip_vif.tap_straps_if.drive(JtagTapLc);
      cfg.m_jtag_riscv_agent_cfg.is_rv_dm = 0;
      reset_jtag_tap();
      jtag_lc_state_transition(DecLcStTestUnlocked0, DecLcStScrap);
      `DV_CHECK_EQ(otp_read_lc_partition_state(cfg.mem_bkdr_util_h[Otp]), LcStScrap,
                   "SCRAP in the first life cycle copy")
    end else begin
      `uvm_info(`gfn, "Step 12: skipped, the first life cycle copy stays TEST_UNLOCKED0", UVM_LOW)
    end

    // Step 13: TEST_LOCKED6 with count 16, from the second life cycle copy.
    `uvm_info(`gfn, "Step 13: TEST_LOCKED6 after CP", UVM_LOW)
    reset_to_lc_tap();
    check_lc_state(DecLcStTestLocked6, 16);

    // Step 14: TEST_LOCKED6 -> TEST_UNLOCKED7 with the test unlock token.
    `uvm_info(`gfn, "Step 14: TEST_LOCKED6 -> TEST_UNLOCKED7", UVM_LOW)
    jtag_lc_state_transition(DecLcStTestLocked6, DecLcStTestUnlocked7, {<<8{lc_unlock_token}});
    reset_to_lc_tap();
    check_lc_state(DecLcStTestUnlocked7, 17);

    // Step 15: TEST_UNLOCKED7 -> DEV, PROD or PROD_END with the test exit token.
    `uvm_info(`gfn, $sformatf("Step 15: TEST_UNLOCKED7 -> %s", final_lc_state.name()), UVM_LOW)
    jtag_lc_state_transition(DecLcStTestUnlocked7, final_lc_state, {<<8{lc_exit_token}});
    reset_to_lc_tap();
    check_lc_state(final_lc_state, 18);

    // The CPU boots the test ROM in the final state.
    // Waiting for it to halt makes the forced pass in post_start() the last status change.
    // It also leaves no ROM fetches outstanding at the end of the simulation.
    `DV_WAIT(cfg.sw_test_status_vif.sw_test_status == SwTestStatusInBootRomHalt)
  endtask

  task post_start();
    // No SW runs in this test.
    override_test_status_and_finish(.passed(1));
    super.post_start();
  endtask : post_start
endclass
