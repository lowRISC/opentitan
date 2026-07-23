// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Very simple sequence that sends a single item with the given mode values (which can all be
// randomised)
//
// Most of the mode values in the item are multi-bit. The corresponding values in the sequence have
// documentation comments that explain how the single bit value in the sequence controls
// randomisation of the multi-bit value in the item.

class rv_dm_mode_seq extends dv_base_seq #(.REQ (rv_dm_mode_seq_item),
                                           .SEQUENCER_T (rv_dm_mode_sequencer));
  `uvm_object_utils(rv_dm_mode_seq)

  bit m_has_next_dm_addr;
  rand bit [31:0] m_next_dm_addr;

  // Signals from lc_ctrl //////////////////////////////////////////////////////////////////////////
  bit      m_has_lc_ctrl_signals;

  // If m_lc_hw_debug_clr_valid is true then the item's m_lc_hw_debug_clr signal will be an lc_tx_t
  // encoding of the boolean value in m_lc_hw_debug_clr. If not, the signal will be have arbitrary
  // invalid encoding.
  rand bit m_lc_hw_debug_clr_valid;
  rand bit m_lc_hw_debug_clr;

  // If m_lc_hw_debug_en is true, the item's m_lc_hw_debug_en signal will be On. If not, it will be
  // an arbitrary value other than On.
  rand bit m_lc_hw_debug_en;

  // If m_lc_dft_en is true, the item's m_lc_dft_en signal will be On. If not, it will be an
  // arbitrary value other than On.
  rand bit m_lc_dft_en;

  // If m_lc_check_byp_en is false, the item's m_lc_check_byp_en signal will be Off. If not, it will
  // be an arbitrary value other than Off.
  //
  // Note: This signal is only used in DMI mode
  rand bit m_lc_check_byp_en;

  // If m_lc_escalate_en is false, the item's m_lc_escalate_en signal will be Off. If not, it will
  // be an arbitrary value other than Off.
  rand bit m_lc_escalate_en;

  // If m_lc_init_done is true, the item's m_lc_init_done signal will be On. If not, it will be an
  // arbitrary value other than On.
  rand bit m_lc_init_done;

  rand bit m_strap_en_override;

  // Signals from pinmux ///////////////////////////////////////////////////////////////////////////
  bit      m_has_pinmux_signals;

  // If m_pinmux_hw_debug_en is true, the item's m_pinmux_hw_debug_en signal will be MuBi4True. If
  // not, it will be an arbitrary value other than MuBi4True.
  rand bit m_pinmux_hw_debug_en;

  // Signals from pwrmgr ///////////////////////////////////////////////////////////////////////////
  bit      m_has_pwrmgr_signals;
  rand bit m_strap_en;

  // Signals from otp_ctrl /////////////////////////////////////////////////////////////////////////
  bit      m_has_otp_ctrl_signals;

  // If m_otp_dis_rv_dm_late_debug is false, the item's m_otp_dis_rv_dm_late_debug signal will be
  // MuBi8False. If not, it will be an arbitrary value other than MuBi8False.
  rand bit m_otp_dis_rv_dm_late_debug;

  // Scanmode signal ///////////////////////////////////////////////////////////////////////////////
  bit      m_has_scanmode;

  // If m_scanmode is true, the item's m_scanmode signal will be MuBi4True. If not, it will be an
  // arbitrary value other than MuBi4True.
  rand bit m_scanmode;

  extern function new (string name="");
  extern virtual function void do_print(uvm_printer printer);
  extern virtual task body();

  // A bool to multi-bit bool converter. If bool_val matches strict_bool, return strict_encoding. If
  // not, return an arbitrary value with width bits that doesn't equal strict_encoding.
  extern function bit [31:0] gen_something_for_bool(int unsigned width,
                                                    bit          strict_bool,
                                                    bit [31:0]   strict_encoding,
                                                    bit          bool_val);

  // Generate an lc_tx_t / mubi4_t / mubi8_t from the given boolean value. Use a valid encoding if
  // bool_val = strict_val.
  extern function bit [3:0] gen_lc_tx_t_from_bool(bit strict_val, bit bool_val);
  extern function bit [3:0] gen_mubi4_t_from_bool(bit strict_val, bit bool_val);
  extern function bit [7:0] gen_mubi8_t_from_bool(bit strict_val, bit bool_val);

  // Generate a random lc_tx_t value that is neither On nor Off
  extern function bit [3:0] gen_bad_lc_tx_t();

  // Return bool_val as an lc_tx_t
  extern static function bit [3:0] bool_to_lc_tx_t(bit bool_val);
endclass

function rv_dm_mode_seq::new (string name="");
  super.new(name);
endfunction

function void rv_dm_mode_seq::do_print(uvm_printer printer);
  super.do_print(printer);

  if (m_has_next_dm_addr) begin
    printer.print_field_int("m_next_dm_addr", m_next_dm_addr, 32);
  end else begin
    printer.print_field_int("m_has_next_dm_addr", m_has_next_dm_addr, 1);
  end


  if (m_has_lc_ctrl_signals) begin
    printer.print_field_int("m_lc_hw_debug_clr_valid", m_lc_hw_debug_clr_valid, 1);
    if (m_lc_hw_debug_clr_valid) begin
      printer.print_field_int("m_lc_hw_debug_clr", m_lc_hw_debug_clr, 1);
    end
    printer.print_field_int("m_lc_hw_debug_en", m_lc_hw_debug_en, 1);
    printer.print_field_int("m_lc_dft_en", m_lc_dft_en, 1);
    printer.print_field_int("m_lc_check_byp_en", m_lc_check_byp_en, 1);
    printer.print_field_int("m_lc_escalate_en", m_lc_escalate_en, 1);
    printer.print_field_int("m_lc_init_done", m_lc_init_done, 1);
    printer.print_field_int("m_strap_en_override", m_strap_en_override, 1);
  end else begin
    printer.print_field_int("m_has_lc_ctrl_signals", m_has_lc_ctrl_signals, 1);
  end


  if (m_has_pinmux_signals) begin
    printer.print_field_int("m_pinmux_hw_debug_en", m_pinmux_hw_debug_en, 1);
  end else begin
    printer.print_field_int("m_has_pinmux_signals", m_has_pinmux_signals, 1);
  end


  if (m_has_pwrmgr_signals) begin
    printer.print_field_int("m_strap_en", m_strap_en, 1);
  end else begin
    printer.print_field_int("m_has_pwrmgr_signals", m_has_pwrmgr_signals, 1);
  end


  if (m_has_otp_ctrl_signals) begin
    printer.print_field_int("m_otp_dis_rv_dm_late_debug", m_otp_dis_rv_dm_late_debug, 1);
  end else begin
    printer.print_field_int("m_has_otp_ctrl_signals", m_has_otp_ctrl_signals, 1);
  end


  if (m_has_scanmode) begin
    printer.print_field_int("m_scanmode", m_scanmode, 1);
  end else begin
    printer.print_field_int("m_has_scanmode", m_has_scanmode, 1);
  end
endfunction

task rv_dm_mode_seq::body();
  rv_dm_mode_seq_item item;

  bit [3:0] enc_lc_hw_debug_clr, enc_lc_hw_debug_en, enc_lc_dft_en,
            enc_lc_check_byp_en, enc_lc_escalate_en, enc_lc_init_done;
  bit [3:0] enc_pinmux_hw_debug_en;
  bit [7:0] enc_otp_dis_rv_dm_late_debug;
  bit [3:0] enc_scanmode;

  item = rv_dm_mode_seq_item::type_id::create("item");
  item.m_has_next_dm_addr = m_has_next_dm_addr;
  item.m_has_lc_ctrl_signals = m_has_lc_ctrl_signals;
  item.m_has_pinmux_signals = m_has_pinmux_signals;
  item.m_has_pwrmgr_signals = m_has_pwrmgr_signals;
  item.m_has_otp_ctrl_signals = m_has_otp_ctrl_signals;
  item.m_has_scanmode = m_has_scanmode;

  start_item(item);

  // Randomise encodings for various fields of the item (if they are enabled) before randomising the
  // item itself. This avoids having to call complicated functions (which can call `uvm_error) from
  // inside the item randomisation.
  if (m_has_lc_ctrl_signals) begin
    enc_lc_hw_debug_clr = m_lc_hw_debug_clr_valid ?
                          bool_to_lc_tx_t(m_lc_hw_debug_clr) :
                          gen_bad_lc_tx_t();
    enc_lc_hw_debug_en = gen_lc_tx_t_from_bool(1, m_lc_hw_debug_en);
    enc_lc_dft_en = gen_lc_tx_t_from_bool(1, m_lc_dft_en);
    enc_lc_check_byp_en = gen_lc_tx_t_from_bool(0, m_lc_check_byp_en);
    enc_lc_escalate_en = gen_lc_tx_t_from_bool(0, m_lc_escalate_en);
    enc_lc_init_done = gen_lc_tx_t_from_bool(1, m_lc_init_done);
  end
  if (m_has_pinmux_signals) begin
    enc_pinmux_hw_debug_en = gen_lc_tx_t_from_bool(1, m_pinmux_hw_debug_en);
  end
  if (m_has_otp_ctrl_signals) begin
    enc_otp_dis_rv_dm_late_debug = gen_mubi8_t_from_bool(0, m_otp_dis_rv_dm_late_debug);
  end
  if (m_has_scanmode) begin
    enc_scanmode = gen_mubi4_t_from_bool(1, m_scanmode);
  end

  if (!item.randomize() with {
          if (m_has_next_dm_addr) {
            item.m_next_dm_addr == local::m_next_dm_addr;
          }
          if (m_has_lc_ctrl_signals) {
            item.m_lc_hw_debug_clr == local::enc_lc_hw_debug_clr;
            item.m_lc_hw_debug_en == local::enc_lc_hw_debug_en;
            item.m_lc_dft_en == local::enc_lc_dft_en;
            item.m_lc_check_byp_en == local::enc_lc_check_byp_en;
            item.m_lc_escalate_en == local::enc_lc_escalate_en;
            item.m_lc_init_done == local::enc_lc_init_done;
            item.m_strap_en_override == local::m_strap_en_override;
          }
          if (m_has_pinmux_signals) {
            item.m_pinmux_hw_debug_en == local::enc_pinmux_hw_debug_en;
          }
          if (m_has_pwrmgr_signals) {
            item.m_strap_en == local::m_strap_en;
          }
          if (m_has_otp_ctrl_signals) {
            item.m_otp_dis_rv_dm_late_debug == local::enc_otp_dis_rv_dm_late_debug;
          }
          if (m_has_scanmode) {
            item.m_scanmode == local::enc_scanmode;
          }
       }) begin
    `uvm_fatal(get_name(), "Failed to randomize item")
  end
  finish_item(item);
endtask

function bit [31:0] rv_dm_mode_seq::gen_something_for_bool(int unsigned width,
                                                           bit          strict_bool,
                                                           bit [31:0]   strict_encoding,
                                                           bit          bool_val);
  if (bool_val == strict_bool) begin
    return strict_encoding;
  end else begin
    bit [31:0] ret;
    if (!std::randomize(ret) with { (ret >> width) == 0; ret != strict_encoding; }) begin
      `uvm_error(get_full_name(),
                 $sformatf("Couldn't pick a random non-strict value (width = %0d)", width))
    end
    return ret;
  end
endfunction

function bit [3:0] rv_dm_mode_seq::gen_lc_tx_t_from_bool(bit strict_val, bit bool_val);
  return gen_something_for_bool(4, strict_val,
                                strict_val ? lc_ctrl_pkg::On : lc_ctrl_pkg::Off,
                                bool_val);
endfunction

function bit [3:0] rv_dm_mode_seq::gen_mubi4_t_from_bool(bit strict_val, bit bool_val);
  return gen_something_for_bool(4, strict_val,
                                strict_val ? prim_mubi_pkg::MuBi4True : prim_mubi_pkg::MuBi4False,
                                bool_val);
endfunction

function bit [7:0] rv_dm_mode_seq::gen_mubi8_t_from_bool(bit strict_val, bit bool_val);
  return gen_something_for_bool(8, strict_val,
                                strict_val ? prim_mubi_pkg::MuBi8True : prim_mubi_pkg::MuBi8False,
                                bool_val);
endfunction

function bit [3:0] rv_dm_mode_seq::gen_bad_lc_tx_t();
  bit [3:0] ret;
  if (!std::randomize(ret) with { ret != lc_ctrl_pkg::On; ret != lc_ctrl_pkg::Off; }) begin
    `uvm_error(get_full_name(), "Couldn't pick a random bad lc_tx_t")
  end
  return ret;
endfunction

function bit [3:0] rv_dm_mode_seq::bool_to_lc_tx_t(bit bool_val);
  return bool_val ? lc_ctrl_pkg::On : lc_ctrl_pkg::Off;
endfunction
