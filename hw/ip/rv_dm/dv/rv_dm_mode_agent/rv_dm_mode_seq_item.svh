// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

// Sequence item for mode updates
//
// The signals come from various places in the toplevel, and each group has an associated validity
// flag.

class rv_dm_mode_seq_item extends uvm_sequence_item;
  `uvm_object_utils(rv_dm_mode_seq_item)

  bit             m_has_next_dm_addr;
  rand bit [31:0] m_next_dm_addr;

  // Note: The 4-bit values in this section represent values of type lc_tx_t, but we use the raw bit
  //       vector to allow invalid encodings.
  bit             m_has_lc_ctrl_signals;
  rand bit [3:0]  m_lc_hw_debug_clr;
  rand bit [3:0]  m_lc_hw_debug_en;
  rand bit [3:0]  m_lc_dft_en;
  rand bit [3:0]  m_lc_check_byp_en;
  rand bit [3:0]  m_lc_escalate_en;
  rand bit [3:0]  m_lc_init_done;
  rand bit        m_strap_en_override;

  // Note: The 4-bit value represents a value of type lc_tx_t, but we use the raw bit vector to
  //       allow invalid encodings.
  bit             m_has_pinmux_signals;
  rand bit [3:0]  m_pinmux_hw_debug_en;

  bit             m_has_pwrmgr_signals;
  rand bit        m_strap_en;

  // Note: The 8-bit value represents a value of type mubi8_t, but we use the raw bit vector to
  //       allow invalid encodings.
  bit             m_has_otp_ctrl_signals;
  rand bit [7:0]  m_otp_dis_rv_dm_late_debug;

  // Note: The 4-bit value represents a value of type mubi4_t, but we use the raw bit vector to
  //       allow invalid encodings.
  bit             m_has_scanmode;
  rand bit [3:0]  m_scanmode;

  extern function new (string name="");
  extern virtual function void do_print(uvm_printer printer);

  // Print an lc_tx_t field to the supplied printer
  extern static function void print_lc_tx_t_field(uvm_printer printer,
                                                  string      name,
                                                  bit [3:0]   value);

  // Print an mubi4_t field to the supplied printer
  extern static function void print_mubi4_t_field(uvm_printer printer,
                                                  string      name,
                                                  bit [3:0]   value);

  // Print an mubi8_t field to the supplied printer
  extern static function void print_mubi8_t_field(uvm_printer printer,
                                                  string      name,
                                                  bit [7:0]   value);

  // A slightly silly constraint that ensures signals that don't claim to be provided are dead zero.
  // This shouldn't have any effect on the behaviour through the driver, but makes waves and logs a
  // bit easier to read.
  extern constraint zero_when_not_provided_c;
endclass

function rv_dm_mode_seq_item::new (string name="");
  super.new(name);
endfunction

function void rv_dm_mode_seq_item::do_print(uvm_printer printer);
  super.do_print(printer);

  if (m_has_next_dm_addr) begin
    printer.print_field_int("m_next_dm_addr", m_next_dm_addr, 32);
  end else begin
    printer.print_field_int("m_has_next_dm_addr", m_has_next_dm_addr, 1, UVM_BIN);
  end

  if (m_has_lc_ctrl_signals) begin
    print_lc_tx_t_field(printer, "m_lc_hw_debug_clr", m_lc_hw_debug_clr);
    print_lc_tx_t_field(printer, "m_lc_hw_debug_en", m_lc_hw_debug_en);
    print_lc_tx_t_field(printer, "m_lc_dft_en", m_lc_dft_en);
    print_lc_tx_t_field(printer, "m_lc_check_byp_en", m_lc_check_byp_en);
    print_lc_tx_t_field(printer, "m_lc_escalate_en", m_lc_escalate_en);
    print_lc_tx_t_field(printer, "m_lc_init_done", m_lc_init_done);
    printer.print_field_int("m_strap_en_override", m_strap_en_override, 1, UVM_BIN);
  end else begin
    printer.print_field_int("m_has_lc_ctrl_signals", m_has_lc_ctrl_signals, 1, UVM_BIN);
  end

  if (m_has_pinmux_signals) begin
    print_lc_tx_t_field(printer, "m_pinmux_hw_debug_en", m_pinmux_hw_debug_en);
  end else begin
    printer.print_field_int("m_has_pinmux_signals", m_has_pinmux_signals, 1, UVM_BIN);
  end

  if (m_has_pwrmgr_signals) begin
    printer.print_field_int("m_strap_en", m_strap_en, 1, UVM_BIN);
  end else begin
    printer.print_field_int("m_has_pwrmgr_signals", m_has_pwrmgr_signals, 1, UVM_BIN);
  end

  if (m_has_otp_ctrl_signals) begin
    print_mubi8_t_field(printer, "m_otp_dis_rv_dm_late_debug", m_otp_dis_rv_dm_late_debug);
  end else begin
    printer.print_field_int("m_has_otp_ctrl_signals", m_has_otp_ctrl_signals, 1, UVM_BIN);
  end

  if (m_has_scanmode) begin
    print_mubi4_t_field(printer, "m_scanmode", m_scanmode);
  end else begin
    printer.print_field_int("m_has_scanmode", m_has_scanmode, 1, UVM_BIN);
  end
endfunction

function void rv_dm_mode_seq_item::print_lc_tx_t_field(uvm_printer printer,
                                                       string      name,
                                                       bit [3:0]   value);
  lc_tx_t as_enum = lc_tx_t'(value);
  string  str = as_enum.name();

  if (str == "") begin
    str = "(?)";
  end

  printer.print_generic(name, "lc_tx_t", 4, $sformatf("%-3s = 4'b%04b", str, value));
endfunction

function void rv_dm_mode_seq_item::print_mubi4_t_field(uvm_printer printer,
                                                       string      name,
                                                       bit [3:0]   value);
  mubi4_t as_enum = mubi4_t'(value);
  string  str = as_enum.name();

  if (str == "") begin
    str = "(?)";
  end

  printer.print_generic(name, "mubi4_t", 4, $sformatf("%-10s = 4'b%04b", str, value));
endfunction

function void rv_dm_mode_seq_item::print_mubi8_t_field(uvm_printer printer,
                                                       string      name,
                                                       bit [7:0]   value);
  mubi8_t as_enum = mubi8_t'(value);
  string  str = as_enum.name();

  if (str == "") begin
    str = "(?)";
  end

  printer.print_generic(name, "mubi8_t", 8, $sformatf("%-10s = 8'h%02x", str, value));
endfunction

constraint rv_dm_mode_seq_item::zero_when_not_provided_c {
  !m_has_next_dm_addr -> ~|m_next_dm_addr;
  !m_has_lc_ctrl_signals -> ~|{m_lc_hw_debug_clr, m_lc_hw_debug_en, m_lc_dft_en,
                               m_lc_check_byp_en, m_lc_escalate_en, m_lc_init_done,
                               m_strap_en_override};
  !m_has_pinmux_signals -> ~|m_pinmux_hw_debug_en;
  !m_has_pwrmgr_signals -> ~|m_strap_en;
  !m_has_otp_ctrl_signals -> ~|m_otp_dis_rv_dm_late_debug;
  !m_has_scanmode -> ~|m_scanmode;
}
