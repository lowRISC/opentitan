// Copyright lowRISC contributors (OpenTitan project).
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

<%!
  from ipgen.pinmux_gen import (INSEL_NUM_CONST, OUTSEL_NUM_CONST, check_params, gen_index_label,
                                mio_insel_legal, mio_outsel_legal, pad_attr_sv, sv_hex)
%>\
package pinmux_pkg;

  import pinmux_reg_pkg::*;
  import prim_pad_wrapper_pkg::*;

  parameter int NumIOs     = NMioPads + NDioPads;
  parameter int NDFTStraps = 2;
  parameter int NTapStraps = 2;

  // Since the target-specific top-levels often have slightly different debug signal positions, we
  // need a way to pass this info from the target specific top-level into the pinmux logic. The
  // datastructure below serves this purpose. Note that all the indices below are with respect to
  // the concatenated {DIO, MIO} packed array.
  typedef struct packed {
  % if enable_strap_sampling:
    integer                   tck_idx;
    integer                   tms_idx;
    integer                   trst_idx;
    integer                   tdi_idx;
    integer                   tdo_idx;
    integer                   tap_strap0_idx;
    integer                   tap_strap1_idx;
    integer                   dft_strap0_idx;
    integer                   dft_strap1_idx;
  % endif
  % if enable_usb_wakeup:
    integer                   usb_dp_idx;
    integer                   usb_dn_idx;
    integer                   usb_sense_idx;
  % endif
    pad_type_e [NDioPads-1:0] dio_pad_type;
    pad_type_e [NMioPads-1:0] mio_pad_type;
    scan_role_e [NDioPads-1:0] dio_scan_role;
    scan_role_e [NMioPads-1:0] mio_scan_role;
  } target_cfg_t;

  parameter target_cfg_t DefaultTargetCfg = '{
  % if enable_strap_sampling:
    tck_idx:           0,
    tms_idx:           0,
    trst_idx:          0,
    tdi_idx:           0,
    tdo_idx:           0,
    tap_strap0_idx:    0,
    tap_strap1_idx:    0,
    dft_strap0_idx:    0,
    dft_strap1_idx:    0,
  % endif
  % if enable_usb_wakeup:
    usb_dp_idx:        0,
    usb_dn_idx:        0,
    usb_sense_idx:     0,
  % endif
    dio_pad_type:      {NDioPads{BidirStd}},
    mio_pad_type:      {NMioPads{BidirStd}},
    dio_scan_role:     {NDioPads{NoScan}},
    mio_scan_role:     {NMioPads{NoScan}}
  };

<%
  check_params(n_mio_pads, n_dio_pads, n_mio_periph_in, n_mio_periph_out, mio_periph_ins,
               mio_periph_outs, mio_pad_attr_resvals, dio_pad_attr_resvals)
  # The pad attrs list has one entry per MIO pad, take the pad names from there.
  mio_pad_names = [name for name, _ in mio_pad_attr_resvals]
  insel_w = n_mio_pads + INSEL_NUM_CONST
  outsel_w = n_mio_periph_out + OUTSEL_NUM_CONST
%>\
  // Legal MIO_PERIPH_INSEL values for each MIO peripheral input. LSB corresponds to lowest index.
  // Includes static options.
  parameter logic [NMioPeriphIn-1:0][NMioPads+1:0] MioPeriphInselLegal = {
% for label, mask in gen_index_label(mio_insel_legal(n_mio_pads, mio_periph_ins))[::-1]:
    ${sv_hex(mask, insel_w)}${f"  // {label}" if loop.last else f", // {label}"}
% endfor
  };

  // Legal MIO_OUTSEL values for each MIO pad. LSB corresponds to lowest index. Includes static
  // options.
  parameter logic [NMioPads-1:0][NMioPeriphOut+2:0] MioOutselLegal = {
% for label, mask in gen_index_label(mio_outsel_legal(mio_pad_names, mio_periph_outs))[::-1]:
    ${sv_hex(mask, outsel_w)}${f"  // {label}" if loop.last else f", // {label}"}
% endfor
  };

  // Reset values of the MIO_PAD_ATTR CSRs defined by the top. LSB corresponds to lowest index.
  parameter pad_attr_t [NMioPads-1:0] MioPadAttrResval = {
% for label, attrs in gen_index_label(mio_pad_attr_resvals)[::-1]:
    ${pad_attr_sv(attrs)}${f"  // {label}" if loop.last else f", // {label}"}
% endfor
  };

  // Reset values of the DIO_PAD_ATTR CSRs defined by the top. LSB corresponds to lowest index.
  parameter pad_attr_t [NDioPads-1:0] DioPadAttrResval = {
% for label, attrs in gen_index_label(dio_pad_attr_resvals)[::-1]:
    ${pad_attr_sv(attrs)}${f"  // {label}" if loop.last else f", // {label}"}
% endfor
  };

  // Wakeup Detector Modes
  typedef enum logic [2:0] {
    Posedge   = 3'b000,
    Negedge   = 3'b001,
    Edge      = 3'b010,
    HighTimed = 3'b011,
    LowTimed  = 3'b100
  } wkup_mode_e;

  // Interface with LC controller
  typedef struct packed {
    logic                  valid;
    logic [NDFTStraps-1:0] straps;
  } dft_strap_test_req_t;

  typedef enum logic [NTapStraps-1:0] {
    FuncSel   = 2'b00,
    LcTapSel  = 2'b01,
    RvTapSel  = 2'b10,
    DftTapSel = 2'b11
  } tap_strap_t;

endpackage : pinmux_pkg
