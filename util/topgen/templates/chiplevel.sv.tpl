// Copyright lowRISC contributors.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0
${gencmd}
<%
import re
import topgen.lib as lib
from copy import deepcopy

# Provide shortcuts for some commonly used variables
pinmux = top['pinmux']
pinout = top['pinout']

num_mio_inputs = pinmux['io_counts']['muxed']['inouts'] + \
                 pinmux['io_counts']['muxed']['inputs']
num_mio_outputs = pinmux['io_counts']['muxed']['inouts'] + \
                  pinmux['io_counts']['muxed']['outputs']
num_mio_pads = pinmux['io_counts']['muxed']['pads']

num_dio_inputs = pinmux['io_counts']['dedicated']['inouts'] + \
                 pinmux['io_counts']['dedicated']['inputs']
num_dio_outputs = pinmux['io_counts']['dedicated']['inouts'] + \
                  pinmux['io_counts']['dedicated']['outputs']
num_dio_total = pinmux['io_counts']['dedicated']['inouts'] + \
                pinmux['io_counts']['dedicated']['inputs'] + \
                pinmux['io_counts']['dedicated']['outputs']

def get_dio_sig(pinmux: {}, pad: {}):
  '''Get DIO signal associated with this pad or return None'''
  for sig in pinmux["ios"]:
    if sig["connection"] == "direct" and pad["name"] == sig["pad"]:
      return sig
  else:
    return None

# Modify the pad lists on the fly, based on target config
maxwidth = 0
muxed_pads = []
dedicated_pads = []
k = 0
for pad in pinout["pads"]:
  if pad["connection"] == "muxed":
    if pad["name"] not in target["pinout"]["remove_pads"]:
      maxwidth = max(maxwidth, len(pad["name"]))
      muxed_pads.append(pad)
  else:
    k = pad["idx"]
    if pad["name"] not in target["pinout"]["remove_pads"]:
      maxwidth = max(maxwidth, len(pad["name"]))
      dedicated_pads.append(pad)

for pad in target["pinout"]["add_pads"]:
  # Since these additional pads have not been elaborated in the merge phase,
  # we need to add their global index here.
  amended_pad = deepcopy(pad)
  amended_pad.update({"idx" : k})
  dedicated_pads.append(pad)
  k += 1

num_im = sum([x["width"] if "width" in x else 1 for x in top["inter_signal"]["external"]])

max_sigwidth = max([x["width"] if "width" in x else 1 for x in top["pinmux"]["ios"]])
max_sigwidth = len("{}".format(max_sigwidth))

clks_attr = top['clocks']
cpu_clk = top['clocks']['hier_paths']['top'] + "clk_proc_main"
cpu_rst = top["reset_paths"]["sys"]
dm_rst = top["reset_paths"]["lc"]
esc_clk = top['clocks']['hier_paths']['top'] + "clk_io_div4_timers"
esc_rst = top["reset_paths"]["sys_io_div4"]

unused_resets = lib.get_unused_resets(top)
unused_im_defs, undriven_im_defs = lib.get_dangling_im_def(top["inter_signal"]["definitions"])

%>\
% if target["name"] != "asic":
module chip_${top["name"]}_${target["name"]} #(
  // Path to a VMEM file containing the contents of the boot ROM, which will be
  // baked into the FPGA bitstream.
  parameter BootRomInitFile = "boot_rom_fpga_${target["name"]}.32.vmem",
  // Path to a VMEM file containing the contents of the emulated OTP, which will be
  // baked into the FPGA bitstream.
  parameter OtpCtrlMemInitFile = "otp_img_fpga_${target["name"]}.vmem",
  // TODO: Remove this 0 once infra is ready
  parameter bit RomCtrlSkipCheck = 1
) (
% else:
module chip_${top["name"]}_${target["name"]} #(
  // TODO: Remove this 0 once infra is ready
  parameter bit RomCtrlSkipCheck = 1
) (
% endif
<%

%>\
  // Dedicated Pads
% for pad in dedicated_pads:
<%
  sig = get_dio_sig(pinmux, pad)
  if sig is not None:
    comment = "// Dedicated Pad for {}".format(sig["name"])
  else:
    comment = "// Manual Pad"
%>\
  inout ${pad["name"]}, ${comment}
% endfor

  // Muxed Pads
% for pad in muxed_pads:
  inout ${pad["name"]}${" " if loop.last else ","} // MIO Pad ${pad["idx"]}
% endfor
);

  import top_${top["name"]}_pkg::*;
  import prim_pad_wrapper_pkg::*;

% if target["pinmux"]["special_signals"]:
  ////////////////////////////
  // Special Signal Indices //
  ////////////////////////////

  % for entry in target["pinmux"]["special_signals"]:
<% param_name = (lib.Name.from_snake_case(entry["name"]) +
                 lib.Name(["pad", "idx"])).as_camel_case()
%>\
  parameter int ${param_name} = ${entry["idx"]};
  % endfor
% endif

  // DFT and Debug signal positions in the pinout.
  localparam pinmux_pkg::target_cfg_t PinmuxTargetCfg = '{
    tck_idx:           TckPadIdx,
    tms_idx:           TmsPadIdx,
    trst_idx:          TrstNPadIdx,
    tdi_idx:           TdiPadIdx,
    tdo_idx:           TdoPadIdx,
    tap_strap0_idx:    Tap0PadIdx,
    tap_strap1_idx:    Tap1PadIdx,
    dft_strap0_idx:    Dft0PadIdx,
    dft_strap1_idx:    Dft1PadIdx,
    // TODO: check whether there is a better way to pass these USB-specific params
    usb_dp_idx:        DioUsbdevDp,
    usb_dn_idx:        DioUsbdevDn,
    usb_dp_pullup_idx: DioUsbdevDpPullup,
    usb_dn_pullup_idx: DioUsbdevDnPullup,
    // Pad types for attribute WARL behavior
    dio_pad_type: {
<%
  pad_attr = []
  for sig in list(reversed(top["pinmux"]["ios"])):
    if sig["connection"] != "muxed":
      pad_attr.append((sig['name'], sig["attr"]))
%>\
% for name, attr in pad_attr:
      ${attr}${" " if loop.last else ","} // DIO ${name}
% endfor
    },
    mio_pad_type: {
<%
  pad_attr = []
  for pad in list(reversed(pinout["pads"])):
    if pad["connection"] == "muxed":
      pad_attr.append(pad["type"])
%>\
% for attr in pad_attr:
      ${attr}${" " if loop.last else ","} // MIO Pad ${len(pad_attr) - loop.index - 1}
% endfor
    }
  };

  ////////////////////////
  // Signal definitions //
  ////////////////////////

  pad_attr_t [pinmux_reg_pkg::NMioPads-1:0] mio_attr;
  pad_attr_t [pinmux_reg_pkg::NDioPads-1:0] dio_attr;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_out;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_oe;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_in;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_in_raw;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_out;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_oe;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_in;

  logic unused_mio_in_raw;
  assign unused_mio_in_raw = ^mio_in_raw;

  // Manual pads
% for pad in dedicated_pads:
<%
  pad_prefix = pad["name"].lower()
%>\
% if not get_dio_sig(pinmux, pad):
  logic manual_in_${pad_prefix}, manual_out_${pad_prefix}, manual_oe_${pad_prefix};
% endif
% endfor

% for pad in dedicated_pads:
<%
  pad_prefix = pad["name"].lower()
%>\
% if not get_dio_sig(pinmux, pad):
  pad_attr_t manual_attr_${pad_prefix};
% endif
% endfor

% if target["pinout"]["remove_pads"]:
  /////////////////////////
  // Stubbed pad tie-off //
  /////////////////////////

  // Only signals going to non-custom pads need to be tied off.
  logic [${len(pinout["pads"])-1}:0] unused_sig;
% for pad in pinout["pads"]:
  % if pad["connection"] == 'muxed':
    % if pad["name"] in target["pinout"]["remove_pads"]:
  assign mio_in[${pad["idx"]}] = 1'b0;
  assign unused_sig[${loop.index}] = mio_out[${pad["idx"]}] ^ mio_oe[${pad["idx"]}];
    % endif
  % else:
    % if pad["name"] in target["pinout"]["remove_pads"]:
<%
    ## Only need to tie off if this is not a custom pad.
    sig = get_dio_sig(pinmux, pad)
    if sig is not None:
      sig_index = lib.get_io_enum_literal(sig, 'dio')
%>\
      % if sig is not None:
  assign dio_in[${lib.get_io_enum_literal(sig, 'dio')}] = 1'b0;
  assign unused_sig[${loop.index}] = dio_out[${sig_index}] ^ dio_oe[${sig_index}];
      % endif
    % endif
  % endif
% endfor
%endif

  //////////////////////
  // Padring Instance //
  //////////////////////

% if target["name"] == "asic":
  // AST signals needed in padring
  ast_pkg::ast_clks_t ast_base_clks;
  logic scan_rst_n;
  lc_ctrl_pkg::lc_tx_t scanmode;
% endif

  padring #(
    // Padring specific counts may differ from pinmux config due
    // to custom, stubbed or added pads.
    .NDioPads(${len(dedicated_pads)}),
    .NMioPads(${len(muxed_pads)}),
% if target["name"] == "asic":
    .PhysicalPads(1),
    .NIoBanks(int'(IoBankCount)),
    .DioScanRole ({
% for pad in list(reversed(dedicated_pads)):
      scan_role_pkg::${lib.Name.from_snake_case('dio_pad_' + pad["name"] + '_scan_role').as_camel_case()}${"" if loop.last else ","}
% endfor
    }),
    .MioScanRole ({
% for pad in list(reversed(muxed_pads)):
      scan_role_pkg::${lib.Name.from_snake_case('mio_pad_' + pad["name"] + '_scan_role').as_camel_case()}${"" if loop.last else ","}
% endfor
    }),
    .DioPadBank ({
% for pad in list(reversed(dedicated_pads)):
      ${lib.Name.from_snake_case('io_bank_' + pad["bank"]).as_camel_case()}${" " if loop.last else ","} // ${pad['name']}
% endfor
    }),
    .MioPadBank ({
% for pad in list(reversed(muxed_pads)):
      ${lib.Name.from_snake_case('io_bank_' + pad["bank"]).as_camel_case()}${" " if loop.last else ","} // ${pad['name']}
% endfor
    }),
% endif
\
\
    .DioPadType ({
% for pad in list(reversed(dedicated_pads)):
      ${pad["type"]}${" " if loop.last else ","} // ${pad['name']}
% endfor
    }),
    .MioPadType ({
% for pad in list(reversed(muxed_pads)):
      ${pad["type"]}${" " if loop.last else ","} // ${pad['name']}
% endfor
    })
  ) u_padring (
  // This is only used for scan and DFT purposes
% if target["name"] == "asic":
    .clk_scan_i   ( ast_base_clks.clk_sys ),
    .scanmode_i   ( scanmode              ),
% else:
    .clk_scan_i   ( 1'b0                  ),
    .scanmode_i   ( lc_ctrl_pkg::Off      ),
  % endif
    .dio_in_raw_o ( ),
    .mio_in_raw_o ( mio_in_raw            ),
    // Chip IOs
    .dio_pad_io ({
% for pad in list(reversed(dedicated_pads)):
      ${pad["name"]}${"" if loop.last else ","}
% endfor
    }),

    .mio_pad_io ({
% for pad in list(reversed(muxed_pads)):
      ${pad["name"]}${"" if loop.last else ","}
% endfor
    }),

    // Core-facing
% for port in ["in_o", "out_i", "oe_i", "attr_i"]:
    .dio_${port} ({
  % for pad in list(reversed(dedicated_pads)):
  <%
    sig = get_dio_sig(pinmux, pad)
  %>\
    % if sig is None:
      manual_${port[:-2]}_${pad["name"].lower()}${"" if loop.last else ","}
    % else:
      dio_${port[:-2]}[${lib.get_io_enum_literal(sig, 'dio')}]${"" if loop.last else ","}
    % endif
  % endfor
      }),
% endfor

% for port in ["in_o", "out_i", "oe_i", "attr_i"]:
<%
    sig_name = 'mio_' + port[:-2]
    indices = list(reversed(list(pad['idx'] for pad in muxed_pads)))
%>\
    .mio_${port} (${lib.make_bit_concatenation(sig_name, indices, 6)})${"" if loop.last else ","}
% endfor
  );


###################################################################
## USB for CW305                                                 ##
###################################################################
% if target["name"] == "cw305":
  // Connect the DP pad
  assign dio_in[DioUsbdevDp] = manual_in_usb_p;
  assign manual_out_usb_p = dio_out[DioUsbdevDp];
  assign manual_oe_usb_p = dio_oe[DioUsbdevDp];
  assign manual_attr_usb_p = dio_attr[DioUsbdevDp];

  // Connect the DN pad
  assign dio_in[DioUsbdevDn] = manual_in_usb_n;
  assign manual_out_usb_n = dio_out[DioUsbdevDn];
  assign manual_oe_usb_n = dio_oe[DioUsbdevDn];
  assign manual_attr_usb_n = dio_attr[DioUsbdevDn];

  // Connect sense pad
  assign dio_in[DioUsbdevSense] = manual_in_io_usb_sense0;
  assign manual_out_io_usb_sense0 = dio_out[DioUsbdevSense];
  assign manual_oe_io_usb_sense0 = dio_oe[DioUsbdevSense];
  assign manual_attr_io_sense0 = dio_attr[DioUsbdevSense];

  // Connect DN pullup
  assign dio_in[DioUsbdevDnPullup] = manual_in_io_usb_dnpullup0;
  assign manual_out_io_usb_dnpullup0 = dio_out[DioUsbdevDnPullup];
  assign manual_oe_io_usb_dnpullup0 = dio_oe[DioUsbdevDnPullup];
  assign manual_attr_io_dnpullup0 = dio_attr[DioUsbdevDnPullup];

  // Connect DP pullup
  assign dio_in[DioUsbdevDpPullup] = manual_in_io_usb_dppullup0;
  assign manual_out_io_usb_dppullup0 = dio_out[DioUsbdevDpPullup];
  assign manual_oe_io_usb_dppullup0 = dio_oe[DioUsbdevDpPullup];
  assign manual_attr_io_dppullup0 = dio_attr[DioUsbdevDpPullup];

  // Tie-off unused signals
  assign dio_in[DioUsbdevSe0] = 1'b0;
  assign dio_in[DioUsbdevTxModeSe] = 1'b0;
  assign dio_in[DioUsbdevSuspend] = 1'b0;

  logic unused_usb_sigs;
  assign unused_usb_sigs = ^{
    // SE0
    dio_out[DioUsbdevSe0],
    dio_oe[DioUsbdevSe0],
    dio_attr[DioUsbdevSe0],
    // TX Mode
    dio_out[DioUsbdevTxModeSe],
    dio_oe[DioUsbdevTxModeSe],
    dio_attr[DioUsbdevTxModeSe],
    // Suspend
    dio_out[DioUsbdevSuspend],
    dio_oe[DioUsbdevSuspend],
    dio_attr[DioUsbdevSuspend],
    // D is used as an input only
    dio_out[DioUsbdevD],
    dio_oe[DioUsbdevD],
    dio_attr[DioUsbdevD]
  };

% endif

###################################################################
## USB for Nexysvideo                                            ##
###################################################################
% if target["name"] == "nexysvideo":

  /////////////////////
  // USB Overlay Mux //
  /////////////////////

  // TODO: generalize this USB mux code and align with other tops.

  // Software can enable the pinflip feature inside usbdev.
  // The example hello_usbdev does this based on GPIO0 (a switch on the board)
  //
  // Here, we use the state of the DN pullup to effectively undo the
  // swapping such that the PCB always sees the unflipped D+/D-. We
  // could do the same inside the .xdc file but then two FPGA
  // bitstreams would be needed for testing.
  //
  // dio_in/out/oe map is: PADS <- _padring <- JTAG mux -> _umux -> USB mux -> _core

  // Split out for differential PHY testing

  // Outputs always drive and just copy the value
  // Let them go to the normal place too because it won't do any harm
  // and it simplifies the changes needed

  // The output enable for IO_USB_DNPULLUP0 is used to decide whether we need to undo the swapping.
  logic undo_swap;
  assign undo_swap = dio_oe[DioUsbdevDnPullup];

  // GPIO[2] = Switch 2 on board is used to select using the UPHY
  // Keep GPIO[1] for selecting differential in sw
  logic use_uphy;
  assign use_uphy = mio_in[MioPadIoa2];

  // DioUsbdevDn
  assign manual_attr_usb_n = '0;
  assign manual_attr_io_uphy_dn_tx = '0;

  assign manual_out_io_uphy_dn_tx = manual_out_usb_n;
  assign manual_out_usb_n = undo_swap ? dio_out[DioUsbdevDp] :
                                        dio_out[DioUsbdevDn];

  assign manual_oe_io_uphy_dn_tx = manual_oe_usb_n;
  assign manual_oe_usb_n = undo_swap ? dio_oe[DioUsbdevDp] :
                                       dio_oe[DioUsbdevDn];

  assign dio_in[DioUsbdevDn] = use_uphy ?
                               (undo_swap ? manual_in_io_uphy_dp_rx :
                                            manual_in_io_uphy_dn_rx) :
                               (undo_swap ? manual_in_usb_p :
                                            manual_in_usb_n);
  // DioUsbdevDp
  assign manual_attr_usb_p = '0;
  assign manual_attr_io_uphy_dp_tx = '0;

  assign manual_out_io_uphy_dp_tx = manual_out_usb_p;
  assign manual_out_usb_p = undo_swap ? dio_out[DioUsbdevDn] :
                                       dio_out[DioUsbdevDp];

  assign manual_oe_io_uphy_dp_tx = manual_oe_usb_p;
  assign manual_oe_usb_p = undo_swap ? dio_oe[DioUsbdevDn] :
                                       dio_oe[DioUsbdevDp];
  assign dio_in[DioUsbdevDp] = use_uphy ?
                               (undo_swap ? manual_in_io_uphy_dn_rx :
                                            manual_in_io_uphy_dp_rx) :
                               (undo_swap ? manual_in_usb_n :
                                            manual_in_usb_p);
  // DioUsbdevD
  // This is not connected at the moment
  logic unused_out_usb_d;
  assign unused_out_usb_d = dio_out[DioUsbdevD] ^
                            dio_oe[DioUsbdevD];
  assign dio_in[DioUsbdevD] = use_uphy ?
                              (undo_swap ? ~manual_in_io_uphy_d_rx :
                                            manual_in_io_uphy_d_rx) :
                              // This is not connected at the moment
                              (undo_swap ? 1'b1 : 1'b0);
  assign manual_out_io_uphy_d_rx = 1'b0;
  assign manual_oe_io_uphy_d_rx = 1'b0;

  // DioUsbdevDnPullup
  assign manual_attr_io_usb_dnpullup0 = '0;
  assign manual_out_io_usb_dnpullup0 = undo_swap ? dio_out[DioUsbdevDpPullup] :
                                                   dio_out[DioUsbdevDnPullup];
  assign manual_oe_io_usb_dnpullup0 = undo_swap ? dio_oe[DioUsbdevDpPullup] :
                                                  dio_oe[DioUsbdevDnPullup];
  assign dio_in[DioUsbdevDnPullup] = manual_in_io_usb_dnpullup0;

  // DioUsbdevDpPullup
  assign manual_attr_io_usb_dppullup0 = '0;
  assign manual_out_io_usb_dppullup0 = undo_swap ? dio_out[DioUsbdevDnPullup] :
                                                   dio_out[DioUsbdevDpPullup];
  assign manual_oe_io_usb_dppullup0 = undo_swap ? dio_oe[DioUsbdevDnPullup] :
                                                  dio_oe[DioUsbdevDpPullup];
  assign dio_in[DioUsbdevDpPullup] = manual_in_io_usb_dppullup0;

  // DioUsbdevSense
  assign manual_out_io_usb_sense0 = dio_out[DioUsbdevSense];
  assign manual_oe_io_usb_sense0  = dio_oe[DioUsbdevSense];
  assign dio_in[DioUsbdevSense] = use_uphy ? manual_in_io_uphy_sense :
                                             manual_in_io_usb_sense0;
  assign manual_out_io_uphy_sense = 1'b0;
  assign manual_oe_io_uphy_sense = 1'b0;

  // DioUsbdevRxEnable
  assign dio_in[DioUsbdevRxEnable] = 1'b0;

  // Additional outputs for uphy
  assign manual_oe_io_uphy_dppullup = 1'b1;
  assign manual_out_io_uphy_dppullup = manual_out_io_usb_dppullup0 &
                                       manual_oe_io_usb_dppullup0;

  logic unused_in_io_uphy_dppullup;
  assign unused_in_io_uphy_dppullup = manual_in_io_uphy_dppullup;

  assign manual_oe_io_uphy_oe_n = 1'b1;
  assign manual_out_io_uphy_oe_n = ~manual_oe_usb_p;

  logic unused_in_io_uphy_oe_n;
  assign unused_in_io_uphy_oe_n = manual_in_io_uphy_oe_n;

% endif

###################################################################
## ASIC                                                          ##
###################################################################
% if target["name"] == "asic":

  //////////////////////////////////
  // Manual Pad / Signal Tie-offs //
  //////////////////////////////////

  assign manual_out_por_n = 1'b0;
  assign manual_oe_por_n = 1'b0;

  assign manual_out_cc1 = 1'b0;
  assign manual_oe_cc1 = 1'b0;
  assign manual_out_cc2 = 1'b0;
  assign manual_oe_cc2 = 1'b0;

  assign manual_out_flash_test_mode0 = 1'b0;
  assign manual_oe_flash_test_mode0 = 1'b0;
  assign manual_out_flash_test_mode1 = 1'b0;
  assign manual_oe_flash_test_mode1 = 1'b0;
  assign manual_out_flash_test_volt = 1'b0;
  assign manual_oe_flash_test_volt = 1'b0;
  assign manual_out_otp_ext_volt = 1'b0;
  assign manual_oe_otp_ext_volt = 1'b0;

  // These pad attributes currently tied off permanently (these are all input-only pads).
  assign manual_attr_por_n = '0;
  assign manual_attr_cc1 = '0;
  assign manual_attr_cc2 = '0;
  assign manual_attr_flash_test_mode0 = '0;
  assign manual_attr_flash_test_mode1 = '0;
  assign manual_attr_flash_test_volt = '0;
  assign manual_attr_otp_ext_volt = '0;

  logic unused_manual_sigs;
  assign unused_manual_sigs = ^{
    manual_in_cc2,
    manual_in_cc1,
    manual_in_flash_test_volt,
    manual_in_flash_test_mode0,
    manual_in_flash_test_mode1,
    manual_in_otp_ext_volt
  };

  ///////////////////////////////
  // Differential USB Receiver //
  ///////////////////////////////

  // TODO: generalize this USB mux code and align with other tops.

  // Connect the DP pad
  assign dio_in[DioUsbdevDp] = manual_in_usb_p;
  assign manual_out_usb_p = dio_out[DioUsbdevDp];
  assign manual_oe_usb_p = dio_oe[DioUsbdevDp];
  assign manual_attr_usb_p = dio_attr[DioUsbdevDp];

  // Connect the DN pad
  assign dio_in[DioUsbdevDn] = manual_in_usb_n;
  assign manual_out_usb_n = dio_out[DioUsbdevDn];
  assign manual_oe_usb_n = dio_oe[DioUsbdevDn];
  assign manual_attr_usb_n = dio_attr[DioUsbdevDn];

  // Pullups
  logic usb_pullup_p_en, usb_pullup_n_en;
  assign usb_pullup_p_en = dio_out[DioUsbdevDpPullup] & dio_oe[DioUsbdevDpPullup];
  assign usb_pullup_n_en = dio_out[DioUsbdevDnPullup] & dio_oe[DioUsbdevDnPullup];

  logic usb_rx_enable;
  assign usb_rx_enable = dio_out[DioUsbdevRxEnable] & dio_oe[DioUsbdevRxEnable];

  logic [ast_pkg::UsbCalibWidth-1:0] usb_io_pu_cal;

  // pwrmgr interface
  pwrmgr_pkg::pwr_ast_req_t base_ast_pwr;
  pwrmgr_pkg::pwr_ast_rsp_t ast_base_pwr;

  prim_usb_diff_rx #(
    .CalibW(ast_pkg::UsbCalibWidth)
  ) u_prim_usb_diff_rx (
    .input_pi      ( USB_P                 ),
    .input_ni      ( USB_N                 ),
    .input_en_i    ( usb_rx_enable         ),
    .core_pok_i    ( ast_base_pwr.main_pok ),
    .pullup_p_en_i ( usb_pullup_p_en       ),
    .pullup_n_en_i ( usb_pullup_n_en       ),
    .calibration_i ( usb_io_pu_cal         ),
    .input_o       ( dio_in[DioUsbdevD]    )
  );

  // Tie-off unused signals
  assign dio_in[DioUsbdevSense] = 1'b0;
  assign dio_in[DioUsbdevSe0] = 1'b0;
  assign dio_in[DioUsbdevDpPullup] = 1'b0;
  assign dio_in[DioUsbdevDnPullup] = 1'b0;
  assign dio_in[DioUsbdevTxModeSe] = 1'b0;
  assign dio_in[DioUsbdevSuspend] = 1'b0;
  assign dio_in[DioUsbdevRxEnable] = 1'b0;

  logic unused_usb_sigs;
  assign unused_usb_sigs = ^{
    // Sense
    dio_out[DioUsbdevSense],
    dio_oe[DioUsbdevSense],
    dio_attr[DioUsbdevSense],
    // SE0
    dio_out[DioUsbdevSe0],
    dio_oe[DioUsbdevSe0],
    dio_attr[DioUsbdevSe0],
    // TX Mode
    dio_out[DioUsbdevTxModeSe],
    dio_oe[DioUsbdevTxModeSe],
    dio_attr[DioUsbdevTxModeSe],
    // Suspend
    dio_out[DioUsbdevSuspend],
    dio_oe[DioUsbdevSuspend],
    dio_attr[DioUsbdevSuspend],
    // Rx enable
    dio_attr[DioUsbdevRxEnable],
    // D is used as an input only
    dio_out[DioUsbdevD],
    dio_oe[DioUsbdevD],
    dio_attr[DioUsbdevD],
    // Pullup/down
    dio_attr[DioUsbdevDpPullup],
    dio_attr[DioUsbdevDnPullup]
  };

  //////////////////////
  // AST              //
  //////////////////////
  // TLUL interface
  tlul_pkg::tl_h2d_t base_ast_bus;
  tlul_pkg::tl_d2h_t ast_base_bus;

  // assorted ast status
  ast_pkg::ast_status_t ast_status;

  // ast clocks and resets
  logic aon_pok;

  // synchronization clocks / rests
  clkmgr_pkg::clkmgr_ast_out_t clks_ast;
  rstmgr_pkg::rstmgr_ast_out_t rsts_ast;

  // otp power sequence
  otp_ctrl_pkg::otp_ast_req_t otp_ctrl_otp_ast_pwr_seq;
  otp_ctrl_pkg::otp_ast_rsp_t otp_ctrl_otp_ast_pwr_seq_h;

  logic usb_ref_pulse;
  logic usb_ref_val;

  // adc
  ast_pkg::adc_ast_req_t adc_req;
  ast_pkg::adc_ast_rsp_t adc_rsp;

  // entropy source interface
  // The entropy source pacakge definition should eventually be moved to es
  entropy_src_pkg::entropy_src_rng_req_t es_rng_req;
  entropy_src_pkg::entropy_src_rng_rsp_t es_rng_rsp;
  logic es_rng_fips;

  // entropy distribution network
  edn_pkg::edn_req_t ast_edn_edn_req;
  edn_pkg::edn_rsp_t ast_edn_edn_rsp;

  // alerts interface
  ast_pkg::ast_alert_rsp_t ast_alert_rsp;
  ast_pkg::ast_alert_req_t ast_alert_req;

  // Flash connections
  lc_ctrl_pkg::lc_tx_t flash_bist_enable;
  logic flash_power_down_h;
  logic flash_power_ready_h;

  // Life cycle clock bypass req/ack
  lc_ctrl_pkg::lc_tx_t ast_clk_byp_req;
  lc_ctrl_pkg::lc_tx_t ast_clk_byp_ack;

  // DFT connections
  logic scan_en;
  lc_ctrl_pkg::lc_tx_t dft_en;
  pinmux_pkg::dft_strap_test_req_t dft_strap_test;

  // Debug connections
  logic [ast_pkg::Ast2PadOutWidth-1:0] ast2pinmux;
  logic [ast_pkg::Pad2AstInWidth-1:0] pad2ast;

  assign pad2ast = {
                     mio_in_raw[MioPadIoc3],
                     mio_in_raw[MioPadIob8],
                     mio_in_raw[MioPadIob7],
                     mio_in_raw[MioPadIob2],
                     mio_in_raw[MioPadIob1],
                     mio_in_raw[MioPadIob0]
                   };


  // Jitter enable
  logic jen;

  // reset domain connections
  import rstmgr_pkg::PowerDomains;
  import rstmgr_pkg::DomainAonSel;
  import rstmgr_pkg::Domain0Sel;

  // external clock comes in at a fixed position
  logic ext_clk;
  assign ext_clk = mio_in_raw[MioPadIoc6];

  // Memory configuration connections
  ast_pkg::spm_rm_t ast_ram_1p_cfg;
  ast_pkg::spm_rm_t ast_rf_cfg;
  ast_pkg::spm_rm_t ast_rom_cfg;
  ast_pkg::dpm_rm_t ast_ram_2p_fcfg;
  ast_pkg::dpm_rm_t ast_ram_2p_lcfg;

  prim_ram_1p_pkg::ram_1p_cfg_t ram_1p_cfg;
  prim_ram_2p_pkg::ram_2p_cfg_t ram_2p_cfg;
  prim_rom_pkg::rom_cfg_t rom_cfg;

  // conversion from ast structure to memory centric structures
  assign ram_1p_cfg = '{
    ram_cfg: '{
                cfg_en: ast_ram_1p_cfg.marg_en,
                cfg:    ast_ram_1p_cfg.marg
              },
    rf_cfg:  '{
                cfg_en: ast_rf_cfg.marg_en,
                cfg:    ast_rf_cfg.marg
              }
  };

  assign ram_2p_cfg = '{
    a_ram_fcfg: '{
                   cfg_en: ast_ram_2p_fcfg.marg_en_a,
                   cfg:    ast_ram_2p_fcfg.marg_a
                 },
    a_ram_lcfg: '{
                   cfg_en: ast_ram_2p_lcfg.marg_en_a,
                   cfg:    ast_ram_2p_lcfg.marg_a
                 },
    b_ram_fcfg: '{
                   cfg_en: ast_ram_2p_fcfg.marg_en_b,
                   cfg:    ast_ram_2p_fcfg.marg_b
                 },
    b_ram_lcfg: '{
                   cfg_en: ast_ram_2p_lcfg.marg_en_b,
                   cfg:    ast_ram_2p_lcfg.marg_b
                 }
  };

  assign rom_cfg = '{
    cfg_en: ast_rom_cfg.marg_en,
    cfg: ast_rom_cfg.marg
  };


  // AST does not use all clocks / resets forwarded to it
  logic unused_slow_clk_en;
  logic unused_usb_clk_aon;
  logic unused_usb_clk_io_div4;
  assign unused_slow_clk_en = base_ast_pwr.slow_clk_en;
  assign unused_usb_clk_aon = clks_ast.clk_ast_usbdev_aon_peri;
  assign unused_usb_clk_io_div4 = clks_ast.clk_ast_usbdev_io_div4_peri;

  logic unused_usb_usb_rst;
  logic [PowerDomains-1:0] unused_usb_sys_io_div4_rst;
  logic [PowerDomains-1:0] unused_usb_sys_aon_rst;
  logic unused_ast_sys_io_div4_rst;
  logic unused_sensor_ctrl_sys_io_div4_rst;
  logic unused_adc_ctrl_sys_io_div4_rst;
  logic unused_entropy_sys_rst;
  logic unused_edn_sys_rst;
  assign unused_usb_usb_rst = rsts_ast.rst_ast_usbdev_usb_n[DomainAonSel];
  assign unused_usb_sys_io_div4_rst = rsts_ast.rst_ast_usbdev_sys_io_div4_n;
  assign unused_usb_sys_aon_rst = rsts_ast.rst_ast_usbdev_sys_aon_n;
  assign unused_ast_sys_io_div4_rst =
    rsts_ast.rst_ast_ast_sys_io_div4_n[Domain0Sel];
  assign unused_sensor_ctrl_sys_io_div4_rst =
    rsts_ast.rst_ast_sensor_ctrl_aon_sys_io_div4_n[Domain0Sel];
  assign unused_adc_ctrl_sys_io_div4_rst =
    rsts_ast.rst_ast_adc_ctrl_aon_sys_io_div4_n[Domain0Sel];
  assign unused_entropy_sys_rst = rsts_ast.rst_ast_entropy_src_sys_n[DomainAonSel];
  assign unused_edn_sys_rst = rsts_ast.rst_ast_edn0_sys_n[DomainAonSel];

  ast_pkg::ast_dif_t flash_alert;
  ast_pkg::ast_dif_t otp_alert;
  logic ast_init_done;

  ast #(
    .EntropyStreams(ast_pkg::EntropyStreams),
    .AdcChannels(ast_pkg::AdcChannels),
    .AdcDataWidth(ast_pkg::AdcDataWidth),
    .UsbCalibWidth(ast_pkg::UsbCalibWidth),
    .Ast2PadOutWidth(ast_pkg::Ast2PadOutWidth),
    .Pad2AstInWidth(ast_pkg::Pad2AstInWidth)
  ) u_ast (
    // tlul
    .tl_i                  ( base_ast_bus ),
    .tl_o                  ( ast_base_bus ),
    // init done indication
    .ast_init_done_o       ( ast_init_done ),
    // buffered clocks & resets
    // Reset domain connection is manual at the moment
    .clk_ast_adc_i         ( clks_ast.clk_ast_adc_ctrl_aon_io_div4_peri ),
    .rst_ast_adc_ni        ( rsts_ast.rst_ast_adc_ctrl_aon_sys_io_div4_n[DomainAonSel] ),
    .clk_ast_alert_i       ( clks_ast.clk_ast_sensor_ctrl_aon_io_div4_secure ),
    .rst_ast_alert_ni      ( rsts_ast.rst_ast_sensor_ctrl_aon_sys_io_div4_n[DomainAonSel] ),
    .clk_ast_es_i          ( clks_ast.clk_ast_edn0_main_secure ),
    .rst_ast_es_ni         ( rsts_ast.rst_ast_edn0_sys_n[Domain0Sel] ),
    .clk_ast_rng_i         ( clks_ast.clk_ast_entropy_src_main_secure ),
    .rst_ast_rng_ni        ( rsts_ast.rst_ast_entropy_src_sys_n[Domain0Sel] ),
    .clk_ast_tlul_i        ( clks_ast.clk_ast_ast_io_div4_secure ),
    .rst_ast_tlul_ni       ( rsts_ast.rst_ast_ast_sys_io_div4_n[DomainAonSel] ),
    .clk_ast_usb_i         ( clks_ast.clk_ast_usbdev_usb_peri ),
    .rst_ast_usb_ni        ( rsts_ast.rst_ast_usbdev_usb_n[Domain0Sel] ),
    .clk_ast_ext_i         ( ext_clk ),
    .por_ni                ( manual_in_por_n ),
    // pok test for FPGA
    .vcc_supp_i            ( 1'b1 ),
    .vcaon_supp_i          ( 1'b1 ),
    .vcmain_supp_i         ( 1'b1 ),
    .vioa_supp_i           ( 1'b1 ),
    .viob_supp_i           ( 1'b1 ),
    // pok
    .vcaon_pok_o           ( aon_pok ),
    .vcmain_pok_o          ( ast_base_pwr.main_pok ),
    .vioa_pok_o            ( ast_status.io_pok[0] ),
    .viob_pok_o            ( ast_status.io_pok[1] ),
    // main regulator
    .main_env_iso_en_i     ( base_ast_pwr.pwr_clamp_env ),
    .main_pd_ni            ( base_ast_pwr.main_pd_n ),
    // pdm control (flash)/otp
    .flash_power_down_h_o  ( flash_power_down_h ),
    .flash_power_ready_h_o ( flash_power_ready_h ),
    .otp_power_seq_i       ( otp_ctrl_otp_ast_pwr_seq ),
    .otp_power_seq_h_o     ( otp_ctrl_otp_ast_pwr_seq_h ),
    // system source clock
    .clk_src_sys_en_i      ( base_ast_pwr.core_clk_en ),
    // need to add function in clkmgr
    .clk_src_sys_jen_i     ( jen ),
    .clk_src_sys_o         ( ast_base_clks.clk_sys  ),
    .clk_src_sys_val_o     ( ast_base_pwr.core_clk_val ),
    // aon source clock
    .clk_src_aon_o         ( ast_base_clks.clk_aon ),
    .clk_src_aon_val_o     ( ast_base_pwr.slow_clk_val ),
    // io source clock
    .clk_src_io_en_i       ( base_ast_pwr.io_clk_en ),
    .clk_src_io_o          ( ast_base_clks.clk_io ),
    .clk_src_io_val_o      ( ast_base_pwr.io_clk_val ),
    // usb source clock
    .usb_ref_pulse_i       ( usb_ref_pulse ),
    .usb_ref_val_i         ( usb_ref_val ),
    .clk_src_usb_en_i      ( base_ast_pwr.usb_clk_en ),
    .clk_src_usb_o         ( ast_base_clks.clk_usb ),
    .clk_src_usb_val_o     ( ast_base_pwr.usb_clk_val ),
    // USB IO Pull-up Calibration Setting
    .usb_io_pu_cal_o       ( usb_io_pu_cal ),
    // adc
    .adc_a0_ai             ( CC1 ),
    .adc_a1_ai             ( CC2 ),
    .adc_pd_i              ( adc_req.pd ),
    .adc_chnsel_i          ( adc_req.channel_sel ),
    .adc_d_o               ( adc_rsp.data ),
    .adc_d_val_o           ( adc_rsp.data_valid ),
    // rng
    .rng_en_i              ( es_rng_req.rng_enable ),
    .rng_fips_i            ( es_rng_fips ),
    .rng_val_o             ( es_rng_rsp.rng_valid ),
    .rng_b_o               ( es_rng_rsp.rng_b ),
    // entropy
    .entropy_rsp_i         ( ast_edn_edn_rsp ),
    .entropy_req_o         ( ast_edn_edn_req ),
    // alerts
    .fla_alert_in_i        ( flash_alert    ),
    .otp_alert_in_i        ( otp_alert      ),
    .alert_rsp_i           ( ast_alert_rsp  ),
    .alert_req_o           ( ast_alert_req  ),
    // dft
    .dft_strap_test_i      ( dft_strap_test   ),
    .lc_dft_en_i           ( dft_en           ),
    // pinmux related
    .padmux2ast_i          ( pad2ast    ),
    .ast2padmux_o          ( ast2pinmux ),
    // Direct short to PAD
    .pad2ast_t0_ai         ( IOA4 ),
    .pad2ast_t1_ai         ( IOA5 ),
    .ast2pad_t0_ao         ( IOA2 ),
    .ast2pad_t1_ao         ( IOA3 ),
    .lc_clk_byp_req_i      ( ast_clk_byp_req   ),
    .lc_clk_byp_ack_o      ( ast_clk_byp_ack   ),
    .flash_bist_en_o       ( flash_bist_enable ),
    // Memory configuration connections
    .dpram_rmf_o           ( ast_ram_2p_fcfg ),
    .dpram_rml_o           ( ast_ram_2p_lcfg ),
    .spram_rm_o            ( ast_ram_1p_cfg  ),
    .sprgf_rm_o            ( ast_rf_cfg      ),
    .sprom_rm_o            ( ast_rom_cfg     ),
    // scan
    .dft_scan_md_o         ( scanmode ),
    .scan_shift_en_o       ( scan_en ),
    .scan_reset_no         ( scan_rst_n )
  );

  //////////////////////
  // Top-level design //
  //////////////////////

  top_${top["name"]} #(
    .AesMasking(1'b1),
    .AesSBoxImpl(aes_pkg::SBoxImplDom),
    .SecAesStartTriggerDelay(0),
    .SecAesAllowForcingMasks(1'b0),
    .KmacEnMasking(1),  // DOM AND + Masking scheme
    .KmacReuseShare(0),
    .SramCtrlRetAonInstrExec(0),
    .SramCtrlMainInstrExec(1),
    .PinmuxAonTargetCfg(PinmuxTargetCfg),
    .RomCtrlSkipCheck(RomCtrlSkipCheck)
  ) top_${top["name"]} (
    .rst_ni                       ( aon_pok                    ),
    // ast connections
    .clk_main_i                   ( ast_base_clks.clk_sys      ),
    .clk_io_i                     ( ast_base_clks.clk_io       ),
    .clk_usb_i                    ( ast_base_clks.clk_usb      ),
    .clk_aon_i                    ( ast_base_clks.clk_aon      ),
    .clks_ast_o                   ( clks_ast                   ),
    .clk_main_jitter_en_o         ( jen                        ),
    .rsts_ast_o                   ( rsts_ast                   ),
    .pwrmgr_ast_req_o             ( base_ast_pwr               ),
    .pwrmgr_ast_rsp_i             ( ast_base_pwr               ),
    .sensor_ctrl_ast_alert_req_i  ( ast_alert_req              ),
    .sensor_ctrl_ast_alert_rsp_o  ( ast_alert_rsp              ),
    .sensor_ctrl_ast_status_i     ( ast_status                 ),
    .usbdev_usb_ref_val_o         ( usb_ref_pulse              ),
    .usbdev_usb_ref_pulse_o       ( usb_ref_val                ),
    .ast_tl_req_o                 ( base_ast_bus               ),
    .ast_tl_rsp_i                 ( ast_base_bus               ),
    .adc_req_o                    ( adc_req                    ),
    .adc_rsp_i                    ( adc_rsp                    ),
    .ast_edn_req_i                ( ast_edn_edn_req            ),
    .ast_edn_rsp_o                ( ast_edn_edn_rsp            ),
    .otp_ctrl_otp_ast_pwr_seq_o   ( otp_ctrl_otp_ast_pwr_seq   ),
    .otp_ctrl_otp_ast_pwr_seq_h_i ( otp_ctrl_otp_ast_pwr_seq_h ),
    .otp_alert_o                  ( otp_alert                  ),
    .flash_bist_enable_i          ( flash_bist_enable          ),
    .flash_power_down_h_i         ( flash_power_down_h         ),
    .flash_power_ready_h_i        ( flash_power_ready_h        ),
    .flash_alert_o                ( flash_alert                ),
    .es_rng_req_o                 ( es_rng_req                 ),
    .es_rng_rsp_i                 ( es_rng_rsp                 ),
    .es_rng_fips_o                ( es_rng_fips                ),
    .ast_clk_byp_req_o            ( ast_clk_byp_req            ),
    .ast_clk_byp_ack_i            ( ast_clk_byp_ack            ),
    .ast2pinmux_i                 ( ast2pinmux                 ),
    .ast_init_done_i              ( ast_init_done              ),

    // Flash test mode voltages
    .flash_test_mode_a_io         ( {FLASH_TEST_MODE1,
                                     FLASH_TEST_MODE0}         ),
    .flash_test_voltage_h_io      ( FLASH_TEST_VOLT            ),

    // OTP external voltage
    .otp_ext_voltage_h_io         ( OTP_EXT_VOLT               ),

    // Multiplexed I/O
    .mio_in_i                     ( mio_in                     ),
    .mio_out_o                    ( mio_out                    ),
    .mio_oe_o                     ( mio_oe                     ),

    // Dedicated I/O
    .dio_in_i                     ( dio_in                     ),
    .dio_out_o                    ( dio_out                    ),
    .dio_oe_o                     ( dio_oe                     ),

    // Pad attributes
    .mio_attr_o                   ( mio_attr                   ),
    .dio_attr_o                   ( dio_attr                   ),

    // Memory attributes
    .ram_1p_cfg_i                 ( ram_1p_cfg                 ),
    .ram_2p_cfg_i                 ( ram_2p_cfg                 ),
    .rom_cfg_i                    ( rom_cfg                    ),

    // DFT signals
    .ast_lc_dft_en_o              ( dft_en                     ),
    .dft_strap_test_o             ( dft_strap_test             ),
    .dft_hold_tap_sel_i           ( '0                         ),
    .scan_rst_ni                  ( scan_rst_n                 ),
    .scan_en_i                    ( scan_en                    ),
    .scanmode_i                   ( scanmode                   )
  );
% endif

###################################################################
## FPGA shared                                                   ##
###################################################################
% if target["name"] in ["cw305", "nexysvideo"]:
  //////////////////
  // PLL for FPGA //
  //////////////////

  assign manual_out_io_clk = 1'b0;
  assign manual_oe_io_clk = 1'b0;
  assign manual_out_por_n = 1'b0;
  assign manual_oe_por_n = 1'b0;
  assign manual_out_io_jsrst_n = 1'b0;
  assign manual_oe_io_jsrst_n = 1'b0;

  logic clk_main, clk_usb_48mhz, clk_aon, rst_n;
  clkgen_xil7series # (
    .AddClkBuf(0)
  ) clkgen (
    .clk_i(manual_in_io_clk),
    .rst_ni(manual_in_por_n),
    .jtag_srst_ni(manual_in_io_jsrst_n),
    .clk_main_o(clk_main),
    .clk_48MHz_o(clk_usb_48mhz),
    .clk_aon_o(clk_aon),
    .rst_no(rst_n)
  );

  //////////////////////
  // Top-level design //
  //////////////////////
  pwrmgr_pkg::pwr_ast_rsp_t ast_base_pwr;
  ast_pkg::ast_alert_req_t ast_base_alerts;
  ast_pkg::ast_status_t ast_base_status;

  assign ast_base_pwr.slow_clk_val = 1'b1;
  assign ast_base_pwr.core_clk_val = 1'b1;
  assign ast_base_pwr.io_clk_val   = 1'b1;
  assign ast_base_pwr.usb_clk_val  = 1'b1;
  assign ast_base_pwr.main_pok     = 1'b1;

  ast_pkg::ast_dif_t silent_alert = '{
                                       p: 1'b0,
                                       n: 1'b1
                                     };

  assign ast_base_alerts.alerts = {ast_pkg::NumAlerts{silent_alert}};
  assign ast_base_status.io_pok = {ast_pkg::NumIoRails{1'b1}};

  // the rst_ni pin only goes to AST
  // the rest of the logic generates reset based on the 'pok' signal.
  // for verilator purposes, make these two the same.
  lc_ctrl_pkg::lc_tx_t lc_clk_bypass;

% if target["name"] == "cw305":
  // This is used for outputting the capture trigger
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_out_pre;
% endif

// TODO: align this with ASIC version to minimize the duplication.
// Also need to add AST simulation and FPGA emulation models for things like entropy source -
// otherwise Verilator / FPGA will hang.
  top_${top["name"]} #(
% if target["name"] == "cw305":
    .AesMasking(1'b1),
    .AesSBoxImpl(aes_pkg::SBoxImplDom),
    .SecAesStartTriggerDelay(40),
    .SecAesAllowForcingMasks(1'b1),
    .SecAesSkipPRNGReseeding(1'b1),
    .IbexICache(0),
    .BootRomInitFile(BootRomInitFile),
% else:
    .AesMasking(1'b0),
    .AesSBoxImpl(aes_pkg::SBoxImplLut),
    .SecAesStartTriggerDelay(0),
    .SecAesAllowForcingMasks(1'b0),
    .SecAesSkipPRNGReseeding(1'b0),
    .EntropySrcStub(1'b1),
    .CsrngSBoxImpl(aes_pkg::SBoxImplLut),
    .OtbnRegFile(otbn_pkg::RegFileFPGA),
    .OtbnStub(1'b1),
    .OtpCtrlMemInitFile(OtpCtrlMemInitFile),
    .RomCtrlBootRomInitFile(BootRomInitFile),
% endif
    .IbexRegFile(ibex_pkg::RegFileFPGA),
    .IbexPipeLine(1),
    .SecureIbex(0),
    .SramCtrlRetAonInstrExec(0),
    .SramCtrlMainInstrExec(1),
    .PinmuxAonTargetCfg(PinmuxTargetCfg)
  ) top_${top["name"]} (
    .rst_ni                       ( rst_n            ),
    .clk_main_i                   ( clk_main         ),
    .clk_io_i                     ( clk_main         ),
    .clk_usb_i                    ( clk_usb_48mhz    ),
    .clk_aon_i                    ( clk_aon          ),
    .clks_ast_o                   (                  ),
    .clk_main_jitter_en_o         (                  ),
    .rsts_ast_o                   (                  ),
    .pwrmgr_ast_req_o             (                  ),
    .pwrmgr_ast_rsp_i             ( ast_base_pwr     ),
    .sensor_ctrl_ast_alert_req_i  ( ast_base_alerts  ),
    .sensor_ctrl_ast_alert_rsp_o  (                  ),
    .sensor_ctrl_ast_status_i     ( ast_base_status  ),
    .usbdev_usb_ref_val_o         (                  ),
    .usbdev_usb_ref_pulse_o       (                  ),
    .ast_edn_req_i                ( '0               ),
    .ast_edn_rsp_o                (                  ),
    .flash_bist_enable_i          ( lc_ctrl_pkg::Off ),
    .flash_power_down_h_i         ( 1'b0             ),
    .flash_power_ready_h_i        ( 1'b1             ),
    .ast_clk_byp_req_o            ( lc_clk_bypass    ),
    .ast_clk_byp_ack_i            ( lc_clk_bypass    ),

% if target["name"] != "cw305":
    .ast_tl_req_o                 (                  ),
    .ast_tl_rsp_i                 ( '0               ),
    .otp_ctrl_otp_ast_pwr_seq_o   (                  ),
    .otp_ctrl_otp_ast_pwr_seq_h_i ( '0               ),
    .otp_alert_o                  (                  ),
    .es_rng_req_o                 (                  ),
    .es_rng_rsp_i                 ( '0               ),
    .es_rng_fips_o                (                  ),
    .ast2pinmux_i                 ( '0               ),
% endif

    // Multiplexed I/O
    .mio_in_i        ( mio_in   ),
% if target["name"] == "cw305":
    .mio_out_o       ( mio_out_pre  ),
% else:
    .mio_out_o       ( mio_out  ),
% endif
    .mio_oe_o        ( mio_oe   ),

    // Dedicated I/O
    .dio_in_i        ( dio_in   ),
    .dio_out_o       ( dio_out  ),
    .dio_oe_o        ( dio_oe   ),

    // Pad attributes
    .mio_attr_o      ( mio_attr      ),
    .dio_attr_o      ( dio_attr      ),

    // Memory attributes
    .ram_1p_cfg_i    ( '0 ),
    .ram_2p_cfg_i    ( '0 ),
    .rom_cfg_i       ( '0 ),

    // DFT signals
    .dft_hold_tap_sel_i ( '0               ),
    .scan_rst_ni        ( 1'b1             ),
    .scan_en_i          ( 1'b0             ),
    .scanmode_i         ( lc_ctrl_pkg::Off )
  );
% endif


###################################################################
## CW305 capture trigger                                         ##
###################################################################
% if target["name"] == "cw305":

  //////////////////////////////////////
  // Generate precise capture trigger //
  //////////////////////////////////////

  // TODO: make this a "manual" IO specific to the CW305 target
  // such that we can decouple this from the MIO signals.
  localparam int MioIdxTrigger = 15;

  // To obtain a more precise capture trigger for side-channel analysis, we only forward the
  // software-controlled capture trigger when the AES module is actually busy (performing
  // either encryption/decryption or clearing internal registers).
  // GPIO15 is used as capture trigger (mapped to IOB9 at the moment in pinmux.c).
  always_comb begin : p_trigger
    mio_out = mio_out_pre;
    mio_out[MioIdxTrigger] = mio_out_pre[MioIdxTrigger] &
                             ~top_englishbreakfast.clkmgr_aon_idle[clkmgr_pkg::Aes];
  end

  //////////////////////
  // ChipWhisperer IO //
  //////////////////////

  logic unused_inputs;
  assign unused_inputs = manual_in_tio_clkout ^ manual_in_io_utx_debug;

  // Clock ouput to capture board.
  assign manual_out_tio_clkout = manual_in_io_clk;
  assign manual_oe_tio_clkout = 1'b1;

  // UART Tx for debugging. The UART itself is connected to the capture board.
  assign manual_out_io_utx_debug = top_${top["name"]}.cio_uart0_tx_d2p;
  assign manual_oe_io_utx_debug = 1'b1;

% endif

endmodule : chip_${top["name"]}_${target["name"]}
