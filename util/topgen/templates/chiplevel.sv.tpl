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

cpu_clk = top['clocks'].hier_paths['top'] + "clk_proc_main"

unused_im_defs, undriven_im_defs = lib.get_dangling_im_def(top["inter_signal"]["definitions"])

%>\

% if target["name"] != "asic":
module chip_${top["name"]}_${target["name"]} #(
  // Path to a VMEM file containing the contents of the boot ROM, which will be
  // baked into the FPGA bitstream.
  parameter BootRomInitFile = "test_rom_fpga_${target["name"]}.32.vmem",
  // Path to a VMEM file containing the contents of the emulated OTP, which will be
  // baked into the FPGA bitstream.
  parameter OtpCtrlMemInitFile = "otp_img_fpga_${target["name"]}.vmem"
) (
% else:
module chip_${top["name"]}_${target["name"]} #(
% if lib.num_rom_ctrl(top["module"]) > 1:
  parameter bit SecRomCtrl0DisableScrambling = 1'b0,
  parameter bit SecRomCtrl1DisableScrambling = 1'b0
% else:
  parameter bit SecRomCtrl0DisableScrambling = 1'b0
% endif
) (
% endif
<%
  removed_port_names = []
%>\
  // Dedicated Pads
% for pad in dedicated_pads:
<%
  sig = get_dio_sig(pinmux, pad)
  if pad["name"] in target["pinout"]["remove_ports"]:
    port_comment = "// Removed port: "
    removed_port_names.append(pad["name"])
  else:
    port_comment = ""
  if sig is not None:
    comment = "// Dedicated Pad for {}".format(sig["name"])
  else:
    comment = "// Manual Pad"
%>\
  ${port_comment}${pad["port_type"]} ${pad["name"]}, ${comment}
% endfor

  // Muxed Pads
% for pad in muxed_pads:
<%
  if pad["name"] in target["pinout"]["remove_ports"]:
    port_comment = "// Removed port: "
    removed_port_names.append(pad["name"])
  else:
    port_comment = ""
%>\
  ${port_comment}${pad["port_type"]} ${pad["name"]}${" " if loop.last else ","} // MIO Pad ${pad["idx"]}
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
  localparam int ${param_name} = ${entry["idx"]};
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
% if top["name"] != "darjeeling":
    usb_dp_idx:        DioUsbdevUsbDp,
    usb_dn_idx:        DioUsbdevUsbDn,
    usb_sense_idx:     MioInUsbdevSense,
% else:
    // The use of these indexes is gated behind a parameter, but to synthesize they
    // need to exist even if the code-path is never used (pinmux.sv:UsbWkupModuleEn).
    // Hence, set to zero.
    usb_dp_idx:        0,
    usb_dn_idx:        0,
    usb_sense_idx:     0,
% endif
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

  % if removed_port_names:
  // Net definitions for removed ports
  % endif
  % for port in removed_port_names:
  wire ${port};
  % endfor

  pad_attr_t [pinmux_reg_pkg::NMioPads-1:0] mio_attr;
  pad_attr_t [pinmux_reg_pkg::NDioPads-1:0] dio_attr;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_out;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_oe;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_in;
  logic [pinmux_reg_pkg::NMioPads-1:0] mio_in_raw;
  logic [${len(dedicated_pads)}-1:0] dio_in_raw;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_out;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_oe;
  logic [pinmux_reg_pkg::NDioPads-1:0] dio_in;

  logic unused_mio_in_raw;
  logic unused_dio_in_raw;
  assign unused_mio_in_raw = ^mio_in_raw;
  assign unused_dio_in_raw = ^dio_in_raw;

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
  assign mio_in_raw[${pad["idx"]}] = 1'b0;
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

  ast_pkg::ast_clks_t ast_base_clks;

% if target["name"] == "asic":
  // AST signals needed in padring
  logic scan_rst_n;
   prim_mubi_pkg::mubi4_t scanmode;
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
    .scanmode_i   ( prim_mubi_pkg::MuBi4False ),
  % endif
    .dio_in_raw_o ( dio_in_raw ),
    // Chip IOs
    .dio_pad_io ({
% for pad in list(reversed(dedicated_pads)):
  % if re.match(r"`INOUT_A?", pad["port_type"]):
`ifdef ANALOGSIM
      '0,
`else
      ${pad["name"]}${"" if loop.last else ","}
`endif
  % else:
      ${pad["name"]}${"" if loop.last else ","}
  % endif
% endfor
    }),

    .mio_pad_io ({
% for pad in list(reversed(muxed_pads)):
  % if re.match(r"`INOUT_A?", pad["port_type"]):
`ifdef ANALOGSIM
      '0,
`else
      ${pad["name"]}${"" if loop.last else ","}
`endif
  % else:
      ${pad["name"]}${"" if loop.last else ","}
  % endif
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

% for port in ["in_o", "out_i", "oe_i", "attr_i", "in_raw_o"]:
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
  logic usb_dp_pullup_en;
  logic usb_dn_pullup_en;
  logic usb_rx_d;
  logic usb_tx_d;
  logic usb_tx_se0;
  logic usb_tx_use_d_se0;
  logic usb_rx_enable;

  // Connect the DP pad
  assign dio_in[DioUsbdevUsbDp] = manual_in_usb_p;
  assign manual_out_usb_p = dio_out[DioUsbdevUsbDp];
  assign manual_oe_usb_p = dio_oe[DioUsbdevUsbDp];
  assign manual_attr_usb_p = dio_attr[DioUsbdevUsbDp];

  // Connect the DN pad
  assign dio_in[DioUsbdevUsbDn] = manual_in_usb_n;
  assign manual_out_usb_n = dio_out[DioUsbdevUsbDn];
  assign manual_oe_usb_n = dio_oe[DioUsbdevUsbDn];
  assign manual_attr_usb_n = dio_attr[DioUsbdevUsbDn];

  // Connect DN pullup
  assign manual_out_io_usb_dnpullup0 = usb_dn_pullup_en;
  assign manual_oe_io_usb_dnpullup0 = 1'b1;
  assign manual_attr_io_dnpullup0 = '0;

  // Connect DP pullup
  assign manual_out_io_usb_dppullup0 = usb_dp_pullup_en;
  assign manual_oe_io_usb_dppullup0 = 1'b1;
  assign manual_attr_io_dppullup0 = '0;

  // Tie-off unused signals
  assign usb_rx_d = 1'b0;

% endif
###################################################################
## USB for CW310                                                 ##
###################################################################
% if target["name"] == "cw310":
  % if "usbdev" in {module["type"] for module in top["module"]}:
  // TODO: generalize this USB mux code and align with other tops.

  // Only use the UPHY on CW310, which does not support pin flipping.
  logic usb_dp_pullup_en;
  logic usb_dn_pullup_en;
  logic usb_rx_d;
  logic usb_tx_d;
  logic usb_tx_se0;
  logic usb_rx_enable;

  // DioUsbdevUsbDn
  assign manual_attr_io_usb_dn_tx = '0;
  assign manual_out_io_usb_dn_tx = dio_out[DioUsbdevUsbDn];
  assign manual_oe_io_usb_dn_tx = 1'b1;
  assign dio_in[DioUsbdevUsbDn] = manual_in_io_usb_dn_rx;
  // DioUsbdevUsbDp
  assign manual_attr_io_usb_dp_tx = '0;
  assign manual_out_io_usb_dp_tx = dio_out[DioUsbdevUsbDp];
  assign manual_oe_io_usb_dp_tx = 1'b1;
  assign dio_in[DioUsbdevUsbDp] = manual_in_io_usb_dp_rx;

  assign manual_attr_io_usb_oe_n = '0;
  assign manual_out_io_usb_oe_n = ~dio_oe[DioUsbdevUsbDp];
  assign manual_oe_io_usb_oe_n = 1'b1;

  // DioUsbdevD
  assign manual_attr_io_usb_d_rx = '0;
  assign usb_rx_d = manual_in_io_usb_d_rx;

  // Pull-up / soft connect pin
  assign manual_attr_io_usb_connect = '0;
  assign manual_out_io_usb_connect = usb_dp_pullup_en;
  assign manual_oe_io_usb_connect = 1'b1;

  // Set SPD to full-speed
  assign manual_attr_io_usb_speed = '0;
  assign manual_out_io_usb_speed = 1'b1;
  assign manual_oe_io_usb_speed = 1'b1;

  // TUSB1106 low-power mode
  assign manual_attr_io_usb_suspend = '0;
  assign manual_out_io_usb_suspend = !usb_rx_enable;
  assign manual_oe_io_usb_suspend = 1'b1;

  logic unused_usb_sigs;
  assign unused_usb_sigs = ^{
    usb_dn_pullup_en,
    usb_tx_d,
    usb_tx_se0,
    manual_in_io_usb_connect,
    manual_in_io_usb_oe_n,
    manual_in_io_usb_speed,
    manual_in_io_usb_suspend,
    // DP and DN are broken out into multiple unidirectional pins
    dio_oe[DioUsbdevUsbDp],
    dio_oe[DioUsbdevUsbDn],
    dio_attr[DioUsbdevUsbDp],
    dio_attr[DioUsbdevUsbDn]
  };

  % endif
% endif


###################################################################
## AST For all targets                                           ##
###################################################################

  //////////////////////////////////
  // AST - Common for all targets //
  //////////////////////////////////

  // pwrmgr interface
  pwrmgr_pkg::pwr_ast_req_t base_ast_pwr;
  pwrmgr_pkg::pwr_ast_rsp_t ast_base_pwr;
% if top["name"] == "darjeeling":
  pwrmgr_pkg::pwr_boot_status_t pwrmgr_boot_status;
% endif

  // assorted ast status
  ast_pkg::ast_pwst_t ast_pwst;
% if top["name"] != "darjeeling":
  ast_pkg::ast_pwst_t ast_pwst_h;
% endif

  // TLUL interface
  tlul_pkg::tl_h2d_t base_ast_bus;
  tlul_pkg::tl_d2h_t ast_base_bus;

  // synchronization clocks / rests
  clkmgr_pkg::clkmgr_out_t clkmgr_aon_clocks;
  rstmgr_pkg::rstmgr_out_t rstmgr_aon_resets;

  // external clock
  logic ext_clk;

  // monitored clock
  logic sck_monitor;

  // observe interface
% if top["name"] != "darjeeling":
  logic [7:0] fla_obs;
% endif
  logic [7:0] otp_obs;
  ast_pkg::ast_obs_ctrl_t obs_ctrl;

  // otp power sequence
  otp_ctrl_pkg::otp_ast_req_t otp_ctrl_otp_ast_pwr_seq;
  otp_ctrl_pkg::otp_ast_rsp_t otp_ctrl_otp_ast_pwr_seq_h;

% if top["name"] != "darjeeling":
  logic usb_ref_pulse;
  logic usb_ref_val;
% endif

  // entropy source interface
  // The entropy source pacakge definition should eventually be moved to es
% if top["name"] == "darjeeling":
  entropy_src_pkg::entropy_src_hw_if_req_t entropy_src_hw_if_req;
  entropy_src_pkg::entropy_src_hw_if_rsp_t entropy_src_hw_if_rsp;
% else:
  entropy_src_pkg::entropy_src_rng_req_t es_rng_req;
  entropy_src_pkg::entropy_src_rng_rsp_t es_rng_rsp;
  logic es_rng_fips;

  // adc
  ast_pkg::adc_ast_req_t adc_req;
  ast_pkg::adc_ast_rsp_t adc_rsp;

  // Debug connections
  logic [ast_pkg::Ast2PadOutWidth-1:0] ast2pinmux;
  logic [ast_pkg::Pad2AstInWidth-1:0] pad2ast;
% endif

  // entropy distribution network
  edn_pkg::edn_req_t ast_edn_edn_req;
  edn_pkg::edn_rsp_t ast_edn_edn_rsp;

  // alerts interface
  ast_pkg::ast_alert_rsp_t ast_alert_rsp;
  ast_pkg::ast_alert_req_t ast_alert_req;

  % if top["name"] != "darjeeling":
  // Flash connections
  prim_mubi_pkg::mubi4_t flash_bist_enable;
  logic flash_power_down_h;
  logic flash_power_ready_h;
  % endif

  // clock bypass req/ack
  prim_mubi_pkg::mubi4_t io_clk_byp_req;
  prim_mubi_pkg::mubi4_t io_clk_byp_ack;
  prim_mubi_pkg::mubi4_t all_clk_byp_req;
  prim_mubi_pkg::mubi4_t all_clk_byp_ack;
  prim_mubi_pkg::mubi4_t hi_speed_sel;
  prim_mubi_pkg::mubi4_t div_step_down_req;

  // DFT connections
  logic scan_en;
  lc_ctrl_pkg::lc_tx_t lc_dft_en;
  pinmux_pkg::dft_strap_test_req_t dft_strap_test;

  // Jitter enable
  prim_mubi_pkg::mubi4_t jen;

  // reset domain connections
  import rstmgr_pkg::PowerDomains;
  import rstmgr_pkg::DomainAonSel;
  import rstmgr_pkg::Domain0Sel;

  // Memory configuration connections
  ast_pkg::spm_rm_t ast_ram_1p_cfg;
  ast_pkg::spm_rm_t ast_rf_cfg;
  ast_pkg::spm_rm_t ast_rom_cfg;
  ast_pkg::dpm_rm_t ast_ram_2p_fcfg;
  ast_pkg::dpm_rm_t ast_ram_2p_lcfg;

  // conversion from ast structure to memory centric structures
  prim_ram_1p_pkg::ram_1p_cfg_t ram_1p_cfg;
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

% if top["name"] == "darjeeling":
  logic unused_usb_ram_2p_cfg;
  assign unused_usb_ram_2p_cfg = ^{ast_ram_2p_fcfg.marg_en_a,
                                   ast_ram_2p_fcfg.marg_a,
                                   ast_ram_2p_fcfg.marg_en_b,
                                   ast_ram_2p_fcfg.marg_b};
% else:
  // this maps as follows:
  // assign usb_ram_2p_cfg = {10'h000, ram_2p_cfg_i.a_ram_fcfg, ram_2p_cfg_i.b_ram_fcfg};
  prim_ram_2p_pkg::ram_2p_cfg_t usb_ram_2p_cfg;
  assign usb_ram_2p_cfg = '{
    a_ram_lcfg: '{
                   cfg_en: ast_ram_2p_fcfg.marg_en_a,
                   cfg:    ast_ram_2p_fcfg.marg_a
                 },
    b_ram_lcfg: '{
                   cfg_en: ast_ram_2p_fcfg.marg_en_b,
                   cfg:    ast_ram_2p_fcfg.marg_b
                 },
    default: '0
  };
% endif

  // this maps as follows:
  // assign spi_ram_2p_cfg = {10'h000, ram_2p_cfg_i.a_ram_lcfg, ram_2p_cfg_i.b_ram_lcfg};
  prim_ram_2p_pkg::ram_2p_cfg_t spi_ram_2p_cfg;
  assign spi_ram_2p_cfg = '{
    a_ram_lcfg: '{
                   cfg_en: ast_ram_2p_lcfg.marg_en_a,
                   cfg:    ast_ram_2p_lcfg.marg_a
                 },
    b_ram_lcfg: '{
                   cfg_en: ast_ram_2p_lcfg.marg_en_b,
                   cfg:    ast_ram_2p_lcfg.marg_b
                 },
    default: '0
  };

  prim_rom_pkg::rom_cfg_t rom_cfg;
  assign rom_cfg = '{
    cfg_en: ast_rom_cfg.marg_en,
    cfg: ast_rom_cfg.marg
  };


  //////////////////////////////////
  // AST - Custom for targets     //
  //////////////////////////////////

<%
  ast = [m for m in top["module"] if m["name"] == "ast"]
  assert(len(ast) == 1)
  ast = ast[0]
%>\

  assign ast_base_pwr.main_pok = ast_pwst.main_pok;

  logic [rstmgr_pkg::PowerDomains-1:0] por_n;
  assign por_n = {ast_pwst.main_pok, ast_pwst.aon_pok};

% if target["name"] == "asic":

  // external clock comes in at a fixed position
% if top["name"] != "darjeeling":
  assign ext_clk = mio_in_raw[MioPadIoc6];

  logic [ast_pkg::UsbCalibWidth-1:0] usb_io_pu_cal;
  logic usb_diff_rx_obs;

  assign pad2ast = `PAD2AST_WIRES ;

% else:
  assign ext_clk = mio_in_raw[MioPadMio11];

  wire unused_t0, unused_t1;
  assign unused_t0 = 1'b0;
  assign unused_t1 = 1'b0;
% endif

  // AST does not use all clocks / resets forwarded to it
  logic unused_slow_clk_en;
  assign unused_slow_clk_en = base_ast_pwr.slow_clk_en;

  logic unused_pwr_clamp;
  assign unused_pwr_clamp = base_ast_pwr.pwr_clamp;

% else:
  // TODO: Hook this up when FPGA pads are updated
  assign ext_clk = '0;
  assign pad2ast = '0;

  logic clk_main, clk_usb_48mhz, clk_aon, rst_n, srst_n;
  clkgen_xil7series # (
    .AddClkBuf(0)
  ) clkgen (
    .clk_i(manual_in_io_clk),
    .rst_ni(manual_in_por_n),
    .srst_ni(srst_n),
    .clk_main_o(clk_main),
    .clk_48MHz_o(clk_usb_48mhz),
    .clk_aon_o(clk_aon),
    .rst_no(rst_n)
  );

  logic [31:0] fpga_info;
  usr_access_xil7series u_info (
    .info_o(fpga_info)
  );

  ast_pkg::clks_osc_byp_t clks_osc_byp;
  assign clks_osc_byp = '{
    usb: clk_usb_48mhz,
    sys: clk_main,
    io:  clk_main,
    aon: clk_aon
  };

% endif

  prim_mubi_pkg::mubi4_t ast_init_done;

  ast #(
    .EntropyStreams(ast_pkg::EntropyStreams),
    .AdcChannels(ast_pkg::AdcChannels),
    .AdcDataWidth(ast_pkg::AdcDataWidth),
    .UsbCalibWidth(ast_pkg::UsbCalibWidth),
    .Ast2PadOutWidth(ast_pkg::Ast2PadOutWidth),
    .Pad2AstInWidth(ast_pkg::Pad2AstInWidth)
  ) u_ast (
% if target["name"] == "asic":
    // external POR
    .por_ni                ( manual_in_por_n ),

    // USB IO Pull-up Calibration Setting
% if top["name"] == "darjeeling":
    .usb_io_pu_cal_o       ( ),
% else:
    .usb_io_pu_cal_o       ( usb_io_pu_cal ),
% endif

    // adc
% if top["name"] == "earlgrey":
    .adc_a0_ai             ( CC1 ),
    .adc_a1_ai             ( CC2 ),
% else:
    .adc_a0_ai             ( '0 ),
    .adc_a1_ai             ( '0 ),
% endif

    // Direct short to PAD
% if top["name"] == "darjeeling":
    .ast2pad_t0_ao         ( unused_t0 ),
    .ast2pad_t1_ao         ( unused_t1 ),
% else:
    .ast2pad_t0_ao         ( IOA2 ),
    .ast2pad_t1_ao         ( IOA3 ),
% endif
% else:
    // external POR
    .por_ni                ( rst_n ),

    // USB IO Pull-up Calibration Setting
    .usb_io_pu_cal_o       ( ),

    // clocks' oschillator bypass for FPGA
    .clk_osc_byp_i         ( clks_osc_byp ),

    // adc
    .adc_a0_ai             ( '0 ),
    .adc_a1_ai             ( '0 ),

    // Direct short to PAD
    .ast2pad_t0_ao         (  ),
    .ast2pad_t1_ao         (  ),

% endif
    // clocks and resets supplied for detection
    .sns_clks_i            ( clkmgr_aon_clocks    ),
    .sns_rsts_i            ( rstmgr_aon_resets    ),
    .sns_spi_ext_clk_i     ( sck_monitor          ),
    // tlul
    .tl_i                  ( base_ast_bus ),
    .tl_o                  ( ast_base_bus ),
    // init done indication
    .ast_init_done_o       ( ast_init_done ),
    // buffered clocks & resets
    % for port, clk in ast["clock_connections"].items():
    .${port} (${clk}),
    % endfor
    % for port, reset in ast["reset_connections"].items():
    .${port} (${lib.get_reset_path(top, reset)}),
    % endfor
    .clk_ast_ext_i         ( ext_clk ),

    // pok test for FPGA
    .vcc_supp_i            ( 1'b1 ),
    .vcaon_supp_i          ( 1'b1 ),
    .vcmain_supp_i         ( 1'b1 ),
    .vioa_supp_i           ( 1'b1 ),
    .viob_supp_i           ( 1'b1 ),
    // pok
    .ast_pwst_o            ( ast_pwst ),
% if top["name"] == "darjeeling":
    .ast_pwst_h_o          ( ),
% else:
    .ast_pwst_h_o          ( ast_pwst_h ),
% endif
    // main regulator
    .main_env_iso_en_i     ( base_ast_pwr.pwr_clamp_env ),
    .main_pd_ni            ( base_ast_pwr.main_pd_n ),
    // pdm control (flash)/otp
% if top["name"] == "darjeeling":
    .flash_power_down_h_o  ( ),
    .flash_power_ready_h_o ( ),
% else:
    .flash_power_down_h_o  ( flash_power_down_h ),
    .flash_power_ready_h_o ( flash_power_ready_h ),
% endif
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
    .clk_src_io_48m_o      ( div_step_down_req ),
    // usb source clock
% if top["name"] == "darjeeling":
    .usb_ref_pulse_i       ( '0 ),
    .usb_ref_val_i         ( '0 ),
% else:
    .usb_ref_pulse_i       ( usb_ref_pulse ),
    .usb_ref_val_i         ( usb_ref_val ),
% endif
    .clk_src_usb_en_i      ( base_ast_pwr.usb_clk_en ),
    .clk_src_usb_o         ( ast_base_clks.clk_usb ),
    .clk_src_usb_val_o     ( ast_base_pwr.usb_clk_val ),
% if top["name"] == "darjeeling":
    // entropy_src
    .es_req_i              ( entropy_src_hw_if_req ),
    .es_rsp_o              ( entropy_src_hw_if_rsp ),
    // adc
    .adc_pd_i              ( '0 ),
    .adc_chnsel_i          ( '0 ),
    .adc_d_o               (    ),
    .adc_d_val_o           (    ),
% else:
    // adc
    .adc_pd_i              ( adc_req.pd ),
    .adc_chnsel_i          ( adc_req.channel_sel ),
    .adc_d_o               ( adc_rsp.data ),
    .adc_d_val_o           ( adc_rsp.data_valid ),
    // rng
    .rng_en_i              ( es_rng_req.rng_enable ),
    .rng_fips_i            ( es_rng_fips ),
    .rng_val_o             ( es_rng_rsp.rng_valid ),
    .rng_b_o               ( es_rng_rsp.rng_b ),
% endif
    // entropy
    .entropy_rsp_i         ( ast_edn_edn_rsp ),
    .entropy_req_o         ( ast_edn_edn_req ),
    // alerts
    .alert_rsp_i           ( ast_alert_rsp  ),
    .alert_req_o           ( ast_alert_req  ),
    // dft
    .dft_strap_test_i      ( dft_strap_test   ),
    .lc_dft_en_i           ( lc_dft_en        ),
% if top["name"] == "darjeeling":
    .fla_obs_i             ( '0 ),
    .usb_obs_i             ( '0 ),
% else:
    .fla_obs_i             ( fla_obs ),
    .usb_obs_i             ( usb_diff_rx_obs ),
% endif
    .otp_obs_i             ( otp_obs ),
    .otm_obs_i             ( '0 ),
    .obs_ctrl_o            ( obs_ctrl ),
    // pinmux related
% if top["name"] == "darjeeling":
    .padmux2ast_i          ( '0         ),
    .ast2padmux_o          (            ),
% else:
    .padmux2ast_i          ( pad2ast    ),
    .ast2padmux_o          ( ast2pinmux ),
% endif
    .ext_freq_is_96m_i     ( hi_speed_sel ),
    .all_clk_byp_req_i     ( all_clk_byp_req  ),
    .all_clk_byp_ack_o     ( all_clk_byp_ack  ),
    .io_clk_byp_req_i      ( io_clk_byp_req   ),
    .io_clk_byp_ack_o      ( io_clk_byp_ack   ),
% if top["name"] == "darjeeling":
    .flash_bist_en_o       ( ),
% else:
    .flash_bist_en_o       ( flash_bist_enable ),
% endif
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


% if top["name"] in ["darjeeling"]:
  //////////////////
  // TAP Instance //
  //////////////////

  tlul_pkg::tl_h2d_t dmi_h2d;
  tlul_pkg::tl_d2h_t dmi_d2h;
  jtag_pkg::jtag_req_t jtag_req;
  jtag_pkg::jtag_rsp_t jtag_rsp;

  assign jtag_req.tck    = manual_in_jtag_tck;
  assign jtag_req.tms    = manual_in_jtag_tms;
  assign jtag_req.trst_n = manual_in_jtag_trst_n;
  assign jtag_req.tdi    = manual_in_jtag_tdi;

  assign manual_out_jtag_tck     = '0;
  assign manual_out_jtag_tms     = '0;
  assign manual_out_jtag_trst_n  = '0;
  assign manual_out_jtag_tdi     = '0;
  assign manual_oe_jtag_tck      = '0;
  assign manual_oe_jtag_tms      = '0;
  assign manual_oe_jtag_trst_n   = '0;
  assign manual_oe_jtag_tdi      = '0;
  assign manual_attr_jtag_tck    = '0;
  assign manual_attr_jtag_tms    = '0;
  assign manual_attr_jtag_trst_n = '0;
  assign manual_attr_jtag_tdi    = '0;

  assign manual_out_jtag_tdo     = jtag_rsp.tdo;
  assign manual_oe_jtag_tdo      = jtag_rsp.tdo_oe;
  assign manual_attr_jtag_tdo    = '0;

  logic unused_manual_jtag_sigs;
  assign unused_manual_jtag_sigs = ^{
    manual_in_jtag_tdo
  };

  tlul_jtag_dtm #(
    .IdcodeValue(jtag_id_pkg::LC_DM_COMBINED_JTAG_IDCODE),
    // Notes:
    // - one RV_DM instance uses 9bits
    // - our crossbar tooling expects individual IPs to be spaced apart by 12bits at the moment
    // - the DMI address shifted through jtag is a word address and hence 2bits smaller than this
    // - setting this to 18bits effectively gives us 2^6 = 64 addressable 12bit ranges
    .NumDmiByteAbits(18)
  ) u_tlul_jtag_dtm (
    .clk_i      (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni     (rstmgr_aon_resets.rst_sys_n[rstmgr_pkg::Domain0Sel]),
    .jtag_i     (jtag_req),
    .jtag_o     (jtag_rsp),
    .scan_rst_ni(scan_rst_n),
    .scanmode_i (scanmode),
    .tl_h2d_o   (dmi_h2d),
    .tl_d2h_i   (dmi_d2h)
  );

  ////////////////
  // CTN M-to-1 //
  ////////////////

  tlul_pkg::tl_h2d_t ctn_tl_h2d[2];
  tlul_pkg::tl_d2h_t ctn_tl_d2h[2];

  tlul_pkg::tl_h2d_t ctn_sm1_to_s1n_tl_h2d;
  tlul_pkg::tl_d2h_t ctn_sm1_to_s1n_tl_d2h;

  tlul_socket_m1 #(
    .M         (2),
    .HReqPass  ({2{1'b1}}),
    .HRspPass  ({2{1'b1}}),
    .HReqDepth ({2{4'd0}}),
    .HRspDepth ({2{4'd0}}),
    .DReqPass  (1'b1),
    .DRspPass  (1'b1),
    .DReqDepth (4'd0),
    .DRspDepth (4'd0)
  ) u_ctn_sm1 (
    .clk_i  (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni (rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::Domain0Sel]),
    .tl_h_i (ctn_tl_h2d),
    .tl_h_o (ctn_tl_d2h),
    .tl_d_o (ctn_sm1_to_s1n_tl_h2d),
    .tl_d_i (ctn_sm1_to_s1n_tl_d2h)
  );

  ////////////////////////////////////////////
  // CTN Address decoding and SRAM Instance //
  ////////////////////////////////////////////

  localparam int CtnSramDw = top_pkg::TL_DW + tlul_pkg::DataIntgWidth;

  tlul_pkg::tl_h2d_t ctn_s1n_tl_h2d[1];
  tlul_pkg::tl_d2h_t ctn_s1n_tl_d2h[1];

  // Steering signal for address decoding.
  logic [0:0] ctn_dev_sel_s1n;

  logic sram_req, sram_we, sram_rvalid;
  logic [top_pkg::CtnSramAw-1:0] sram_addr;
  logic [CtnSramDw-1:0] sram_wdata, sram_wmask, sram_rdata;

  // Steering of requests.
  // Addresses leaving the RoT through the CTN port are mapped to an internal 1G address space of
  // 0x4000_0000 - 0x8000_0000. However, the CTN RAM only covers a 1MB region inside that space,
  // and hence additional decoding and steering logic is needed here.
  // TODO: this should in the future be replaced by an automatically generated crossbar.
  always_comb begin
    // Default steering to generate error response if address is not within the range
    ctn_dev_sel_s1n = 1'b1;
    // Steering to CTN SRAM.
    if ((ctn_sm1_to_s1n_tl_h2d.a_address & ~(TOP_DARJEELING_RAM_CTN_SIZE_BYTES-1)) ==
        TOP_DARJEELING_RAM_CTN_BASE_ADDR) begin
      ctn_dev_sel_s1n = 1'd0;
    end
  end

  tlul_socket_1n #(
    .HReqDepth (4'h0),
    .HRspDepth (4'h0),
    .DReqDepth (8'h0),
    .DRspDepth (8'h0),
    .N         (1)
  ) u_ctn_s1n (
    .clk_i        (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni       (rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::Domain0Sel]),
    .tl_h_i       (ctn_sm1_to_s1n_tl_h2d),
    .tl_h_o       (ctn_sm1_to_s1n_tl_d2h),
    .tl_d_o       (ctn_s1n_tl_h2d),
    .tl_d_i       (ctn_s1n_tl_d2h),
    .dev_select_i (ctn_dev_sel_s1n)
  );

  tlul_adapter_sram #(
    .SramAw(top_pkg::CtnSramAw),
    .SramDw(CtnSramDw - tlul_pkg::DataIntgWidth),
    .Outstanding(2),
    .ByteAccess(1),
    .CmdIntgCheck(1),
    .EnableRspIntgGen(1),
    .EnableDataIntgGen(0),
    .EnableDataIntgPt(1),
    .SecFifoPtr      (0)
  ) u_tlul_adapter_sram_ctn (
    .clk_i       (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni      (rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::Domain0Sel]),
    .tl_i        (ctn_s1n_tl_h2d[0]),
    .tl_o        (ctn_s1n_tl_d2h[0]),
    // Ifetch is explicitly allowed
    .en_ifetch_i (prim_mubi_pkg::MuBi4True),
    .req_o       (sram_req),
    .req_type_o  (),
    // SRAM can always accept a request.
    .gnt_i       (1'b1),
    .we_o        (sram_we),
    .addr_o      (sram_addr),
    .wdata_o     (sram_wdata),
    .wmask_o     (sram_wmask),
    .intg_error_o(),
    .rdata_i     (sram_rdata),
    .rvalid_i    (sram_rvalid),
    .rerror_i    ('0)
  );

  prim_ram_1p_adv #(
    .Depth(top_pkg::CtnSramDepth),
    .Width(CtnSramDw),
    .DataBitsPerMask(CtnSramDw),
    .EnableECC(0),
    .EnableParity(0),
    .EnableInputPipeline(1),
    .EnableOutputPipeline(1)
  ) u_prim_ram_1p_adv_ctn (
    .clk_i    (clkmgr_aon_clocks.clk_main_infra),
    .rst_ni   (rstmgr_aon_resets.rst_lc_n[rstmgr_pkg::Domain0Sel]),
    .req_i    (sram_req),
    .write_i  (sram_we),
    .addr_i   (sram_addr),
    .wdata_i  (sram_wdata),
    .wmask_i  (sram_wmask),
    .rdata_o  (sram_rdata),
    .rvalid_o (sram_rvalid),
    // No error detection is enabled inside SRAM.
    // Bus ECC is checked at the consumer side.
    .rerror_o (),
    .cfg_i    (ram_1p_cfg)
  );
%endif
###################################################################
## ASIC                                                          ##
###################################################################

% if target["name"] == "asic":

  //////////////////////////////////
  // Manual Pad / Signal Tie-offs //
  //////////////////////////////////

  assign manual_out_por_n = 1'b0;
  assign manual_oe_por_n = 1'b0;

  % if top["name"] != "darjeeling":
  assign manual_out_cc1 = 1'b0;
  assign manual_oe_cc1 = 1'b0;
  assign manual_out_cc2 = 1'b0;
  assign manual_oe_cc2 = 1'b0;
  assign manual_out_ast_misc = 1'b0;
  assign manual_oe_ast_misc = 1'b0;
  always_comb begin
    // constantly enable pull-down
    manual_attr_ast_misc = '0;
    manual_attr_ast_misc.pull_select = 1'b0;
    manual_attr_ast_misc.pull_en = 1'b1;
  end
  assign manual_out_flash_test_mode0 = 1'b0;
  assign manual_oe_flash_test_mode0 = 1'b0;
  assign manual_out_flash_test_mode1 = 1'b0;
  assign manual_oe_flash_test_mode1 = 1'b0;
  assign manual_out_flash_test_volt = 1'b0;
  assign manual_oe_flash_test_volt = 1'b0;
  % endif

  assign manual_out_otp_ext_volt = 1'b0;
  assign manual_oe_otp_ext_volt = 1'b0;

  // These pad attributes currently tied off permanently (these are all input-only pads).
  assign manual_attr_por_n = '0;
  % if top["name"] != "darjeeling":
  assign manual_attr_cc1 = '0;
  assign manual_attr_cc2 = '0;
  assign manual_attr_flash_test_mode0 = '0;
  assign manual_attr_flash_test_mode1 = '0;
  assign manual_attr_flash_test_volt = '0;
  % endif
  assign manual_attr_otp_ext_volt = '0;

  logic unused_manual_sigs;
  assign unused_manual_sigs = ^{
    % if top["name"] != "darjeeling":
    manual_in_cc2,
    manual_in_cc1,
    manual_in_flash_test_volt,
    manual_in_flash_test_mode0,
    manual_in_flash_test_mode1,
    % endif
    manual_in_otp_ext_volt
  };

% if "usbdev" in {module["type"] for module in top["module"]}:
  ///////////////////////////////
  // Differential USB Receiver //
  ///////////////////////////////

  // TODO: generalize this USB mux code and align with other tops.

  // Connect the D+ pad
  // Note that we use two pads in parallel for the D+ channel to meet electrical specifications.
  assign dio_in[DioUsbdevUsbDp] = manual_in_usb_p;
  assign manual_out_usb_p = dio_out[DioUsbdevUsbDp];
  assign manual_oe_usb_p = dio_oe[DioUsbdevUsbDp];
  assign manual_attr_usb_p = dio_attr[DioUsbdevUsbDp];

  // Connect the D- pads
  // Note that we use two pads in parallel for the D- channel to meet electrical specifications.
  assign dio_in[DioUsbdevUsbDn] = manual_in_usb_n;
  assign manual_out_usb_n = dio_out[DioUsbdevUsbDn];
  assign manual_oe_usb_n = dio_oe[DioUsbdevUsbDn];
  assign manual_attr_usb_n = dio_attr[DioUsbdevUsbDn];

  logic usb_rx_d;

  // Pullups and differential receiver enable
  logic usb_dp_pullup_en, usb_dn_pullup_en;
  logic usb_rx_enable;

  prim_usb_diff_rx #(
    .CalibW(ast_pkg::UsbCalibWidth)
  ) u_prim_usb_diff_rx (
    .input_pi          ( USB_P                 ),
    .input_ni          ( USB_N                 ),
    .input_en_i        ( usb_rx_enable         ),
    .core_pok_h_i      ( ast_pwst_h.aon_pok    ),
    .pullup_p_en_i     ( usb_dp_pullup_en      ),
    .pullup_n_en_i     ( usb_dn_pullup_en      ),
    .calibration_i     ( usb_io_pu_cal         ),
    .usb_diff_rx_obs_o ( usb_diff_rx_obs       ),
    .input_o           ( usb_rx_d              )
  );
% endif

% if top["name"] == "darjeeling":
  soc_proxy_pkg::soc_alert_req_t [soc_proxy_pkg::NumFatalExternalAlerts-1:0] soc_fatal_alert_req;
  soc_proxy_pkg::soc_alert_req_t [soc_proxy_pkg::NumRecovExternalAlerts-1:0] soc_recov_alert_req;
  assign soc_fatal_alert_req =
      {soc_proxy_pkg::NumFatalExternalAlerts{soc_proxy_pkg::SOC_ALERT_REQ_DEFAULT}};
  assign soc_recov_alert_req =
      {soc_proxy_pkg::NumRecovExternalAlerts{soc_proxy_pkg::SOC_ALERT_REQ_DEFAULT}};
  // The logic below is a is a loopback path.  It listens to the internal reset request generated by
  // the power manager and translates this request into a stretched pulse (modeled by the counter).
  // The stretched pulse is fed back to top_darjeeling as external async SoC reset request.
  // TODO(#22710): This should be moved to the DV environment, and we need to extend the code to be
  // able to asynchronously assert the external reset pin without any internal request.
  logic  internal_request_d, internal_request_q;
  logic  external_reset, count_up;
  logic  [3:0] count;
  assign internal_request_d = pwrmgr_boot_status.light_reset_req;
  always_ff @(posedge ast_base_clks.clk_aon or negedge por_n[0]) begin
    if (!por_n[0]) begin
      external_reset     <= 1'b0;
      internal_request_q <= 1'b0;
      count_up           <= '0;
      count              <= '0;
    end else begin
      internal_request_q <= internal_request_d;
      if (!internal_request_q && internal_request_d) begin
        count_up       <= 1'b1;
        external_reset <= 1;
      end else if (count == 'd8) begin
        count_up       <= 0;
        external_reset <= 0;
        count          <= '0;
      end else if (count_up) begin
        count <= count + 1;
      end
    end
  end

% endif
  //////////////////////
  // Top-level design //
  //////////////////////
  top_${top["name"]} #(
% if target["name"] != "asic":
    .PinmuxAonTargetCfg(PinmuxTargetCfg)
% else:
    .PinmuxAonTargetCfg(PinmuxTargetCfg),
    .SecAesAllowForcingMasks(1'b1),
  % if lib.num_rom_ctrl(top["module"]) > 1:
    .SecRomCtrl0DisableScrambling(SecRomCtrl0DisableScrambling),
    .SecRomCtrl1DisableScrambling(SecRomCtrl1DisableScrambling)
  % else:
    .SecRomCtrl0DisableScrambling(SecRomCtrl0DisableScrambling)
  % endif
% endif
  ) top_${top["name"]} (
    // ast connections
    .por_n_i                           ( por_n                      ),
    .clk_main_i                        ( ast_base_clks.clk_sys      ),
    .clk_io_i                          ( ast_base_clks.clk_io       ),
    .clk_usb_i                         ( ast_base_clks.clk_usb      ),
    .clk_aon_i                         ( ast_base_clks.clk_aon      ),
    .clks_ast_o                        ( clkmgr_aon_clocks          ),
    .clk_main_jitter_en_o              ( jen                        ),
    .rsts_ast_o                        ( rstmgr_aon_resets          ),
    .sck_monitor_o                     ( sck_monitor                ),
    .pwrmgr_ast_req_o                  ( base_ast_pwr               ),
    .pwrmgr_ast_rsp_i                  ( ast_base_pwr               ),
    .sensor_ctrl_ast_alert_req_i       ( ast_alert_req              ),
    .sensor_ctrl_ast_alert_rsp_o       ( ast_alert_rsp              ),
    .sensor_ctrl_ast_status_i          ( ast_pwst.io_pok            ),
% if top["name"] != "darjeeling":
    .usb_dp_pullup_en_o                ( usb_dp_pullup_en           ),
    .usb_dn_pullup_en_o                ( usb_dn_pullup_en           ),
    .usbdev_usb_rx_d_i                 ( usb_rx_d                   ),
    .usbdev_usb_tx_d_o                 (                            ),
    .usbdev_usb_tx_se0_o               (                            ),
    .usbdev_usb_tx_use_d_se0_o         (                            ),
    .usbdev_usb_rx_enable_o            ( usb_rx_enable              ),
    .usbdev_usb_ref_val_o              ( usb_ref_val                ),
    .usbdev_usb_ref_pulse_o            ( usb_ref_pulse              ),
    .adc_req_o                         ( adc_req                    ),
    .adc_rsp_i                         ( adc_rsp                    ),
% endif
    .ast_edn_req_i                     ( ast_edn_edn_req            ),
    .ast_edn_rsp_o                     ( ast_edn_edn_rsp            ),
    .ast_tl_req_o                      ( base_ast_bus               ),
    .ast_tl_rsp_i                      ( ast_base_bus               ),
    .obs_ctrl_i                        ( obs_ctrl                   ),
    .otp_ctrl_otp_ast_pwr_seq_o        ( otp_ctrl_otp_ast_pwr_seq   ),
    .otp_ctrl_otp_ast_pwr_seq_h_i      ( otp_ctrl_otp_ast_pwr_seq_h ),
    .otp_obs_o                         ( otp_obs                    ),
% if top["name"] == "darjeeling":
    .ctn_tl_h2d_o                      ( ctn_tl_h2d[0]              ),
    .ctn_tl_d2h_i                      ( ctn_tl_d2h[0]              ),
    .soc_gpi_async_o                   (                            ),
    .soc_gpo_async_i                   ( '0                         ),
    .dma_sys_req_o                     (                            ),
    .dma_sys_rsp_i                     ( '0                         ),
    .dma_ctn_tl_h2d_o                  ( ctn_tl_h2d[1]              ),
    .dma_ctn_tl_d2h_i                  ( ctn_tl_d2h[1]              ),
    .mbx_tl_req_i                      ( tlul_pkg::TL_H2D_DEFAULT   ),
    .mbx_tl_rsp_o                      (                            ),
    .pwrmgr_boot_status_o              ( pwrmgr_boot_status         ),
    .soc_fatal_alert_req_i             ( soc_fatal_alert_req        ),
    .soc_fatal_alert_rsp_o             (                            ),
    .soc_recov_alert_req_i             ( soc_recov_alert_req        ),
    .soc_recov_alert_rsp_o             (                            ),
    .soc_intr_async_i                  ( '0                         ),
    .soc_wkup_async_i                  ( 1'b0                       ),
    // TODO(#22710): this should come from modeled SoC (e.g., from TB).
    .soc_rst_req_async_i               ( external_reset             ),
    .soc_lsio_trigger_i                ( '0                         ),
    .entropy_src_hw_if_req_o           ( entropy_src_hw_if_req      ),
    .entropy_src_hw_if_rsp_i           ( entropy_src_hw_if_rsp      ),
    .mbx0_doe_intr_en_o                (                            ),
    .mbx0_doe_intr_o                   (                            ),
    .mbx0_doe_intr_support_o           (                            ),
    .mbx0_doe_async_msg_support_o      (                            ),
    .mbx1_doe_intr_en_o                (                            ),
    .mbx1_doe_intr_o                   (                            ),
    .mbx1_doe_intr_support_o           (                            ),
    .mbx1_doe_async_msg_support_o      (                            ),
    .mbx2_doe_intr_en_o                (                            ),
    .mbx2_doe_intr_o                   (                            ),
    .mbx2_doe_intr_support_o           (                            ),
    .mbx2_doe_async_msg_support_o      (                            ),
    .mbx3_doe_intr_en_o                (                            ),
    .mbx3_doe_intr_o                   (                            ),
    .mbx3_doe_intr_support_o           (                            ),
    .mbx3_doe_async_msg_support_o      (                            ),
    .mbx4_doe_intr_en_o                (                            ),
    .mbx4_doe_intr_o                   (                            ),
    .mbx4_doe_intr_support_o           (                            ),
    .mbx4_doe_async_msg_support_o      (                            ),
    .mbx5_doe_intr_en_o                (                            ),
    .mbx5_doe_intr_o                   (                            ),
    .mbx5_doe_intr_support_o           (                            ),
    .mbx5_doe_async_msg_support_o      (                            ),
    .mbx6_doe_intr_en_o                (                            ),
    .mbx6_doe_intr_o                   (                            ),
    .mbx6_doe_intr_support_o           (                            ),
    .mbx6_doe_async_msg_support_o      (                            ),
    .mbx_jtag_doe_intr_en_o            (                            ),
    .mbx_jtag_doe_intr_o               (                            ),
    .mbx_jtag_doe_intr_support_o       (                            ),
    .mbx_jtag_doe_async_msg_support_o  (                            ),
    .mbx_pcie0_doe_intr_en_o           (                            ),
    .mbx_pcie0_doe_intr_o              (                            ),
    .mbx_pcie0_doe_intr_support_o      (                            ),
    .mbx_pcie0_doe_async_msg_support_o (                            ),
    .mbx_pcie1_doe_intr_en_o           (                            ),
    .mbx_pcie1_doe_intr_o              (                            ),
    .mbx_pcie1_doe_intr_support_o      (                            ),
    .mbx_pcie1_doe_async_msg_support_o (                            ),
% else:
    .es_rng_req_o                      ( es_rng_req                 ),
    .es_rng_rsp_i                      ( es_rng_rsp                 ),
    .es_rng_fips_o                     ( es_rng_fips                ),
    .flash_bist_enable_i               ( flash_bist_enable          ),
    .flash_power_down_h_i              ( flash_power_down_h         ),
    .flash_power_ready_h_i             ( flash_power_ready_h        ),
    .flash_obs_o                       ( fla_obs                    ),
    // Flash test mode voltages
    .flash_test_mode_a_io              ( {FLASH_TEST_MODE1,
                                          FLASH_TEST_MODE0}         ),
    .flash_test_voltage_h_io           ( FLASH_TEST_VOLT            ),
    .ast2pinmux_i                      ( ast2pinmux                 ),
% endif
    .io_clk_byp_req_o                  ( io_clk_byp_req             ),
    .io_clk_byp_ack_i                  ( io_clk_byp_ack             ),
    .all_clk_byp_req_o                 ( all_clk_byp_req            ),
    .all_clk_byp_ack_i                 ( all_clk_byp_ack            ),
    .hi_speed_sel_o                    ( hi_speed_sel               ),
    .div_step_down_req_i               ( div_step_down_req          ),
    .calib_rdy_i                       ( ast_init_done              ),
    .ast_init_done_i                   ( ast_init_done              ),

    // OTP external voltage
    .otp_ext_voltage_h_io              ( OTP_EXT_VOLT               ),

% if top["name"] in ["darjeeling"]:
    // DMI TL-UL
    .dbg_tl_req_i                      ( dmi_h2d                    ),
    .dbg_tl_rsp_o                      ( dmi_d2h                    ),
    // Quasi-static word address for next_dm register value.
    .rv_dm_next_dm_addr_i              ( '0                         ),
% endif
    // Multiplexed I/O
    .mio_in_i                          ( mio_in                     ),
    .mio_out_o                         ( mio_out                    ),
    .mio_oe_o                          ( mio_oe                     ),

    // Dedicated I/O
    .dio_in_i                          ( dio_in                     ),
    .dio_out_o                         ( dio_out                    ),
    .dio_oe_o                          ( dio_oe                     ),

    // Pad attributes
    .mio_attr_o                        ( mio_attr                   ),
    .dio_attr_o                        ( dio_attr                   ),

    // Memory attributes
    .ram_1p_cfg_i                      ( ram_1p_cfg                 ),
    .spi_ram_2p_cfg_i                  ( spi_ram_2p_cfg             ),
% if top["name"] != "darjeeling":
    .usb_ram_2p_cfg_i                  ( usb_ram_2p_cfg             ),
% endif

    .rom_cfg_i                         ( rom_cfg                    ),

    // DFT signals
    .ast_lc_dft_en_o                   ( lc_dft_en                  ),
% if top["name"] in ["darjeeling"]:
    .ast_lc_hw_debug_en_o              (                            ),
% endif
    .dft_strap_test_o                  ( dft_strap_test             ),
    .dft_hold_tap_sel_i                ( '0                         ),
    .scan_rst_ni                       ( scan_rst_n                 ),
    .scan_en_i                         ( scan_en                    ),
    .scanmode_i                        ( scanmode                   ),

    // FPGA build info
    .fpga_info_i                       ( '0                         )
  );
% endif

###################################################################
## FPGA shared                                                   ##
###################################################################
% if target["name"] in ["cw310", "cw305"]:
  //////////////////
  // PLL for FPGA //
  //////////////////

  assign manual_attr_io_clk = '0;
  assign manual_out_io_clk = 1'b0;
  assign manual_oe_io_clk = 1'b0;
  assign manual_attr_por_n = '0;
  assign manual_out_por_n = 1'b0;
  assign manual_oe_por_n = 1'b0;
  assign manual_attr_por_button_n = '0;
  assign manual_out_por_button_n = 1'b0;
  assign manual_oe_por_button_n = 1'b0;

  % if target["name"] in ["cw305", "cw310"]:
  assign srst_n = manual_in_por_button_n;
  % endif

  % if target["name"] == "cw305":
  // TODO: follow-up later and hardwire all ast connects that do not
  //       exist for this target
  assign otp_obs_o = '0;
  % endif


  //////////////////////
  // Top-level design //
  //////////////////////

  // the rst_ni pin only goes to AST
  // the rest of the logic generates reset based on the 'pok' signal.
  // for verilator purposes, make these two the same.
  prim_mubi_pkg::mubi4_t lc_clk_bypass;   // TODO Tim

// TODO: align this with ASIC version to minimize the duplication.
// Also need to add AST simulation and FPGA emulation models for things like entropy source -
// otherwise Verilator / FPGA will hang.
  top_${top["name"]} #(
% if target["name"] == "cw310":
    .SecAesMasking(1'b1),
    .SecAesSBoxImpl(aes_pkg::SBoxImplDom),
    .SecAesStartTriggerDelay(320),
    .SecAesAllowForcingMasks(1'b1),
    .KmacEnMasking(0),
    .KmacSwKeyMasked(1),
    .SecKmacCmdDelay(320),
    .SecKmacIdleAcceptSwMsg(1'b1),
% if top["name"] == "earlgrey":
    .KeymgrKmacEnMasking(0),
% else:
    .KeymgrDpeKmacEnMasking(0),
% endif
    .CsrngSBoxImpl(aes_pkg::SBoxImplLut),
    .OtbnRegFile(otbn_pkg::RegFileFPGA),
    .SecOtbnMuteUrnd(1'b1),
    .SecOtbnSkipUrndReseedAtStart(1'b1),
    .OtpCtrlMemInitFile(OtpCtrlMemInitFile),
    .RvCoreIbexPipeLine(1),
    .SramCtrlRetAonInstrExec(0),
    % if top["name"] != "darjeeling":
    .UsbdevRcvrWakeTimeUs(10000),
    % endif
  % if lib.num_rom_ctrl(top["module"]) > 1:
    // TODO(opentitan-integrated/issues/251):
    // Enable hashing below once the build infrastructure can
    // load scrambled images on FPGA platforms. The DV can
    // already partially handle it by initializing the 2nd ROM
    // with random data via the backdoor loading interface - it
    // can't load "real" SW images yet since that requires
    // additional build infrastructure.
    .SecRomCtrl1DisableScrambling(1),
  % endif
% elif target["name"] == "cw305":
    .RvCoreIbexPipeLine(0),
    .SecAesMasking(1'b1),
    .SecAesSBoxImpl(aes_pkg::SBoxImplDom),
    .SecAesStartTriggerDelay(320),
    .SecAesAllowForcingMasks(1'b1),
    .SecAesSkipPRNGReseeding(1'b1),
    .UsbdevStub(1'b1),
% else:
    .SecAesMasking(1'b0),
    .SecAesSBoxImpl(aes_pkg::SBoxImplLut),
    .KmacEnMasking(1'b0),
% if top["name"] == "earlgrey":
    .KeymgrKmacEnMasking(0),
% else:
    .KeymgrDpeKmacEnMasking(0),
% endif
    .SecAesStartTriggerDelay(0),
    .SecAesAllowForcingMasks(1'b0),
    .SecAesSkipPRNGReseeding(1'b0),
    .SramCtrlRetAonInstrExec(0),
    .EntropySrcStub(1'b1),
    .CsrngSBoxImpl(aes_pkg::SBoxImplLut),
    .OtbnRegFile(otbn_pkg::RegFileFPGA),
    .OtbnStub(1'b1),
    .OtpCtrlMemInitFile(OtpCtrlMemInitFile),
    .RvCoreIbexPipeLine(1),
% endif
    .RomCtrl0BootRomInitFile(BootRomInitFile),
    .RvCoreIbexRegFile(ibex_pkg::RegFileFPGA),
    .RvCoreIbexSecureIbex(0),
    .SramCtrlMainInstrExec(1),
    .PinmuxAonTargetCfg(PinmuxTargetCfg)
  ) top_${top["name"]} (
    .por_n_i                      ( por_n                 ),
    .clk_main_i                   ( ast_base_clks.clk_sys ),
    .clk_io_i                     ( ast_base_clks.clk_io  ),
    .clk_usb_i                    ( ast_base_clks.clk_usb ),
    .clk_aon_i                    ( ast_base_clks.clk_aon ),
    .clks_ast_o                   ( clkmgr_aon_clocks     ),
    .clk_main_jitter_en_o         ( jen                   ),
    .rsts_ast_o                   ( rstmgr_aon_resets     ),
    .sck_monitor_o                ( sck_monitor           ),
    .pwrmgr_ast_req_o             ( base_ast_pwr          ),
    .pwrmgr_ast_rsp_i             ( ast_base_pwr          ),
% if top["name"] != "darjeeling":
    .usb_dp_pullup_en_o           ( usb_dp_pullup_en      ),
    .usb_dn_pullup_en_o           ( usb_dn_pullup_en      ),
    .usbdev_usb_rx_d_i            ( usb_rx_d              ),
    .usbdev_usb_tx_d_o            ( usb_tx_d              ),
    .usbdev_usb_tx_se0_o          ( usb_tx_se0            ),
    .usbdev_usb_tx_use_d_se0_o    ( usb_tx_use_d_se0      ),
    .usbdev_usb_rx_enable_o       ( usb_rx_enable         ),
    .usbdev_usb_ref_val_o         ( usb_ref_val           ),
    .usbdev_usb_ref_pulse_o       ( usb_ref_pulse         ),
% endif
    .ast_edn_req_i                ( ast_edn_edn_req       ),
    .ast_edn_rsp_o                ( ast_edn_edn_rsp       ),
    .obs_ctrl_i                   ( obs_ctrl              ),
    .io_clk_byp_req_o             ( io_clk_byp_req        ),
    .io_clk_byp_ack_i             ( io_clk_byp_ack        ),
    .all_clk_byp_req_o            ( all_clk_byp_req       ),
    .all_clk_byp_ack_i            ( all_clk_byp_ack       ),
    .hi_speed_sel_o               ( hi_speed_sel          ),
    .div_step_down_req_i          ( div_step_down_req     ),
    .fpga_info_i                  ( fpga_info             ),
% if target["name"] != "cw305":
    .ast_tl_req_o                 ( base_ast_bus               ),
    .ast_tl_rsp_i                 ( ast_base_bus               ),
% if top["name"] == "earlgrey":
    .adc_req_o                    ( adc_req                    ),
    .adc_rsp_i                    ( adc_rsp                    ),
% endif
    .otp_ctrl_otp_ast_pwr_seq_o   ( otp_ctrl_otp_ast_pwr_seq   ),
    .otp_ctrl_otp_ast_pwr_seq_h_i ( otp_ctrl_otp_ast_pwr_seq_h ),
    .otp_obs_o                    ( otp_obs                    ),
    .sensor_ctrl_ast_alert_req_i  ( ast_alert_req              ),
    .sensor_ctrl_ast_alert_rsp_o  ( ast_alert_rsp              ),
    .sensor_ctrl_ast_status_i     ( ast_pwst.io_pok            ),
% if top["name"] == "darjeeling":
    .ctn_tl_h2d_o                 ( ctn_tl_h2d[0]              ),
    .ctn_tl_d2h_i                 ( ctn_tl_d2h[0]              ),
    .soc_gpi_async_o              (                            ),
    .soc_gpo_async_i              ( '0                         ),
    .dma_sys_req_o                (                            ),
    .dma_sys_rsp_i                ( '0                         ),
    .dma_ctn_tl_h2d_o             ( ctn_tl_h2d[1]              ),
    .dma_ctn_tl_d2h_i             ( ctn_tl_d2h[1]              ),
    .entropy_src_hw_if_req_o      ( entropy_src_hw_if_req      ),
    .entropy_src_hw_if_rsp_i      ( entropy_src_hw_if_rsp      ),
% else:
    .es_rng_req_o                 ( es_rng_req                 ),
    .es_rng_rsp_i                 ( es_rng_rsp                 ),
    .es_rng_fips_o                ( es_rng_fips                ),
    .flash_bist_enable_i          ( flash_bist_enable          ),
    .flash_power_down_h_i         ( 1'b0                       ),
    .flash_power_ready_h_i        ( 1'b1                       ),
    .flash_obs_o                  ( flash_obs                  ),
    .ast2pinmux_i                 ( ast2pinmux                 ),
% endif
    .calib_rdy_i                  ( ast_init_done              ),
    .ast_init_done_i              ( ast_init_done              ),
% endif

% if top["name"] in ["darjeeling"]:
    // DMI TL-UL
    .dbg_tl_req_i                 ( dmi_h2d                    ),
    .dbg_tl_rsp_o                 ( dmi_d2h                    ),
    // Quasi-static word address for next_dm register value.
    .rv_dm_next_dm_addr_i         ( '0                         ),
% endif
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
    .ram_1p_cfg_i    ( '0 ),
    .spi_ram_2p_cfg_i( '0 ),
% if top["name"] != "darjeeling":
    .usb_ram_2p_cfg_i( '0 ),
% endif
    .rom_cfg_i       ( '0 ),

     // DFT signals
    .ast_lc_dft_en_o      ( lc_dft_en                  ),
% if top["name"] in ["darjeeling"]:
    .ast_lc_hw_debug_en_o (                            ),
% endif
    // DFT signals
    .dft_hold_tap_sel_i ( '0               ),
    .scan_rst_ni        ( 1'b1             ),
    .scan_en_i          ( 1'b0             ),
    .scanmode_i         ( prim_mubi_pkg::MuBi4False )
  );
% endif

###################################################################
## CW310/305 capture board interface                             ##
###################################################################
% if target["name"] in ["cw310", "cw305"]:

  /////////////////////////////////////////////////////
  // ChipWhisperer CW310/305 Capture Board Interface //
  /////////////////////////////////////////////////////
  // This is used to interface OpenTitan as a target with a capture board trough the ChipWhisperer
  // 20-pin connector. This is used for SCA/FI experiments only.

  logic unused_inputs;
  % if target["name"] == "cw305":
  assign unused_inputs = manual_in_io_clkout ^ manual_in_io_trigger ^ manual_in_io_utx_debug;
  % else:
  assign unused_inputs = manual_in_io_clkout ^ manual_in_io_trigger;
  % endif

  // Synchronous clock output to capture board.
  assign manual_out_io_clkout = manual_in_io_clk;
  assign manual_oe_io_clkout = 1'b1;

  // Capture trigger.
  // We use the clkmgr_aon_idle signal of the IP of interest to form a precise capture trigger.
  // GPIO[11:10] is used for selecting the IP of interest. The encoding is as follows (see
  // hint_names_e enum in clkmgr_pkg.sv for details).
  //
  // IP              - GPIO[11:10] - Index for clkmgr_aon_idle
  // -------------------------------------------------------------
  //  AES            -   00       -  0
  //  HMAC           -   01       -  1 - not implemented on CW305
  //  KMAC           -   10       -  2 - not implemented on CW305
  //  OTBN           -   11       -  3 - not implemented on CW305
  //
  // GPIO9 is used for gating the selected capture trigger in software. Alternatively, GPIO8
  // can be used to implement a less precise but fully software-controlled capture trigger
  // similar to what can be done on ASIC.
  //
  // Note that on the CW305, GPIO[9,8] are connected to LED[5(Green),7(Red)].

  prim_mubi_pkg::mubi4_t clk_trans_idle, manual_in_io_clk_idle;

  % if target["name"] == "cw305":
  assign clk_trans_idle = top_${top["name"]}.clkmgr_aon_idle;
  % else:
  clkmgr_pkg::hint_names_e trigger_sel;
  always_comb begin : trigger_sel_mux
    % if top["name"] == "darjeeling":
    unique case ({dio_out[DioGpioGpio11], dio_out[DioGpioGpio10]})
    % else:
    unique case ({mio_out[MioOutGpioGpio11], mio_out[MioOutGpioGpio10]})
    % endif
      2'b00:   trigger_sel = clkmgr_pkg::HintMainAes;
      2'b01:   trigger_sel = clkmgr_pkg::HintMainHmac;
      2'b10:   trigger_sel = clkmgr_pkg::HintMainKmac;
      2'b11:   trigger_sel = clkmgr_pkg::HintMainOtbn;
      default: trigger_sel = clkmgr_pkg::HintMainAes;
    endcase;
  end
  assign clk_trans_idle = top_${top["name"]}.clkmgr_aon_idle[trigger_sel];
  % endif

  logic clk_io_div4_trigger_en, manual_in_io_clk_trigger_en;
  logic clk_io_div4_trigger_oe, manual_in_io_clk_trigger_oe;
  % if top["name"] == "darjeeling":
  logic clk_io_div4_trigger_hw_en, manual_in_io_clk_trigger_hw_en;
  logic clk_io_div4_trigger_hw_oe, manual_in_io_clk_trigger_hw_oe;
  logic clk_io_div4_trigger_sw_en, manual_in_io_clk_trigger_sw_en;
  logic clk_io_div4_trigger_sw_oe, manual_in_io_clk_trigger_sw_oe;
  assign clk_io_div4_trigger_hw_en = dio_out[DioGpioGpio9];
  assign clk_io_div4_trigger_hw_oe = dio_oe[DioGpioGpio9];
  assign clk_io_div4_trigger_sw_en = dio_out[DioGpioGpio8];
  assign clk_io_div4_trigger_sw_oe = dio_oe[DioGpioGpio8];
  % else:
  logic clk_io_div4_trigger_hw_en, manual_in_io_clk_trigger_hw_en;
  logic clk_io_div4_trigger_hw_oe, manual_in_io_clk_trigger_hw_oe;
  logic clk_io_div4_trigger_sw_en, manual_in_io_clk_trigger_sw_en;
  logic clk_io_div4_trigger_sw_oe, manual_in_io_clk_trigger_sw_oe;
  assign clk_io_div4_trigger_hw_en = mio_out[MioOutGpioGpio9];
  assign clk_io_div4_trigger_hw_oe = mio_oe[MioOutGpioGpio9];
  assign clk_io_div4_trigger_sw_en = mio_out[MioOutGpioGpio8];
  assign clk_io_div4_trigger_sw_oe = mio_oe[MioOutGpioGpio8];
  % endif

  // Synchronize signals to manual_in_io_clk.
  prim_flop_2sync #(
    .Width ($bits(clk_trans_idle) + 4)
  ) u_sync_trigger (
    .clk_i (manual_in_io_clk),
    .rst_ni(manual_in_por_n),
    .d_i   ({clk_trans_idle,
             clk_io_div4_trigger_hw_en,
             clk_io_div4_trigger_hw_oe,
             clk_io_div4_trigger_sw_en,
             clk_io_div4_trigger_sw_oe}),
    .q_o   ({manual_in_io_clk_idle,
             manual_in_io_clk_trigger_hw_en,
             manual_in_io_clk_trigger_hw_oe,
             manual_in_io_clk_trigger_sw_en,
             manual_in_io_clk_trigger_sw_oe})
  );

  // Generate the actual trigger signal as trigger_sw OR trigger_hw.
  assign manual_attr_io_trigger = '0;
  assign manual_oe_io_trigger  =
      manual_in_io_clk_trigger_sw_oe | manual_in_io_clk_trigger_hw_oe;
  assign manual_out_io_trigger =
      manual_in_io_clk_trigger_sw_en | (manual_in_io_clk_trigger_hw_en &
          prim_mubi_pkg::mubi4_test_false_strict(manual_in_io_clk_idle));
% endif
## This separate UART debugging output is needed for the CW305 only.
% if target["name"] == "cw305":

  // UART Tx for debugging. The UART itself is connected to the capture board.
  assign manual_out_io_utx_debug = top_${top["name"]}.cio_uart0_tx_d2p;
  assign manual_oe_io_utx_debug = 1'b1;
% endif

endmodule : chip_${top["name"]}_${target["name"]}
