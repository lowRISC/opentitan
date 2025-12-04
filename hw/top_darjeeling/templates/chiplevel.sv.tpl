// Copyright lowRISC contributors (OpenTitan project).
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
%>\

module chip_${top["name"]}_${target["name"]} #(
  parameter bit SecRomCtrl0DisableScrambling = 1'b0,
  parameter bit SecRomCtrl1DisableScrambling = 1'b0
) (
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
    },
    // Pad scan roles
    dio_scan_role: {
<%
  scan_roles = []
  for sig in list(reversed(top["pinmux"]["ios"])):
    if sig["connection"] != "muxed":
      if len(sig['pad']) > 0:
        scan_string = lib.Name.from_snake_case('dio_pad_' + sig['pad'] + '_scan_role')
        scan_roles.append((f'scan_role_pkg::{scan_string.as_camel_case()}', sig['name']))
      else:
        scan_roles.append(('NoScan', sig['name']))
%>\
% for scan_role, name in list(scan_roles):
      ${scan_role}${"" if loop.last else ","} // DIO ${name}
% endfor
    },
    mio_scan_role: {
<%
  scan_roles = []
  for pad in list(reversed(pinout["pads"])):
    if pad["connection"] == "muxed":
      scan_string = lib.Name.from_snake_case('mio_pad_' + pad['name'] + '_scan_role')
      scan_roles.append(f'scan_role_pkg::{scan_string.as_camel_case()}')
%>\
% for scan_role in list(scan_roles):
      ${scan_role}${"" if loop.last else ","}
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

  // AST signals needed in padring
  logic scan_rst_n;
   prim_mubi_pkg::mubi4_t scanmode;

  padring #(
    // Padring specific counts may differ from pinmux config due
    // to custom, stubbed or added pads.
    .NDioPads(${len(dedicated_pads)}),
    .NMioPads(${len(muxed_pads)}),
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
    .clk_scan_i   ( ast_base_clks.clk_sys ),
    .scanmode_i   ( scanmode              ),
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
## AST For all targets                                           ##
###################################################################

  //////////////////////////////////
  // AST - Common for all targets //
  //////////////////////////////////

  // pwrmgr interface
  pwrmgr_pkg::pwr_ast_req_t base_ast_pwr;
  pwrmgr_pkg::pwr_ast_rsp_t ast_base_pwr;
  pwrmgr_pkg::pwr_boot_status_t pwrmgr_boot_status;

  // assorted ast status
  ast_pkg::ast_pwst_t ast_pwst;

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

  // debug policy bus
  soc_dbg_ctrl_pkg::soc_dbg_policy_t soc_dbg_policy_bus;

  // observe interface
  logic [7:0] otp_obs;
  ast_pkg::ast_obs_ctrl_t obs_ctrl;

  // otp power sequence
  otp_macro_pkg::otp_ast_req_t otp_macro_pwr_seq;
  otp_macro_pkg::otp_ast_rsp_t otp_macro_pwr_seq_h;

  // OTP DFT configuration
  otp_macro_pkg::otp_cfg_t otp_cfg;
  assign otp_cfg = otp_macro_pkg::OTP_CFG_DEFAULT;

  // entropy source interface
  logic es_rng_enable, es_rng_valid;
  logic [ast_pkg::EntropyStreams-1:0] es_rng_bit;

  // alerts interface
  ast_pkg::ast_alert_rsp_t ast_alert_rsp;
  ast_pkg::ast_alert_req_t ast_alert_req;
  assign ast_alert_rsp = '0;

  // clock bypass req/ack
  prim_mubi_pkg::mubi4_t io_clk_byp_req;
  prim_mubi_pkg::mubi4_t all_clk_byp_req;
  prim_mubi_pkg::mubi4_t hi_speed_sel;

  assign io_clk_byp_req    = prim_mubi_pkg::MuBi4False;
  assign all_clk_byp_req   = prim_mubi_pkg::MuBi4False;
  assign hi_speed_sel      = prim_mubi_pkg::MuBi4False;

  // DFT connections
  logic scan_en;
  lc_ctrl_pkg::lc_tx_t lc_dft_en;

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
                test:   ast_ram_1p_cfg.test,
                cfg_en: ast_ram_1p_cfg.marg_en,
                cfg:    ast_ram_1p_cfg.marg
              },
    rf_cfg:  '{
                test:   ast_rf_cfg.test,
                cfg_en: ast_rf_cfg.marg_en,
                cfg:    ast_rf_cfg.marg
              }
  };

  logic unused_usb_ram_2p_cfg;
  assign unused_usb_ram_2p_cfg = ^{ast_ram_2p_fcfg.marg_en_a,
                                   ast_ram_2p_fcfg.marg_a,
                                   ast_ram_2p_fcfg.test_a,
                                   ast_ram_2p_fcfg.marg_en_b,
                                   ast_ram_2p_fcfg.marg_b,
                                   ast_ram_2p_fcfg.test_b};

  // this maps as follows:
  // assign spi_ram_2p_cfg = {10'h000, ram_2p_cfg_i.a_ram_lcfg, ram_2p_cfg_i.b_ram_lcfg};
  prim_ram_2p_pkg::ram_2p_cfg_t spi_ram_2p_cfg;
  assign spi_ram_2p_cfg = '{
    a_ram_lcfg: '{
                   test:   ast_ram_2p_lcfg.test_a,
                   cfg_en: ast_ram_2p_lcfg.marg_en_a,
                   cfg:    ast_ram_2p_lcfg.marg_a
                 },
    b_ram_lcfg: '{
                   test:   ast_ram_2p_lcfg.test_b,
                   cfg_en: ast_ram_2p_lcfg.marg_en_b,
                   cfg:    ast_ram_2p_lcfg.marg_b
                 },
    default: '0
  };

  prim_rom_pkg::rom_cfg_t rom_ctrl0_cfg;
  prim_rom_pkg::rom_cfg_t rom_ctrl1_cfg;

  assign rom_ctrl0_cfg = '{
    test: ast_rom_cfg.test,
    cfg_en: ast_rom_cfg.marg_en,
    cfg: ast_rom_cfg.marg
  };
  assign rom_ctrl1_cfg = '{
    test: ast_rom_cfg.test,
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

  // external clock comes in at a fixed position
  assign ext_clk = mio_in_raw[MioPadMio11];

  wire unused_t0, unused_t1;
  assign unused_t0 = 1'b0;
  assign unused_t1 = 1'b0;

  // AST does not use all clocks / resets forwarded to it
  logic unused_slow_clk_en;
  assign unused_slow_clk_en = base_ast_pwr.slow_clk_en;

  logic unused_pwr_clamp;
  assign unused_pwr_clamp = base_ast_pwr.pwr_clamp;

  ast #(
    .UsbCalibWidth(ast_pkg::UsbCalibWidth),
    .Ast2PadOutWidth(ast_pkg::Ast2PadOutWidth),
    .Pad2AstInWidth(ast_pkg::Pad2AstInWidth)
  ) u_ast (
    // external POR
    .por_ni                ( manual_in_por_n ),

    // USB IO Pull-up Calibration Setting
    .usb_io_pu_cal_o       ( ),

    // Direct short to PAD
    .ast2pad_t0_ao         ( unused_t0 ),
    .ast2pad_t1_ao         ( unused_t1 ),

    // clocks and resets supplied for detection
    .sns_clks_i            ( clkmgr_aon_clocks    ),
    .sns_rsts_i            ( rstmgr_aon_resets    ),
    .sns_spi_ext_clk_i     ( sck_monitor          ),
    // tlul
    .tl_i                  ( base_ast_bus ),
    .tl_o                  ( ast_base_bus ),
    // init done indication
    .ast_init_done_o       ( ),
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
    .ast_pwst_h_o          ( ),
    // main regulator
    .main_env_iso_en_i     ( base_ast_pwr.pwr_clamp_env ),
    .main_pd_ni            ( base_ast_pwr.main_pd_n ),
    // pdm control (otp)
    .otp_power_seq_i       ( otp_macro_pwr_seq ),
    .otp_power_seq_h_o     ( otp_macro_pwr_seq_h ),
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
    .usb_ref_pulse_i       ( '0 ),
    .usb_ref_val_i         ( '0 ),
    .clk_src_usb_en_i      ( '0 ),
    .clk_src_usb_o         (    ),
    .clk_src_usb_val_o     (    ),
    // rng
    .rng_en_i              ( es_rng_enable ),
    .rng_fips_i            ( es_rng_fips   ),
    .rng_val_o             ( es_rng_valid  ),
    .rng_b_o               ( es_rng_bit    ),
    // alerts
    .alert_rsp_i           ( ast_alert_rsp  ),
    .alert_req_o           ( ast_alert_req  ),
    // dft
    .lc_dft_en_i           ( lc_dft_en        ),
    .usb_obs_i             ( '0 ),
    .otp_obs_i             ( otp_obs ),
    .otm_obs_i             ( '0 ),
    .obs_ctrl_o            ( obs_ctrl ),
    // pinmux related
    .padmux2ast_i          ( '0         ),
    .ast2padmux_o          (            ),
    .ext_freq_is_96m_i     ( hi_speed_sel ),
    .all_clk_byp_req_i     ( all_clk_byp_req  ),
    .all_clk_byp_ack_o     ( ),
    .io_clk_byp_req_i      ( io_clk_byp_req   ),
    .io_clk_byp_ack_o      ( ),
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

  // TODO: Resolve this and wire it up.
  tlul_pkg::tl_h2d_t ctn_misc_tl_h2d_i;
  assign ctn_misc_tl_h2d_i = tlul_pkg::TL_H2D_DEFAULT;
  tlul_pkg::tl_d2h_t ctn_misc_tl_d2h_o;

  // TODO: Over/ride/ all access range checks for now.
  prim_mubi_pkg::mubi8_t ac_range_check_overwrite_i;
  assign ac_range_check_overwrite_i = prim_mubi_pkg::MuBi8True;

  // TODO: External RACL error input.
  top_racl_pkg::racl_error_log_t ext_racl_error;
  assign ext_racl_error = '0;

  ////////////////
  // CTN M-to-1 //
  ////////////////

  tlul_pkg::tl_h2d_t ctn_tl_h2d[2];
  tlul_pkg::tl_d2h_t ctn_tl_d2h[2];
  //TODO: Resolve this and wire it up.
  assign ctn_tl_h2d[1] = tlul_pkg::TL_H2D_DEFAULT;

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
    if ((ctn_sm1_to_s1n_tl_h2d.a_address & ~(TOP_DARJEELING_SOC_PROXY_RAM_CTN_SIZE_BYTES-1)) ==
        (TOP_DARJEELING_SOC_PROXY_RAM_CTN_BASE_ADDR - TOP_DARJEELING_SOC_PROXY_CTN_BASE_ADDR)) begin
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
    .user_rsvd_o (),
    .rdata_i     (sram_rdata),
    .rvalid_i    (sram_rvalid),
    .rerror_i    ('0),
    .compound_txn_in_progress_o(),
    .readback_en_i(prim_mubi_pkg::MuBi4False),
    .readback_error_o(),
    .wr_collision_i(1'b0),
    .write_pending_i(1'b0)
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
    .cfg_i    (ram_1p_cfg),
    .cfg_rsp_o(),
    .alert_o()
  );

  //////////////////////////////////
  // Manual Pad / Signal Tie-offs //
  //////////////////////////////////

  assign manual_out_por_n = 1'b0;
  assign manual_oe_por_n = 1'b0;

  assign manual_out_otp_ext_volt = 1'b0;
  assign manual_oe_otp_ext_volt = 1'b0;

  // These pad attributes currently tied off permanently (these are all input-only pads).
  assign manual_attr_por_n = '0;
  assign manual_attr_otp_ext_volt = '0;

  logic unused_manual_sigs;
  assign unused_manual_sigs = ^{
    manual_in_otp_ext_volt
  };

  // The power manager waits until the external reset request is removed by the SoC before
  // proceeding to boot after an internal reset request. DV may also drive this signal briefly and
  // asynchronously to request a reset on behalf of the simulated SoC.
  //
  // Note that since the signal is filtered inside the SoC proxy it must be of at least 5
  // AON clock periods in duration.
  logic soc_rst_req_async;
  assign soc_rst_req_async = 1'b0;

  //////////////////////
  // Top-level design //
  //////////////////////
  top_${top["name"]} #(
    .PinmuxAonTargetCfg(PinmuxTargetCfg),
    .SecAesAllowForcingMasks(1'b1),
    .SecRomCtrl0DisableScrambling(SecRomCtrl0DisableScrambling),
    .SecRomCtrl1DisableScrambling(SecRomCtrl1DisableScrambling)
  ) top_${top["name"]} (
    // ast connections
    .por_n_i                           ( por_n                      ),
    .clk_main_i                        ( ast_base_clks.clk_sys      ),
    .clk_io_i                          ( ast_base_clks.clk_io       ),
    .clk_aon_i                         ( ast_base_clks.clk_aon      ),
    .clks_ast_o                        ( clkmgr_aon_clocks          ),
    .clk_main_jitter_en_o              ( jen                        ),
    .rsts_ast_o                        ( rstmgr_aon_resets          ),
    .integrator_id_i                   ( '0                         ),
    .sck_monitor_o                     ( sck_monitor                ),
    .pwrmgr_ast_req_o                  ( base_ast_pwr               ),
    .pwrmgr_ast_rsp_i                  ( ast_base_pwr               ),
    .ast_tl_req_o                      ( base_ast_bus               ),
    .ast_tl_rsp_i                      ( ast_base_bus               ),
    .obs_ctrl_i                        ( obs_ctrl                   ),
    .otp_macro_pwr_seq_o               ( otp_macro_pwr_seq          ),
    .otp_macro_pwr_seq_h_i             ( otp_macro_pwr_seq_h        ),
    .otp_obs_o                         ( otp_obs                    ),
    .otp_cfg_i                         ( otp_cfg                    ),
    .otp_cfg_rsp_o                     ( otp_cfg_rsp                ),
    .ctn_tl_h2d_o                      ( ctn_tl_h2d[0]              ),
    .ctn_tl_d2h_i                      ( ctn_tl_d2h[0]              ),
    .ac_range_check_overwrite_i        ( ac_range_check_overwrite_i ),
    .racl_error_i                      ( ext_racl_error             ),
    .soc_gpi_async_o                   (                            ),
    .soc_gpo_async_i                   ( '0                         ),
    .soc_dbg_policy_bus_o              ( soc_dbg_policy_bus         ),
    .debug_halt_cpu_boot_i             ( '0                         ),
    .dma_sys_req_o                     (                            ),
    .dma_sys_rsp_i                     ( '0                         ),
    .mbx_tl_req_i                      ( tlul_pkg::TL_H2D_DEFAULT   ),
    .mbx_tl_rsp_o                      (                            ),
    .pwrmgr_ext_rst_ack_i              ( 1'b0                       ),
    .pwrmgr_boot_status_o              ( pwrmgr_boot_status         ),
    .ctn_misc_tl_h2d_i                 ( ctn_misc_tl_h2d_i          ),
    .ctn_misc_tl_d2h_o                 ( ctn_misc_tl_d2h_o          ),
    .soc_wkup_async_i                  ( 1'b0                       ),
    .soc_rst_req_async_i               ( soc_rst_req_async          ),
    .soc_lsio_trigger_i                ( '0                         ),
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
    .es_rng_enable_o                   ( es_rng_enable              ),
    .es_rng_valid_i                    ( es_rng_valid               ),
    .es_rng_bit_i                      ( es_rng_bit                 ),
    .es_rng_fips_o                     ( es_rng_fips                ),

    // OTP external voltage
    .otp_ext_voltage_h_io              ( OTP_EXT_VOLT               ),

    // DMI TL-UL
    .dbg_tl_req_i                      ( dmi_h2d                    ),
    .dbg_tl_rsp_o                      ( dmi_d2h                    ),
    // Quasi-static word address for next_dm register value.
    .rv_dm_next_dm_addr_i              ( '0                         ),
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
    .rom_ctrl0_cfg_i                           ( rom_ctrl0_cfg ),
    .rom_ctrl1_cfg_i                           ( rom_ctrl1_cfg ),
    .i2c_ram_1p_cfg_i                          ( ram_1p_cfg ),
    .i2c_ram_1p_cfg_rsp_o                      (   ),
    .sram_ctrl_ret_aon_ram_1p_cfg_i            ( ram_1p_cfg ),
    .sram_ctrl_ret_aon_ram_1p_cfg_rsp_o        (   ),
    .sram_ctrl_main_ram_1p_cfg_i               ( ram_1p_cfg ),
    .sram_ctrl_main_ram_1p_cfg_rsp_o           (   ),
    .sram_ctrl_mbox_ram_1p_cfg_i               ( ram_1p_cfg ),
    .sram_ctrl_mbox_ram_1p_cfg_rsp_o           (   ),
    .otbn_imem_ram_1p_cfg_i                    ( ram_1p_cfg ),
    .otbn_imem_ram_1p_cfg_rsp_o                (   ),
    .otbn_dmem_ram_1p_cfg_i                    ( ram_1p_cfg ),
    .otbn_dmem_ram_1p_cfg_rsp_o                (   ),
    .rv_core_ibex_icache_tag_ram_1p_cfg_i      ( ram_1p_cfg ),
    .rv_core_ibex_icache_tag_ram_1p_cfg_rsp_o  (   ),
    .rv_core_ibex_icache_data_ram_1p_cfg_i     ( ram_1p_cfg ),
    .rv_core_ibex_icache_data_ram_1p_cfg_rsp_o (   ),
    .spi_device_ram_2p_cfg_sys2spi_i           ( spi_ram_2p_cfg ),
    .spi_device_ram_2p_cfg_spi2sys_i           ( spi_ram_2p_cfg ),
    .spi_device_ram_2p_cfg_rsp_sys2spi_o       (   ),
    .spi_device_ram_2p_cfg_rsp_spi2sys_o       (   ),

    // DFT signals
    .ast_lc_dft_en_o                   ( lc_dft_en                  ),
    .ast_lc_hw_debug_en_o              (                            ),
    .scan_rst_ni                       ( scan_rst_n                 ),
    .scan_en_i                         ( scan_en                    ),
    .scanmode_i                        ( scanmode                   ),

    // FPGA build info
    .fpga_info_i                       ( '0                         )
  );

  logic unused_signals;
  assign unused_signals = ^{pwrmgr_boot_status.clk_status,
                            pwrmgr_boot_status.cpu_fetch_en,
                            pwrmgr_boot_status.lc_done,
                            pwrmgr_boot_status.otp_done,
                            pwrmgr_boot_status.rom_ctrl_status,
                            pwrmgr_boot_status.strap_sampled};

endmodule : chip_${top["name"]}_${target["name"]}
