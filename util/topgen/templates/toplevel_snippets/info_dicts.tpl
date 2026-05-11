## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%import topgen.lib as lib%>\
<%page args="top, feature_info, cio_info"/>\
<%
## feature-gating flags
feature_info['has_pinmux']        = lib.find_module(top['module'], 'pinmux') is not None
feature_info['has_alert_handler'] = lib.find_module(top['module'], 'alert_handler') is not None
feature_info['has_ast']           = lib.find_module(top['module'], 'ast') is not None
feature_info['has_rstmgr']        = lib.find_module(top['module'], 'rstmgr') is not None
feature_info['has_gpio']          = lib.find_module(top['module'], 'gpio') is not None
feature_info['has_scan_en'] = False
for m in top['module']:
  if not lib.is_inst(m):
    continue
  block = name_to_block[m['type']]
  if block.scan_en:
    feature_info['has_scan_en'] = True

if feature_info['has_pinmux']:
  cio_info['num_mio_inputs'] = top['pinmux']['io_counts']['muxed']['inouts'] + \
                              top['pinmux']['io_counts']['muxed']['inputs']
  cio_info['num_mio_outputs'] = top['pinmux']['io_counts']['muxed']['inouts'] + \
                              top['pinmux']['io_counts']['muxed']['outputs']
  cio_info['num_mio_pads'] = top['pinmux']['io_counts']['muxed']['pads']

  cio_info['num_dio_inputs'] = top['pinmux']['io_counts']['dedicated']['inouts'] + \
                              top['pinmux']['io_counts']['dedicated']['inputs']
  cio_info['num_dio_outputs'] = top['pinmux']['io_counts']['dedicated']['inouts'] + \
                              top['pinmux']['io_counts']['dedicated']['outputs']
  cio_info['num_dio_total'] = top['pinmux']['io_counts']['dedicated']['inouts'] + \
                              top['pinmux']['io_counts']['dedicated']['inputs'] + \
                              top['pinmux']['io_counts']['dedicated']['outputs']

  max_sigwidth = max([x["width"] if "width" in x else 1 for x in top["pinmux"]["ios"]])
  cio_info['max_sigwidth'] = len("{}".format(max_sigwidth))
%>\
