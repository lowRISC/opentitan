## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%page args="m, alert_idx, block, alert_handler_signals, alert_info, default_handler"/>\
<%
if block.alerts:
  alert_comments = []
  if "alert_handler" in m:
    handler = m["alert_handler"]
  else:
    handler = default_handler
  alert_tx, alert_rx = alert_handler_signals[handler]
  w = len(block.alerts)
  if 'outgoing_alert' in m:
      outgoing_alert = m['outgoing_alert']
      lo = outgoing_alert_idx[outgoing_alert]
      async_exp = f"AsyncOnOutgoingAlert{alert_group.capitalize()}"
  else:
      lo = alert_idx[handler]
      async_exp = f"{handler}_reg_pkg::AsyncOn"
  slice = f"{lo+w-1}:{lo}"
  async_expr = f"{async_exp}[{slice}]"
  alert_tx_expr = f"{alert_tx}[{slice}]"
  alert_rx_expr = f"{alert_rx}[{slice}]"
  for a in block.alerts:
      alert_comments.append(f"{handler}[{alert_idx[handler]}]: {a.name}")
      alert_idx[handler] += 1

## Construct alert_info to pass data back to the toplevel template
  alert_info["tx_expr"] = alert_tx_expr
  alert_info["rx_expr"] = alert_rx_expr
  alert_info["async_expr"] = async_expr
  alert_info["comments"].extend(alert_comments)
%>\
