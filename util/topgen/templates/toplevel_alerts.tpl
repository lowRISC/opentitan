## Copyright lowRISC contributors (OpenTitan project).
## Licensed under the Apache License, Version 2.0, see LICENSE for details.
## SPDX-License-Identifier: Apache-2.0
<%page args="m, alert_idx, block, alert_handler_signals, alert_info"/>\
<%
alert_comments = []
alert_handlers_used = set(m["alert_connections"].values())
if len(alert_handlers_used) == 1:
    ## Grab all alerts for this module in one big slice
    handler, = alert_handlers_used
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
else:
    ## Concatenate multiple alert handlers' signals
    async_slices = []
    alert_tx_slices = []
    alert_rx_slices = []
    for a in block.alerts:
        handler = m["alert_connections"][a.name]
        idx = alert_idx[handler]
        alert_tx, alert_rx = alert_handler_signals[handler]
        async_slices.append(f"{handler}_reg_pkg::AsyncOn[{idx}]")
        alert_tx_slices.append(f"{alert_tx}[{idx}]")
        alert_rx_slices.append(f"{alert_rx}[{idx}]")
        alert_comments.append(f"{handler}[{idx}]: {a.name}")
        alert_idx[handler] += 1
    async_expr =    "{" + (",\n"+19*" ").join(async_slices)    + "}"
    alert_tx_expr = "{" + (",\n"+22*" ").join(alert_tx_slices) + "}"
    alert_rx_expr = "{" + (",\n"+22*" ").join(alert_rx_slices) + "}"

## Construct alert_info to pass data back to the toplevel template
alert_info["tx_expr"] = alert_tx_expr
alert_info["rx_expr"] = alert_rx_expr
alert_info["async_expr"] = async_expr
alert_info["comments"].extend(alert_comments)
%>\
