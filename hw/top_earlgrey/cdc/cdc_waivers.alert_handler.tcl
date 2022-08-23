# Copyright lowRISC contributors.
# Licensed under the Apache License, Version 2.0, see LICENSE for details.
# SPDX-License-Identifier: Apache-2.0
#
# Verix CDC waiver file
# Expression:
#  ControlSignal==""
#  ReconSignal==""
#  MultiClockDomains=="IO_DIV2_CLK::IO_DIV4_CLK"

set_rule_status -rule {W_CNTL} -status {Waived} -expression {(Signal=~"*u_alert_handler.gen_alerts*u_secure_anchor_flop*") && (ReceivingFlop=~"*u_*alert_sender*.u_decode_ack*")} -comment {Alert ACK remains high until alert sender acked}
set_rule_status -rule {W_CNTL} -status {Waived} -expression {(Signal=~"*u_alert_handler.gen_alerts*u_secure_anchor_flop*") && (ReceivingFlop=~"*u_*alert_sender*.u_decode_ping*")} -comment {Alert PING remains high until alert sender acked}
set_rule_status -rule {W_RECON_GROUPS} -status {Waived} -expression {(ControlSignal=~"*u_alert_handler.u_alert_handler_lpg_ctrl.gen_lpgs**") && (ReconSignal=~"*u_alert_handler.u_alert_handler_lpg_ctrl.gen_alert_map*unused_logic*")} -comment {Intended logic to avoid lint error}
