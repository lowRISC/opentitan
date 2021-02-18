# ALERT_ESC Agent

ALERT_ESC UVM Agent is extended from DV library agent classes.

## Description

This agent implements both alert(alert_rx, alert_tx) and escalation (esc_rx,
esc_tx) interface protocols, and can be configured to behave in both host and
device modes. For design documentation, please refer to [alert_handler
spec]({{< relref "hw/ip/alert_handler/doc/_index.md" >}}).

### Alert Agent

Alert agent supports both synchronous and asynchronous modes.

#### Alert Device Agent

For IPs that send out alerts, it is recommended to attach alert device agents to
the block level testbench.
Please refer to [cip_lib documentation]({{< relref "hw/dv/sv/cip_lib/doc/index.md" >}})
regarding instructions to configure alert device agent in DV testbenches.

### Escalation Agent
