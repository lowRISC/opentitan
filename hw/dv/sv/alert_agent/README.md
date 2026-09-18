# Alert agent

The alert agent extends from the `dv_lib` agent classes.

## Description

This agent implements the alert interface protocol.
For design documentation, please refer to [alert_handler spec](../../../top_earlgrey/ip_autogen/alert_handler/README.md).
The agent can be configured to behave as an alert sender (host mode) or receiver (device mode).

## Device Agent

For IPs that send out alerts, it is recommended to attach alert device agents to the block level testbench.
Please refer to [cip_lib documentation](../cip_lib/README.md) regarding instructions to configure alert device agent in DV testbenches.
