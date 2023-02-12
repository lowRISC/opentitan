# PUSH_PULL UVM Agent

PUSH_PULL UVM Agent is extended from DV library agent classes.

## Description

This agent implements both Push (ready/valid) and Pull (req/ack) interface
protocols, and can be configured to behave in both host and device modes.

The agent configuration object (`push_pull_agent_cfg`) contains an enum `agent_type`
that is used to select either push or pull modes.
To configure the agent to use the ready/valid protocol, set `agent_type = PushAgent`, and
to configure the agent to use the req/ack protocol, set `agent_type = PullAgent`.
