# RNG UVM Agent

RNG UVM Agent is extended from DV library agent classes.

## Description

This agent continually drives entropy/entropy_ok when the enable is asserted.
From enable asserted, it drives after entropy_agent_cfg.entropy_ok_delay_clks
and holds each entropy value for entropy_agent_cfg.entropy_hold_clks.
