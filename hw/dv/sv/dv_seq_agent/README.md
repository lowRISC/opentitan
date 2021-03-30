---
title: "DV Seq Agent"
---

# DV Seq Agent

The DV Seq Agent is a thin subclass of `dv_base_agent` (defined in the
`dv_lib` package). It abstracts away a common task, where you want to
connect the sequencer's list of items to the monitor, to make it easy
to compare these sequence items with the transactions that were
actually seen on the bus.
