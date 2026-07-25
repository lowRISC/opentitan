# Reset agent

The reset agent (`reset_agent`) is a very simple agent that monitors a single reset line.
The only implemented mode is passive mode, but this is enough to send items at the start and end of reset for an interface.

A component can subscribe to the analysis port (`m_analysis_port`) to consume these items.
In order that a sequence (which is not a component) can react to resets, the agent also has a `uvm_event` that is triggered on each edge.
Each time the event is triggered, the associated data (accessible through `get_trigger_data`) is the same item.

Note that the reset signal on the monitored interface has type `logic`, so can have value `x` or `z`.
Such values are ignored by this agent: it tracks the most recently seen known value (`0` or `1`) and waits to see a transition to the opposite value (`1` or `0`, respectively).
As such, no transition is reported for this sequence of `rst_n` values: `... 0, x, 0, z, 0 ...`.
The sequence `... 0, x, 1, ...` is considered to have a transition on the cycle where `rst_n` becomes `1`.
At the start of `run_phase`, the monitor reports an "transition" to the first known value (`0` or `1`).
