# Example: Ibex with enabled instruction tracing for simulation

## Overview

This examples shows the usage of the module `ibex_core_tracing` which forwards
all port signals to the `ibex_core` and a subset of signals to `ibex_tracer`.
The tracer will create a file with a stream of executed instructions.

## Prerequisites

For this example, `modelsim` must be available and the following environment
variable must point to the path of installation:

```
export MODEL_TECH=/path/to/modelsim/bin
```

## Usage

Run the following command in the top level directory.

```
fusesoc --cores-root=. run --target=sim lowrisc:ibex:top_tracing_sim
```

The trace output can be found in `build/lowrisc_ibex_top_tracing_sim_0.1/sim-modelsim/trace_core_00_0.log`.
