---
title: "Ibex ICache DV Plan"
---

## Goals
* **DV**
  * Verify all Ibex ICache IP features by running dynamic simulations with a SV/UVM based testbench
  * Develop and run all tests based on the [testplan](#testplan) below towards closing code and functional coverage.
* **FPV**
  * [TBD]

## Current status

* Design & verification stage (TODO: Create HW dashboard & add link) (see [HW development stages](https://docs.opentitan.org/doc/project/hw_stages) for what this means)
* Simulation results (TODO: Generate nightly simulation results & add link)

## Design features

The ICache design is documented in the [Instruction Cache](https://ibex-core.readthedocs.io/en/latest/icache.html) section of the Ibex User Manual.

## Testbench architecture

The testbench is built using the [DV_LIB testbench architecture](https://github.com/lowRISC/ibex/tree/master/vendor/lowrisc_ip/dv_lib/).

The testbench intentionally avoids knowing detailed information about the cache's performance characteristics (for example, cache size, line size or number of ways).
This means that the testbench cannot compare the DUT with a reference model, nor can it model the exact requests that the DUT will make of instruction memory: the whole point of a cache is that it might avoid an instruction fetch.

The cache has two main interfaces, which face the core and instruction bus respectively.
We model this with two agents: the *core agent* and the *memory agent*.
The core agent will emulate a core making instruction fetch requests from the cache and the memory agent will emulate the instruction bus.

In fact, there's one more logical interface: the `busy_o` signal from the cache.
This signal is passed up to top-level in the design and warns the chip not to clock-gate or reset the core (because there are bus transactions in flight, or a memory invalidation in progress).
Rather than have an extra agent just for this single-bit passive signal, we pass the signal to the monitor in the core agent, which reports changes to the scoreboard.

![Testbench block diagram](tb.svg)

Both agents report events to the scoreboard.
The core agent reports whether the cache is busy, every branch sent to the cache, invalidation requests, enabling/disabling the cache and every instruction fetched (address and contents).
The memory agent reports every change of seed (see the [Memory Agent](#memory-agent) section below).

### Agents

#### Core Agent

The core agent emulates a core making requests of the cache.
This is an active master with a standard UVM structure (sequencer, driver, monitor).
Code implementing the agent can be found in [`dv/uvm/icache/dv/ibex_icache_core_agent`](https://github.com/lowRISC/ibex/tree/master/dv/uvm/icache/dv/ibex_icache_core_agent).

The complicated internal state of the cache is somewhat visible to the core, resulting in strict rules about how the core drives it (see the [detailed behaviour](https://ibex-core.readthedocs.io/en/latest/icache.html#detailed-behaviour) section of the documentation).
These rules actually make the cache easier to verify because they constrain how seemingly unrelated signals (`req_i`, `icache_inval_i`, `icache_enable_i`) must be driven relative to instruction requests, meaning a simpler set of valid transactions.
These transactions are:

 * Branch to address `A`, maybe invalidating and/or enabling/disabling the cache, and read `N ≥ 0` instructions. Stop after fewer instructions if there's an error.
 * Disable `req_i` for `C ≥ 0` cycles, possibly invalidating and/or enabling/disabling the cache.
   When it comes back up, read `N ≥ 0` instructions, stopping early on error.

The monitor for the core agent reports cache invalidations, when the cache is enabled/disabled, branches and instruction reads (including errors).

#### Memory Agent

The memory agent emulates the instruction bus, supplying data to the cache.
This must be deterministic (in order for the scoreboard to tell whether the cache fetched the right data), but must also be able to change with time (in order to check invalidation works correctly).
To support this, the memory contents are modelled with a 32-bit seed value.

The architectural state of the instruction bus and memory (contents at each address; PMP ranges; ranges that will cause a memory error) are all derived from this seed.
The precise functions can be found in [`dv/uvm/icache/dv/ibex_icache_mem_agent/ibex_icache_mem_model.sv`](https://github.com/lowRISC/ibex/blob/master/dv/uvm/icache/dv/ibex_icache_mem_agent/ibex_icache_mem_model.sv).

The memory agent is an active slave, responding to instruction fetches from the cache with either a PMP error (on the same cycle as the request) or instruction data (with an in-order request pipeline).
As well as the instruction fetch requests, its sequence contains occasional transactions that change the underlying seed.
These transactions are reported to the scoreboard (so it can know the set of possible seeds for any given fetch).
To avoid too many valid seeds in the scoreboard, this should happen at a similar rate to cache invalidations in the core agent.

### Top level testbench

The top level testbench is located at [`dv/uvm/icache/dv/tb/tb.sv`](https://github.com/lowRISC/ibex/blob/master/dv/uvm/icache/dv/tb/tb.sv). It instantiates the `ibex_icache` DUT module whose source is at [`rtl/ibex_icache.sv`](https://github.com/lowRISC/ibex/blob/master/rtl/ibex_icache.sv).
In addition, it instantiates the following interfaces, connects them to the DUT and sets their handle into `uvm_config_db`:
* Clock and reset interface ([`vendor/lowrisc_ip/common_ifs`](https://github.com/lowRISC/ibex/tree/master/vendor/lowrisc_ip/common_ifs))
* Core interface ([`dv/uvm/icache/dv/ibex_icache_core_agent/ibex_icache_core_if.sv`](https://github.com/lowRISC/ibex/blob/master/dv/uvm/icache/dv/ibex_icache_core_agent/ibex_icache_core_if.sv))
* Memory interface ([`dv/uvm/icache/dv/ibex_icache_mem_agent/ibex_icache_mem_if.sv`](https://github.com/lowRISC/ibex/blob/master/dv/uvm/icache/dv/ibex_icache_mem_agent/ibex_icache_mem_if.sv))

### Common DV utility components

TBD

### Compile-time configurations

TBD

### Global types & methods
All common types and methods defined at the package level can be found in
`ibex_icache_env_pkg`. Some of them in use are:

TBD

### Stimulus strategy
#### Test sequences

All test sequences reside in [`dv/uvm/icache/dv/env/seq_lib`](https://github.com/lowRISC/ibex/tree/master/dv/uvm/icache/dv/env/seq_lib).

TBD

#### Functional coverage

TBD

### Self-checking strategy
#### Scoreboard
The `ibex_icache_scoreboard` is used to check that instructions fetched from the cache lie at the correct addresses and contain the correct data.
It has two analysis ports: one for the memory agent and another for the core agent.

The scoreboard can keep track of what addresses it expects from responses to the core by modelling the cache's internal address counter and following branches.

To check correctness of the fetched data, the scoreboard will keep track of the set of seeds that have been set by the memory agent since the last cache invalidation began.
For any given seed, the scoreboard can tell what the memory response should have been (an error, or data as a function of the seed and address).
The scoreboard can thus check that the response sent by the cache is what it would expect based on one of the possible seeds.

If the cache is disabled, the scoreboard only checks against seeds valid since the last branch.
It has to check more than just the most recent seed because the cache's fill buffers aren't invalidated until a branch happens.

If the cache is enabled, the scoreboard must check seeds valid since the last branch that happened at or before the most recent invalidation.

We may wish to make more assertions about the cache's behaviour on the instruction bus.
For example, that the cache stops making requests shortly after `req_i` goes low.
To do so, we would just need to monitor fetches in the memory agent as well as seed updates.

#### Assertions
* Interface assertions: TBD
* Unknown checks on DUT outputs: TBD

## Building and running tests

Tests are built and run with the [`dvsim`](https://github.com/lowRISC/ibex/tree/master/vendor/lowrisc_ip/dvsim) tool (vendored in from the OpenTitan project).
To run a basic sanity test:

```console
$ cd dv/uvm/icache/dv
$ dvsim.py icache_sim_cfg.hjson -i ibex_icache_sanity
```

## Testplan

This will be generated from [`dv/uvm/icache/data/ibex_icache_testplan.hjson`](https://github.com/lowRISC/ibex/blob/master/dv/uvm/icache/data/ibex_icache_testplan.hjson), but is not automatically included in this document at the moment because we haven't got the tooling set up to do so.

<!--
  TODO: How will we include the testplan in this documentation?
        More tools from OpenTitan?
 -->
