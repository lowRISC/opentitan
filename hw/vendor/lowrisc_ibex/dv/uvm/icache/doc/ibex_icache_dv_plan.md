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

The testbench is built using the [DV_LIB testbench architecture](https://github.com/lowRISC/ibex/tree/master/vendor/lowrisc_ip/dv/sv/dv_lib/).

The testbench intentionally avoids knowing detailed information about the cache's performance characteristics (for example, cache size, line size or number of ways).
This means that the testbench cannot compare the DUT with a reference model, nor can it model the exact requests that the DUT will make of instruction memory: the whole point of a cache is that it might avoid an instruction fetch.

The cache has two main interfaces, which face the core and instruction bus respectively.
We model this with two main agents: the *core agent* and the *memory agent*.
The core agent will emulate a core making instruction fetch requests from the cache and the memory agent will emulate the instruction bus.

In fact, there's one more logical interface at the top-level: the `busy_o` signal from the cache.
This signal is passed up to top-level in the design and warns the chip not to clock-gate or reset the core (because there are bus transactions in flight, or a memory invalidation in progress).
Rather than have an extra agent just for this single-bit passive signal, we pass the signal to the monitor in the core agent, which reports changes to the scoreboard.

Finally, we bind an interface in for each RAM in the cache.
These interfaces are controlled by instances of the *ECC agent*, which is in charge of injecting occasional one- and two-bit errors which should be spotted by the cache's ECC checks.

![Testbench block diagram](tb.svg)

Both main agents report events to the scoreboard.
The core agent reports whether the cache is busy, every branch sent to the cache, invalidation requests, enabling/disabling the cache and every instruction fetched (address and contents).
The memory agent reports every change of seed (see the [Memory Agent](#memory-agent) section below).
The ECC agents don't currently report to the scoreboard, since they aren't supposed to have any architectural effect.

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

As well as restrictions on how the core can communicate, the cache also assumes that the core will never modify memory and then perform a cached fetch from that memory without an invalidation.
This means that the cache doesn't need to avoid multi-way hits with inconsistent data.
In order that the testbench can guarantee this doesn't happen, the core agent must be in charge of deciding when to update the contents of memory with a new seed (see the Memory Agent, below).
A new seed is picked on every invalidation (since this gives the maximum test sensitivity) and is picked occasionally when the cache is fetching when disabled.

#### Memory Agent

The memory agent emulates the instruction bus, supplying data to the cache.
This must be deterministic (in order for the scoreboard to tell whether the cache fetched the right data), but must also be able to change with time (in order to check invalidation works correctly).
To support this, the memory contents are modelled with a 32-bit seed value.

The architectural state of the instruction bus and memory (contents at each address; ranges that will cause a memory error) are all derived from this seed.
The precise functions can be found in [`dv/uvm/icache/dv/ibex_icache_mem_agent/ibex_icache_mem_model.sv`](https://github.com/lowRISC/ibex/blob/master/dv/uvm/icache/dv/ibex_icache_mem_agent/ibex_icache_mem_model.sv).

The memory agent is an active slave, responding to instruction fetches from the cache with instruction data (with an in-order request pipeline).

#### ECC Agent

Each ECC agent emulates possible data corruption in the cache's underlying memories.
The sole sequence causes occasional 1- or 2-bit errors, injected by XORing valid data from the underlying memory with a mask.

### Top level testbench

The top level testbench is located at [`dv/uvm/icache/dv/tb/tb.sv`](https://github.com/lowRISC/ibex/blob/master/dv/uvm/icache/dv/tb/tb.sv). It instantiates the `ibex_icache` DUT module whose source is at [`rtl/ibex_icache.sv`](https://github.com/lowRISC/ibex/blob/master/rtl/ibex_icache.sv).
In addition, it instantiates the following interfaces, connects them to the DUT and sets their handle into `uvm_config_db`:
* Clock and reset interface ([`vendor/lowrisc_ip/dv/sv/common_ifs`](https://github.com/lowRISC/ibex/tree/master/vendor/lowrisc_ip/dv/sv/common_ifs))
* Core interface ([`dv/uvm/icache/dv/ibex_icache_core_agent/ibex_icache_core_if.sv`](https://github.com/lowRISC/ibex/blob/master/dv/uvm/icache/dv/ibex_icache_core_agent/ibex_icache_core_if.sv))
* Memory interface ([`dv/uvm/icache/dv/ibex_icache_mem_agent/ibex_icache_mem_if.sv`](https://github.com/lowRISC/ibex/blob/master/dv/uvm/icache/dv/ibex_icache_mem_agent/ibex_icache_mem_if.sv))
* ECC interfaces ([`dv/uvm/icache/dv/ibex_icache_ecc_agent/ibex_icache_ecc_if.sv`](https://github.com/lowRISC/ibex/blob/master/dv/uvm/icache/dv/ibex_icache_ecc_agent/ibex_icache_ecc_if.sv))

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

### Functional coverage

Coverpoints will be created at two levels, ICache top level and individual fill buffers.

#### ICache top-level coverage

**Coverpoints**
* `cp_lookup_req` - Two types of lookup
  * `straightline_req` - Looking up the PC following the current one
  * `branch_req` - Lookup up a PC from a branch request
* `cp_hit_miss` - Hit seen and miss seen
* `cp_hit_way` - Hit seen in every cache way
* `cp_fill_buffer_usage` - How many fill buffers are in use
* `cp_data_ecc_err` - ECC error seen in data RAM
* `cp_tag_ecc_error` - ECC error seen in each tag RAM way
* `cp_data_src` - Sources of data for an instruction
  * `ICDataSrcFB` - Data from fill buffer
  * `ICDataSrcExt` - Data direct from external imem bus
  * `ICDataSrcCache` - Data from cache memory
* `cp_req_when_fb_full` - ICache request when fill buffers are all in use
* `cp_branch_when_fb_full` - ICache branch request when fill buffers are all in use
* `cp_throttle_req` - Lookup requests throttled

**Crosses**
* `tag_req_cross` - Cross of all sources of tag RAM requests
* `data_req_cross` - Cross of all sources of data RAM requests
* `data_src_cross` - Cross of data sources, whether the skid buffer was used and
  whether the cache is enabled

#### ICache per fill buffer coverage

**Coverpoints**
* `cp_addr_hz` - Whilst active this fill buffer has the same address as another active fill buffer
* `cp_out_of_order_finish` - Number of older fill buffers outstanding when this fill buffer releases
* `cp_state` - Fill buffer in various states (note there are no explicit single 'state' flops in the RTL)
  * `FBIdle` - Idle and ready to be allocated
  * `FBReqing` - Requesting data via the imem bus
  * `FBReqingAndFilling` - At least one request granted but others still needed and awaiting data
  * `FBFilling` - All requests granted and awaiting data
  * `FBAllocating` - Waiting to or in the process of writing to data RAM
  * `FBAwaitingOutput` - Waiting for fill buffer data to be consumed by output before releasing
* `cp_fb_done_reason` - Why the fill buffer has finished
  * `FBNotDone` - Fill buffer not yet done
  * `FBDoneHitNoExtReqs` - Fill buffer hit against cache and sent no external requests 
  * `FBDoneHitExtReqs` - Fill buffer hit against cache and sent external requests (which must be completed before fill buffer can release)
  * `FBDoneMiss` - Fill buffer missed in cache and has fetched data to satisfy request
  * `FBDoneBranchNoExtReqs` - Fill buffer became stale due to branch and sent no external requests and so released
  * `FBDoneBranchExtReqs` - Fill buffer became stale due to branch and sent external requests (which must be completed before fill buffer can release)
  * `FBDoneNoCache` - Cache is disabled so fill buffer done once it provides output from external request
  * `FBDoneMemErr` - Instruction fetch saw a bus error
* `cp_state_when_disabling` - State of the fill buffer when the cache is disabled
* `cp_state_when_enabling` - State of the fill buffer when the cache is enabled
* `cp_state_when_inval_start` - State of the fill buffer when cache invalidation begins
* `cp_starting_beat` - Beat fill buffer started on and hence sent its first request for (which may be part way through a line)


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

Tests are built and run with the [`dvsim`](https://github.com/lowRISC/ibex/tree/master/vendor/lowrisc_ip/util/dvsim) tool (vendored in from the OpenTitan project).
To ensure output files end up in the right place without ugly command lines, this is wrapped up in a Makefile.
To run the test suite, run:

```console
$ make -C dv/uvm/icache/dv
```

For more complicated use cases (enabling wave dumps, coverage, specific seeds), there are some options in the Makefile.
For very specific use cases, you'll need to run dvsim.py directly.
The easiest way to get an initial command to edit is to run `make -n`.

## Testplan

This will be generated from [`dv/uvm/icache/data/ibex_icache_testplan.hjson`](https://github.com/lowRISC/ibex/blob/master/dv/uvm/icache/data/ibex_icache_testplan.hjson), but is not automatically included in this document at the moment because we haven't got the tooling set up to do so.

<!--
  TODO: How will we include the testplan in this documentation?
        More tools from OpenTitan?
 -->
