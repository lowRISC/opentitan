---
title: "Glossary of Terms"
---

## Build

"Build" refers to the invocation of the EDA tool to compile and elaborate the provided top levels which results in the generation of an executable / database and all of its pre-requisites.
In OpenTitan, the build stage broadly performs the following steps:
- Create the build directory.
- Execute an pre-build utility scripts, if provided.
- Invoke FuseSoC (or equivalent) to generate the filelist (it also autogenerates SystemVerilog sources, if configured).
- Invoke the EDA tool to build the simulation executable / database.
- Execute any post-build utility scripts, if provided.

## Build configuration

## Build modes

A test or a subset of tests may require the DUT to be modified a certain way at compile time (typically via `+define+` preprocessor macros) or elaboration time (typically, modification of design parameter values).
A build mode encapsulates the list of these special build-time options that may result in the generation of an altered simulation executable / database during the build phase with respect to the default (i.e., no special build-time options provided).
In addition, any special pre-build or post-build utility scripts that are required to be executed may be specified within a build mode as well.
The altered simulation executable / database will also cause the simulations to behave differently.
It is hence, necessary to uniquely represent the list of builds, so that they are generated in their own directories.

## Compute infrastructure

A compute infrastructure refers to an organization's high-performance compute setup and the mechanism to launch jobs to it and monitor their status.
Typically, this is a cluster of computers on an internal shared network with read / write access to a network drive.
There are commercial products in the market that provide the load balancing mechanism to dispatch a large number of jobs into the cluster.
The [IBM LSF](https://www.ibm.com/docs/en/spectrum-lsf/10.1.0?topic=overview-lsf-introduction) and [Oracle Sun Grid](https://docs.oracle.com/cd/E19279-01/820-3257-12/n1ge.html) are the typical ones used in the industry.

## Design level

EDA tool flows are run at various levels of the design:
- **Primitives**:
  The most basic building blocks used to create hardware designs
  OpenTitan provides a library of reusble [primitives](https://docs.opentitan.org/hw/ip/prim/doc/index.html).

- **Modules**:
  A discrete entity that implements a specific feature of a larger design
  Modules may instantiate other modules or primitives.

- **IP cores** (a.k.a. block):
  An intellectual property (IP) core is a reusable design module that implements a set of features or a protocol, such as UART.
  These are the building blocks of a chip (SoC) or a larger subsystem.
  IPs have well defined specifications and are typically verified to full coverage closure, so that they can be reused with minimal effort and risk in other designs.
  In the context of running EDA tool flows, the terms "IP level" and "block level" are used interchangeably.
  IP blocks may instantiate several sub-modules and/or primitives.

- **Subsystems**:
  A collection of IP blocks that closely interact with each other to form a larger, reusable module, such as the entropy subsystem.
  OpenTitan does not have a subsystem level design yet.

- **SoC** (a.k.a. chip):
  A system-on-a-chip (SoC) refers to the full chip level design which is eventually taped-out, i.e. manufactured into a discrete Silicon-based semiconductor IC.

## DUT

DUT stands for "design-under-test".
It represents a design entity (an RTL module written in SystemVerilog) on which an EDA tool flow, such as simulations, is run.

## DUT configuration file

A DUT configuration file describes everything required to run a specific EDA tool flow on it.
It is written in Hjson, and is consumed by DVSim as a mandatory input.
Please see the [Hjson guide]({{< relref "hjson_guide" >}}) for more details on what information a DUT configuration file is expected to capture.

## EDA tool flow

An EDA (electronic design automation) tool flow in the context of the development of an integrated circuit (IC) refers to the use of open source as well as commercial tools to develop, simulate, synthesize, and verify the correctness of the design.

The following is a typical list of EDA tool flows commonly encountered in the development of an IC:
- Simulations (RTL, gate level, power-aware)
- Coverage Unreachability Analysis (UNR)
- Emulation (running tests on an FPGA)
- Place and route
- Synthesis
- Power estimation and optimization
- Static timing analysis (STA)
- Formal property verification
- Semantic and style lint
- Clock domain crossing (CDC)
- Reset domain crossing (RDC)
- Logic equivalence check (LEC)

## Filelist

A filelist (a.k.a. "dot-f" file, since it typically has a `.f` extension) is a dependency-resolved list of SystemVerilog sources that is consumed by the EDA tool during the build stage.
While it is not formalized into a standard, it is widely supported by most, if not all, EDA tool vendors.
In OpenTitan, this step is accomplished by [FuseSoC](https://fusesoc.readthedocs.io/).

## Random seed

## Regressions

A regression is a group of tests that are labeled with a target name.
When a regression is run, all of the tests it encapsulates are run.
Please see [TBD]() for more details.

DVSim provides these standard regression targets for all DUTs:
- `smoke` (typically run in CI checks)
- `nightly` (a full regression with coverage enabled, that is run every night)
- `v1` / `v2` / `v3` (DVSim automatically extracts tests that are tagged V1 / V2 / V3 and creates a regression target.
- `all` (runs all tests with the preset reseeds, without coverage)
- `all_once` (run all tests with only a single randomly chosen seed)

## Reseeds

## Run

## Run modes

## Sim modes

Sim modes are the same as [build modes](#build-modes), but with the following distinctions:
- A test specification cannot specify a sim mode as its build configuration.
- Sim modes are additional build time options that are appended to each build configuration.
- The can only be set on the command-line.

## TB

TB is an abbreviation for the testbench.
It is typically a SystemVerilog module (in the context of running simulations or FPV) that instantiates the DUT and various interfaces that are used to actuate the DUT.
It is considered the [top level](#top-level) entity that is compiled and elaborated during the build phase.

Sometimes, the complete verification environment for a DUT (which includes the SystemVerilog testbench, the tests, sequences, scoreboard, etc.) is also referred to as the "testbench".

## Testplan

A testplan describes a list of tests and functional coverage planned to be developed and written towards DV closure for a DUT.
Please see the [testplanner]({{< relref "testplanner" >}}) tool for additional details.
The [DV methodology]({{< relref "doc/ug/dv_methodology.md#testplan" >}}) also provides some additional context on testplans and testpoints.

## Testpoint

A testpoint describes how a discrete feature of the DUT is planned to be tested.
The testplan is essentially a list of testpoints.
Please see [testpoints]({{< relref "testplanner/#testpoints" >}}) in the testplanner tool guide for additional details.

## Test specifications

A test specification points to an actual implemented test in SystemVerilog, including all of the build and runtime options that are required to successfully execute the test in a simulation.
It is a uniquely runnable target.
The DUT configuration file for running simulations is expected to contain a list of test specifications.
A test specification may not correspond 1:1 to a testpoint.
The test specification label(s) that satisfy a testpoint are mapped to the testpoint.

## Top level

A top level entity is the highest design entity (i.e., a design entity which is itself, not instatiated as a sub-module in a different module) that is compiled and elaborated.
For simulations, this is typically the testbench, since it instantiates the DUT.
In simulations, there are also standalone RTL modules (specifically, SVA bindfiles) that are not directly instantiated in the testbench or the DUT hierarchies.
These are also considered "top levels" that are elaborated by the tool.
For other EDA tool flows that are run on the DUT directly, the top level refers to the DUT itself.

The full chip level testbench is also sometimes referred to as "top level", so the usage of this term depends on the context.

## UVM

The Universal Verification Methodology ([UVM](https://www.accellera.org/downloads/standards/uvm)) is a library of SystemVerilog classes that serve as the building blocks to develop an object-oriented, modular, scalable, and highly reusable verification infrastructure for a DUT.
It is ratified as an IEEE standard [1800.2](https://ieeexplore.ieee.org/document/7932212).
