# Tock OS

Tock OS is a secure embedded operating system for microcontrollers.

This directory contains OpenTitan board and chip implementation for Tock that
are maintained downstream. Other OS components are pulled directly from
upstream or a local Tock OS repository. See below for more details.

Tock OS documentation available at:
https://www.tockos.org/
https://github.com/tock/tock

# Rationale

Upstream OpenTitan implementation is not using DIFs, which means that the
peripheral drivers cannot be directly implemented upstream. Therefore it is not
possible to use upstream OpenTitan board and chip implementations.

The intention is, where possible, to use upstream packages. At the moment the
only excpetions are board and chip packages, which are implemented and
maintained downstream.

# Copyright

The source files in this directory come from two sources, with slightly
different copyright licences.

Some source files are copied from the upstream tock repository. The notice in
COPYRIGHT in this directory applies to all source files with explicit Tock OS
Developers copyright headers, or no copyright headers at all.

Where lowRISC has added additional files, these are marked with the lowRISC
Copyright header, and the notice in LICENCE in the root of this repository
applies.

# Directory layout

## Tock OS standard directories

`boards` directory contains board specific configuration.
`chips` directory contains chip specific configuration, and peripheral driver
implementations.

For more information please see Tock OS documentation and local README files.

## Additional directories

`tock` directory implements a crate that pulls in external tock dependencies
(packages that are not maintained downstream). These dependencies can be either
pulled directly from the upstream, or from a local Tock directory.