---
title: "Directory Structure"
---

This document provides an overview of the opentitan repository directory structure.
The hierarchy underneath the root is fairly self explanatory, containing the following:
* `doc`: High level documentatation, user guides and reference manuals
* `util`: Helper scripts and generator tools
* `hw`: Design and DV sources
* `sw`: All software sources used in the project

We will focus on the directory structure underneath `hw` and `sw` below.

## Directory structure underneath `hw`
```
hw
├──dv             => Common / shared resources for SV/UVM as well as
│                    Verilator based testbenches
│
├──formal         => Scripts to build and run formal property verification
│                    (FPV) for all applicable IPs to ensure protocol
│                    compliance
│
├──ip             => Standalone or generic / parameterized implementations
│                    of comportable IPs designed towards building SoCs
│
├──lint           => Scripts to run the `lint` tool on all RTL sources
│
├──top_earlgrey   => An implementation of OpenTitan SoC built using above
│                    IPs as well as third-party 'vendored' IPs
│
├──vendor         => Vendored-in open source IPs from external repositories
```

### `hw/ip`
```
   ip
   ├──uart        => UART IP root dir
   │  │
   │  ├──data     => Configuration data sources for design, DV and project
   │  │              status tracking
   │  │
   │  ├──doc      => All documentation sources including design specification
   │  │              and DV document
   │  │
   │  ├──dv       => SV/UVM testbench sources
   │  │
   │  ├──fpv      => Testbench sources used in FPV (if applicable)
   │  │
   │  ├──model    => Reference 'model' implementation in C (if applicable)
   │  │
   │  ├──rtl      => RTL design sources
   │  │
   │  ├──util     => IP-specfic automation scripts (if applicable)
   │  │
   │  ├──...      => Additional sub-directories could exist for specific IPs
   │                 based on need
   │
   ├──...         => More such Comportable IPs...
```

### `hw/top_earlgrey`
```
   top_earlgrey         => Chip root dir
   │
   ├──data              => Configuration data sources for design, DV and
   │                       project status tracking
   │
   ├──doc               => All documentation sources including chip
   │                       specification and DV document
   │
   ├──dv                => Chip level SV/UVM testbench sources
   │  └──autogen        => auto-generated chip DV sources
   │
   ├──ip                => IPs tailor-made for top_earlgrey
   │  │
   │  ├──xbar           => XBAR implementation for top_earlgrey
   │  │  ├──dv          => DV sources
   │  │  │  └──autogen  => auto-generated XBAR DV sources
   │  │  └──rtl         => RTL sources
   │  │     └──autogen  => Auto-generated XBAR RTL sources
   │  │
   │  ├──...            => More such IPs tailored for top_earlgrey...
   │
   ├──rtl               => Chip level RTL sources
   │  └──autogen        => auto-generated chip RTL sources
   │
   ├──sw                => Auto-generated chip-specific headers for SW
   │
   └──util              => Chip-specfic automation scripts
```

### Auto-generated sources: checked-in
In cases where we rely on automatic generation of RTL, DV, or software sources we currently check those files in to the repository.
This is primarily motivated by a desire to make it easy for engineers to rapidly test spot-fixes.
This is a decision that might be revisited in the future.

#### Mitigating issues
Auto-generated sources can get out-of-sync if the underlying tools or templates are updated.
Also, users may accidently make modifications to those files by hand, which will cease to exist the next time the tools are run.
We employ the following methods to mitigate these risks:
* Add a CI check when a pull request is made to merge new changes to ensure that the checked-in file and the generator output are enquivalent and not out-of-sync
* Put auto-generated sources under a dedicated `autogen/` directory
* Add a warning message banner as a comment clearly indicating that the file has been auto-generated with the complete command

## Directory structure underneath `sw`
```
sw
├──device                 => Sources compiled for the OpenTitan chip,
│  │                         including tests run on FPGA and simulations
│  │ 
│  ├──boot_rom            => Sources for generating the primary boot image
│  │                         loaded into ROM
│  │ 
│  ├──benchmarks          => Standard benchmarks and instructions for running
│  │   └──coremark           them
│  │ 
│  ├──doc                 => Documentation sources
│  │ 
│  ├──examples            => Example programs to demonstrate basic
│  │   ├──hello_world        functionality
│  │   ├──...
│  │ 
│  ├──exts                => Sources that are specific to the intended target
│  │   │                     (FPGA, Verilator, DV, firmware)
│  │   └──common          => Common sources for all SW tests including the CRT
│  │                         source and the linker script
│  │ 
│  ├──lib                 => SW library of device interface functions (DIFs)
│  │                         that provide APIs for controlling the hardware
│  │ 
│  └──tests               => SW tests implemented on FPGA/Verilator/DV targets
│     ├──flash_ctrl
│     ├──...
│   
├──host                   => Sources compiled for the host communicating with
│                            our OpenTitan chip
│
└──vendor                 => Vendored-in open source software sources from
    │                        external repositories
    └── cryptoc
```
