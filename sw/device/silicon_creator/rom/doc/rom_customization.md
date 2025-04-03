---
Document: RFC
Title: ROM Vendor Customizations
Status: Approved by TC on 2025-02-06
Authors:
  - Samuel Ortiz <sameo@opentitan.org>
Reviewers:
  - "@jadephilipoom"
  - "@engdoreis"
---

# RFC: ROM Vendor Customizations

## Problem Statement

Currently, OpenTitan mask ROM implementations lack customization options for silicon creators and vendors. While discrete OpenTitan ROMs can be directly built upon the [upstream implementation](https://github.com/lowRISC/opentitan/tree/master/sw/device/silicon_creator/rom), the same isn't true for integrated OpenTitan top ROMs.

Integrated OpenTitan ROMs configure, initialize, and interact with external subsystems specific to the platform. These interactions often vary between vendors and platform variants. A single, fixed ROM implementation prevents downstream silicon creators and vendors from directly utilizing the upstream code, forcing them to fork the project and maintain custom versions internally.

## Requirements

To enable direct vendor contribution and consumption of OpenTitan upstream ROM implementations, the project architecture and source code for ROMs must meet the following requirements:

1. Vendor customization: OpenTitan ROM code should allow silicon creators and vendors to customize the upstream ROM execution flow with vendor-specific initialization and configuration sequences.
2. Controlled customization points: OpenTitan ROMs should be customizable at specific, predefined execution points. Vendors can only modify ROM behavior at these designated points.
3. Support for closed-source customization: The OpenTitan ROM build infrastructure should support linking ROM images with externally stored, vendor-specific customization code, allowing vendors to keep their customizations private.
4. Attestation: Silicon creators and vendors should provide endorsed reference values for their customized OpenTitan ROMs, including the ROM version and its associated hash. Out-of-band verifiers can then compare these values with the ROM's generated attestation reports.
5. Default functionality: By default, OpenTitan ROMs should function without any vendor-specific customizations.

## Proposed Approach

At a high level, the proposed solution involves implementing an OpenTitan ROM as a state machine. Each state in this state machine is semantically defined by the upstream ROM code and represents a customizable execution step.

As the ROM progresses through its state machine, it executes the current state and then transitions to the next one. A state execution consists of the following three sequential steps:

1. Pre-run Hook: Executed before the primary ROM state function.
2. ROM State Run: The core execution of the ROM state.
3. Post-run Hook: Executed after the primary ROM state function.

By structuring the ROM as a state machine with these hooks, vendors can customize the ROM's behavior at specific points without modifying the upstream ROM code.

```
           Initial
          ┌ROM State───┐
          │ ┌────────┐ │
          │ │Pre-run │ │
          │ ├────────┤ │
          │ │  Run   │ │
          │ ├────────┤ │
          │ │Post-run│ │
          │ └────────┘ │
          └──────┬─────┘
 ROM   ┌─────────┴─────────┐  ROM
┌State─▽─────┐      ┌──────▽──State
│ ┌────────┐ │      │ ┌────────┐ │
│ │Pre-run │ │      │ │Pre-run │ │
│ ├────────┤ │      │ ├────────┤ │
│ │  Run   │ │      │ │  Run   │ │
│ ├────────┤ │      │ ├────────┤ │
│ │Post-run│ │      │ │Post-run│ │
│ └────────┘ │      │ └────────┘ │
└────────────┘      └──────┬─────┘
                           │  ROM
                    ┌──────▽──State
                    │ ┌────────┐ │
                    │ │Pre-run │ │
                    │ ├────────┤ │
                    │ │  Run   │ │
                    │ ├────────┤ │
                    │ │Post-run│ │
                    │ └────────┘ │
                    └────────────┘
```

With this proposal, vendors can customize an OpenTitan ROM by providing custom implementations for the pre-run and post-run hooks of any ROM state. By default, these hooks are empty.

The main ROM state implementation, the run callback, is executed in step 2. All ROM state run callbacks are defined by the upstream ROM implementation and are not customizable.

Crucially, only the run callback determines the next state in the ROM state machine. Pre-run and post-run hooks cannot override these transitions, preventing vendors from directly modifying the ROM's execution flow.

In essence, this proposal enables vendors to customize the execution of individual ROM states, but it strictly controls the overall ROM execution flow.

### ROM states

Each OpenTitan ROM defines a set of execution states and associates each state with a specific ROM state run callback. A ROM state run callback takes an opaque pointer argument (which is shared with the state hooks) and returns the next state in the sequence.

To enable effective vendor customization, ROM states should be clearly defined and map to specific functional steps in the ROM's execution flow. For instance, `kRomStateBootstrap` is a well-defined state, while `kRomStateStep3` is too generic.

The more precisely a ROM state is defined, the easier it is for vendors to understand and customize its behavior.

### ROM state hooks

Pre-run and post-run ROM state hooks are executed by the ROM state machine before and after each state run callback, respectively. They share state with the state run callbacks through an opaque pointer argument.

Unlike the state run callback, ROM state hooks cannot determine the next state in the ROM state machine. Vendors can customize specific ROM state execution steps through these hooks by providing custom implementations in an external repository.

Similar to the existing manufacturing and test hook customization framework, custom ROM state hooks can be included in a ROM image by specifying the path to the vendor hook implementations in an environment variable passed to the ROM build system:

``` bash
ROM_HOOKS_DIR=/PATH/TO/LOCAL/ROM/HOOKS ./bazelisk.sh build //sw/device/silicon_creator/rom:mask_rom
```
