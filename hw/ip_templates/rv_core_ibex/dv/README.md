# Ibex RISC-V Core Wrapper DV document

## Goals
  * Verify compliance with the RISC-V specifications used by OpenTitan.
  * Verify Ibex's security hardening features.
  * Ensure correct functionality is maintained across all possible behaviours of Ibex's external interfaces when integrated into OpenTitan.
  * Verify additional features provided by the wrapper.

## Design features

`rv_core_ibex` wraps a dual core lockstep configuration of [Ibex](https://www.github.com/lowrisc/ibex), an RV32IMC CPU with security hardening features.
The wrapper adapts Ibex's top-level interfaces to be suitable for use with OpenTitan.
In addition rv_core_ibex provides some extra functionality controlled via bus accessible registers.

For more information please see the [Ibex RISC-V Core Wrapper Technical Specification](../README.md).

## Current Status

* Ibex Verification is tracked in the [Ibex documentation](https://ibex-core.readthedocs.io/en/latest/03_reference/verification_stages.html)
  * Verification follows the OpenTitan [HW development stages](../../../../doc/project_governance/development_stages.md)
* [Nightly regression results](https://dev.azure.com/lowrisc/lowrisc-private/_build?definitionId=11)
  * These are from the Ibex private-ci which is restricted to OpenTitan project members

## Verification strategy

The main Ibex testbench is not contained in the OpenTitan repository.
Verification is primarily done by the testbench in the Ibex repository, see the [Ibex Testplan](https://ibex-core.readthedocs.io/en/latest/03_reference/testplan.html) for more details.

The additional features provided by the RISC-V Core Wrapper are verified at a chip level only (See the [Earlgrey Chip DV testplan](../../../top_earlgrey/dv/README.md).
As they are simple features chip level only verification suffices to meet our goals.

Similarly there is no specific verification for the TL-UL <-> Ibex memory protocol wrappers (provided by the separate [TLUL IP](../../tlul/README.md)).
These are exercised extensively by all chip-level testing that runs software on Ibex providing comprehensive verification.

## Coverage

Due to the simplicity of the additional `rv_core_ibex` features, the existence of self checking chip-level tests combined with code and expression coverage is sufficient to be confident of their verification without functional coverpoints.

The TL-UL <-> Ibex memory protocol contains minimal logic so again code and expression coverage will suffice with one exception.
The iside and dside Ibex interfaces can have up to 8 or 2 outstanding requests respectively, we need to ensure these scenarios are seen.
An SVA cover expression will be used to produce coverage for this.
