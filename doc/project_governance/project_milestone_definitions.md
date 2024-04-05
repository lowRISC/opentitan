# Generalized Project Milestone Definitions

[TOC]

## Overview

This document defines template milestones for OpenTitan complex development and
is intended for publication on GitHub and the OpenTitan documentation page. The
definitions mainly define rules for the open-source side, since the
closed-source side may be developed at a different cadence by a vendor. While it
is recommended to adhere to these template milestones as much as possible,
project leads may modify milestone definitions or introduce sub milestones as
appropriate. Production-specific milestones (e.g. compliance testing,
certification milestones) are out of scope of this document and will be defined
later.

## Milestones

### M0 High Level Specification

**GitHub Milestone**: `_project code_.M0`

**Goal**: Complete high level specification for the project.

**Exit Criteria**:

*   Use cases and threat model is released
*   High level specification RFCs approved and released (i.e., blocks are in L1)
*   Associated folder structures for blocks or top-levels have been created

### M1 Initial Design

**GitHub Milestone**: `_project code_.M1`

**Goal**: Initial design scaffolding to start floorplanning and PD iterations.

**Exit Criteria**:

*   All blocks at D1/V0
*   Top-level at D1/V0

### M2 Functionality Complete

**GitHub Milestone**: `_project code_.M2`

**Goal**: Stable feature set to start focusing on design verification.

**Exit Criteria**:

*   All blocks at D2/V1
*   Top-level at D2/V1

### M3 Security Hardening Complete

**GitHub Milestone**: `_project code_.M3`

**Goal**: Implement and review all countermeasures.

**Exit Criteria**:

*   All blocks at D2(S)[^1]

*   Top-level at D2(S)

### M4 RTL Freeze

**GitHub Milestone**: `_project code_.M4`

**Goal**: Freeze open source RTL code except for bug fixes and
achieve >=V2(S)[^2] verification quality.

**Exit Criteria**:

*   All blocks at D3/V2(S)
*   Top-level at D3/V2(S)
*   CDC and RDC complete
*   Floorplan fixed
*   Area and timing optimizations at RTL are complete
*   Projects may choose to require ECOs after this milestone

### M5 Final Release

**GitHub Milestone**: `_project code_.M5`

**Goal**: Reach final maturity state for all blocks and top level.

**Exit Criteria**:

*   All blocks at D3/V3
*   Top level at D3/V3
*   Bug fixes or fixes due to PD feedback require ECOs after this milestone

**All blocks and the top-level are moved into the L2 stage via RFC and a tapeout
archival branch is created in the open source repository. **

### M6 Final ECO

**GitHub Milestone**: `_project code_.M6`

**Goal**: Triage and implement ECOs.

**Exit Criteria**:

*   All closed-source IPs at D3/V3 (or equivalent)[^3]

*   All approved ECOs have been implemented

*   ECOs after this milestone slip the tapeout date due to PD impacts

### M7 Tapeout Signoff

**GitHub Milestone**: `_project code_.M7`

**Goal**: Final tapeout signoff.

**Exit Criteria**:

*   Tapeout readiness checklist complete[^4]

*   Design git tagging and archival for reproducibility[^5]

### M8 Post Silicon Validation Start

**GitHub Milestone**: `_project code_.M8`

**Goal**: Prepare for bringup and post silicon validation (PSV)

**Exit Criteria**:

*   Bringup and PSV testplans have been written
*   Bringup and PSV tests are written and tested where possible (FPGA,
    simulation)
*   Chip samples have arrived

### M9 Post Silicon Validation Complete

**GitHub Milestone**: `_project code_.M9`

**Goal**: Complete post silicon validation.

**Exit Criteria**:

*   Bringup and PSV testplans fully executed
*   PSV results documented
*   Errata documented as necessary
*   ECOs and RTL fixes completed as necessary, for all fixes that didn’t make it
    into the database earlier, including contributing fixes back to the open
    source as necessary

## Notes

[^1]: The V2 signoff is not part of this milestone since experience has shown
    that security hardening on the design side can greatly perturb DV closure
    at V2 (especially coverage closure).
[^2]: Instead of making M4 a pure DV milestone such as M3 for design, the V2S
    requirement is bundled up with D3. The reason for that is that D2S is
    significantly more involved than V2S due to the security audit. The V2S
    signoff can benefit from the D2S pre-work and is more straightforward. In
    addition to that, the V2 and V2S requirements are bundled up in M4
    milestone since non-security blocks typically do not require much work for
    V2S, and for security blocks it typically makes sense to sign off both V2
    and V2S closely together due to the overlap of functional paths and
    countermeasures.
[^3]: Closed-source maturity stages are otherwise not mandated since the
    closed-source counterparts may be developed at a different cadence and in
    a completely closed environment with no external access by a vendor.
[^4]: We may consider creating a public version of the signoff checklist,
    otherwise the default is project confidential.
[^5]: This process needs to be defined.
