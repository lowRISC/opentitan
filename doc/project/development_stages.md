---
aliases: [/doc/project/hw_stages/]
title: OpenTitan Hardware Development Stages
---

## Document Goals

This document describes development stages for hardware within the OpenTitan program.
This includes design and verification stages meant to give a high-level view of the status of a design.
OpenTitan being an open-source program aimed at a high quality silicon release, the intent is to find a balance between the rigor of a heavy tapeout process and the more fluid workings of an open source development.

This document also serves as a guide to the [Hardware Dashboard]({{< relref "hw" >}}), which gives the status of all of the designs in the OpenTitan repository.

This document aims to mostly give a more defined structure to the process that is already followed.
Proper versioning of RTL designs is a complex topic.
This document proposes a sensible path forwards, but this may be revisited as we gain further experience and get more feedback.


## Life Stages (L)

The stages listed here are created to give insight into where a design is in its life from specification to silicon-ready sign-off.
At the moment, this is strictly limited to a hardware design, but could be expanded to other components of development within OpenTitan.
Transitions between these stages are decided by the Technical Committee via the [RFC process]({{< relref "doc/project/rfc_process" >}}).

The first life stage is **Specification**.
The proposed design is written up and submitted through the [RFC process]({{< relref "doc/project/rfc_process" >}}).
Depending on the complexity of the design and the guidance of the Technical Committee, it is possible a single design might require multiple RFCs.
For example, a first RFC for the rationale, feature list, and a rough overview; followed by a more detailed RFC to get approval for the draft technical specification.
As part of the specification process, the design author might reach out for feedback from a smaller group of reviewers while formulating an RFC proposal.
RFCs are always shared with the wider OpenTitan community prior to vote by the Technical Committee.
However, wherever there is potentially sensitive material from a future certification standpoint it should be passed through the security review team.
Once the specification has been shared with the OpenTitan audience and sufficient review has been completed, this phase is exited.

The next life stage is **Development**.
The hardware IP is being developed in GitHub, the specification is converted to Markdown, and design and verification planning is underway.
This is a long phase expected to last until a more formal review is requested for full completion sign-off.
When in Development phase, the stage tracking of the design and verification milestones are valid.
See those sections that follow for details there.
To exit this stage, a sign-off review must occur.
See the section on sign-off for details.

The final life stage is **Signed-Off**.
At this point, a design is frozen and not expected to be updated.
There are exceptions if post-sign-off bugs are found, in which case the stage returns to Development and the version number is not updated.
Feature requests towards a signed-off design requires review and approval by the Technical Committee.
Once accepted, it results in creating a new version and return a design to the appropriate life stage, based upon the size of the change.
See the _Versioning_ section of the document for more discussion.
Signed-off fully-functioning (read: not buggy) designs stay in the "Signed-Off" life stage as an available complete IP, with an associated revision ID.

There exists a [template for IP checklists](https://github.com/lowRISC/opentitan/blob/master/util/uvmdvgen/checklist.md.tpl).
The DIF stages use a separate, [software-specific checklist](https://github.com/lowRISC/opentitan/blob/master/doc/project/sw_checklist.md.tpl).
All the checklist items are listed in the [Sign-off Checklist]({{< relref "doc/project/checklist.md" >}}).

| **Stage** | **Name** | **Definition** |
| --- | --- | --- |
| L0 | Specification | Specification is being written, is in review process |
| L1 | Development | Design is in development in GitHub, possibly integrated in top level |
| L2 | Signed-Off | Design has been frozen at version number, signed-off, available for tapeout |

We may later evaluate adding a **Silicon Proven** stage, after deciding criteria for a tapeout to qualify as proven.


## Hardware Design Stages (D)

The following development milestones are for hardware peripheral designs, i.e. SystemVerilog RTL development.
They are similar to typical chip design milestones, but less rigid in the movement from one stage to the next.
The metric here is the quality bar and feature completeness of the design.

The first design stage is **Initial Work**.
This indicates the period of time between the Specification life stage and the RTL being functional enough to pass sanity checks.
The RTL is still in progress, registers being defined, etc.
Once the device has passed a basic sanity check, has the lint flow setup, has the registers completely defined, it has completed the Initial Work stage.

The second design stage is **Functional**.
In this stage, the design is functional but not complete.
Once all of the features in the specification are implemented, it has completed this stage.

The third design stage is **Feature Complete**.
In this phase, no changes are expected on the design except for bug fixes.
Once all bugs have fixed, lint and CDC violations cleaned up, the design moves into its final stage: **Design Complete**.

| **Stage** | **Name** | **Definition** |
| --- | --- | --- |
| D0 | Initial Work | RTL being developed, not functional |
| D1 | Functional | <ul> <li> Feature set finalized, spec complete <li> CSRs identified; RTL/DV/SW collateral generated <li> SW interface automation completed <li> Clock(s)/reset(s) connected to all sub modules <li> Lint run setup <li> Ports Frozen </ul> |
| D2 | Feature Complete | <ul> <li> Full Feature Complete: all features implemented.  <li> Feature frozen </ul> |
| D3 | Design Complete | <ul> <li> Lint/CDC clean, waivers reviewed <li> Design optimization for power and/or performance complete </ul> |

## Hardware Verification Stages (V)

The following development milestones are for hardware peripheral verification work.
They are similar to typical chip verification milestones, but less rigid in the movement from one stage to the next.
The metric here is the progress towards testing completion and proof of testing coverage.
The verification stages can be applied to simulation-based DV and formal property verification (FPV) approaches.

The first verification stage is **Initial Work**.
This indicates the period of time between the beginning of verification planning and the testbench up and running.
The testbench is still being created, scoreboards implemented, DV document and DV plan being written, nightly regressions running, etc.
Once the verification environment is available for writing tests, with a DV plan written including a testplan and a functional coverage plan, it has completed the Initial Work stage.

The second verification stage is **Under Test**.
In this stage, the verification environment is available but not all tests in the testplan are are completed and the coverpoints are not implemented.
Once all of the items in the DV plan are implemented, it exits this stage.

The third verification stage is **Testing Complete**.
In this phase, no changes are expected on the DV plan, no changes expected on the testbench, and no new tests are expected except to close coverage on the design.
Once all coverage metrics have been met, waivers checked, the verification moves into its final stage: **Verification Complete**.

**Stages for simulation-based DV**:

| **Stage** | **Name** | **Definition** |
| --- | --- | --- |
| V0 | Initial Work | Testbench being developed, not functional; DV plan being written; decided which methodology to use (sim-based DV, FPV, or both). |
| V1 | Under Test | <ul> <li> Documentation: <ul> <li> [DV document]({{< relref "doc/ug/dv_methodology#documentation" >}}) available, <li> [DV plan]({{< relref "doc/ug/dv_methodology#documentation" >}}) completed and reviewed <li> [functional coverage plan]({{< relref "doc/ug/dv_methodology#documentation" >}}) completed and reviewed </ul> <li> Testbench: <ul> <li> DUT instantiated with major interfaces hooked up <li> All available interface assertion monitors hooked up <li> X / unknown checks on DUT outputs added <li> Skeleton environment created with UVCs <li> TLM connections made from interface monitors to the scoreboard </ul> <li> Tests (written and passing): <ul> <li> Sanity test accessing basic functionality <li> CSR / mem test suite </ul> <li> Regressions: Sanity and nightly regression set up</ul> |
| V2 | Testing Complete | <ul> <li> Documentation: <ul> <li> DV document completely written </ul> <li> Design Issues: <ul> <li> all high priority bugs addressed <li> low priority bugs root-caused </ul> <li> Testbench: <ul> <li> all interfaces hooked up and exercised <li> all assertions written and enabled </ul> <li> UVM environment: fully developed with end-to-end checks in scoreboard <li> Tests (written and passing): all tests planned for in the DV plan  <li> Functional coverage (written): all covergroups planned for in the DV plan <li> Regression: all tests passing in nightly regression with multiple seeds (> 90%)  <li> Coverage: 90% code coverage across the board, 100% functional coverpoints covered and 75% crosses covered</ul></ul> |
| V3 | Verification Complete | <ul> <li> Design Issues: all bugs addressed <li> Tests (written and passing): all tests including newly added post-V2 tests (if any) <li> Regression: all tests with all seeds passing <li> Coverage: 100% code and 100% functional coverage with waivers </ul> </ul> |

**Stages for FPV approaches**:

| **Stage** | **Name** | **Definition** |
| --- | --- | --- |
| V0 | Initial Work | Testbench being developed, not functional; DV plan being written; decided which methodology to use (sim-based DV, FPV, or both). |
| V1 | Under Test | <ul> <li> Documentation: <ul> <li> [DV document]({{< relref "doc/ug/dv_methodology#documentation" >}}) available, [DV plan]({{< relref "doc/ug/dv_methodology#documentation" >}}) completed and reviewed </ul> <li> Testbench: <ul> <li> Formal testbench with DUT bound to assertion module(s) <li> All available interface assertion monitors hooked up <li> X / unknown assertions on DUT outputs added </ul> <li> Assertions (written and proven): <ul> <li> All functional properties identified and described in DV plan <li> Assertions for main functional path implemented and passing (sanity check)<li> Each input and each output is part of at least one assertion</ul> <li> Regressions: Sanity and nightly regression set up</ul> |
| V2 | Testing Complete | <ul> <li> Documentation: <ul> <li> DV document completely written </ul> <li> Design Issues: <ul> <li> all high priority bugs addressed <li> low priority bugs root-caused </ul> <li> Testbench: <ul> <li> all interfaces have assertions checking the protocol <li> all functional assertions written and enabled <li> assumptions for FPV specified and reviewed </ul> <li> Tests (written and passing): all tests planned for in the DV plan <li> Regression: 90% of properties proven in nightly regression <li> Coverage: 90% code coverage and 75% logic cone of influence (COI) coverage </ul> |
| V3 | Verification Complete | <ul> <li> Design Issues: all bugs addressed <li> Assertions (written and proven): all assertions including newly added post-V2 assertions (if any) <li> Regression: 100% of properties proven (with reviewed assumptions) <li> Coverage: 100% code coverage and 100% COI coverage</ul> |

## Device Interface Function Stages (S)

The following development stages are for [Device Interface Function (DIF)]({{< relref "doc/rm/device_interface_functions.md" >}}) work.
These milestones have a slightly different emphasis to the hardware design and verification milestones, because software is much easier to change if bugs are found.
The metric they are trying to capture is the stability and completeness of a low-level software interface to hardware design.
We are aiming to keep this process fairly lightweight in the early stages, and not significantly burdeonsome to the associated HW designer through all stages.

There are explicit checkpoints in these stages to ensure that DIF development does not overtake design and verification.

The first DIF stage is **Initial Work**.
This indicates the period of time between starting the software API, and it being complete enough for other software to start using it.
The exact API is still being defined.
Once the DIF is complete enough to cover all existing in-tree uses of the device, and has mock tests, it has completed the Initial Work stage.

The second stage is **Functional**.
In this stage, the DIF can be used for basic operations, but may not cover all the specified functionality of the device.
Once the DIF is complete enough to cover all the functionality of the device, in the way the hardware designer envisioned; is used for both DV testing; and can be used Tock, it has completed this stage.

The third stage is **Complete**.
In this stage, no changes to the interface are expected.
Once testing is complete, and we are satisfied that the interface will not change (except for bug fixes), the DIF moves into its final stage: **Stable**.

| **Stage** | **Name** | **Definition** |
| --- | --- | --- |
| S0 | Initial Work | Work has started on a DIF for the given IP block. |
| S1 | Functional | <ul> <li> DIF has been reviewed and merged <li> DIF is used by all in-tree device code <li> DIF has (mocked) unit tests <li> DIF has smoke test </ul> |
| S2 | Complete | <ul> <li> DIF API is now Complete <li> The respective IP block is feature complete (at least D2) <li> DIF matches HW designer's agreed IP block usage <li> DIF covers all specified functionality of the IP block <li> DIF is used for chip-level DV <li> DIF documented in IP documentation <li> DIF has initial Tock integration </ul> |
| S3 | Stable | <ul> <li> DIF API Reviewed and Stable <li> The respective IP block is at D3/V3 <li> DIF tested fully (DV + Unit tests, full functional coverage) <li> Complete and Stable Tock interface to DIF </ul> |

## Sign-off Review

At the end of the final design and verification phase, the IP block should be proposed to the Technical Committee as ready for sign-off.
This will be done by submitting an RFC (possibly following a suggested template).
The Technical Committee may decide to nominate individuals to evaluate the codebase and make a recommendation or may review directly.
Generally, this process would involve:

*   Specification and RTL are re-reviewed for readability, consistency, and code coverage standards
*   All design items are complete, reviewed against committed specification
*   All lint and CDC errors and warnings are waived, waivers reviewed
*   DV plan is re-reviewed for completeness
*   All test items are confirmed complete
*   All code coverage items are completed or waived
*   Performance requirements are reviewed, performance metrics met
*   Software interface (DIF) files are completed, tested, and signed off by software representative

The process will be refined by the Technical Committee as necessary.

## Indicating Stages and Making Transitions

Stages are indicated via a text file checked into the GitHub and thus transitions can be reviewed through the standard pull request process.
Transitions for Design and Verification stages are _self-nominated_ in the sense that the design or verification owner can modify the text file and submit a pull request (PR) to transition the stage.
In this manner other reviewers can challenge the transition in the standard pull request review process.
These transitions should be done in their own PR (i.e. not interspersed with other changes), and the PR summary and commit message should give any necessary detail on how the transition criteria have been met, as well as any other notes useful for a reviewer.

The content below shows the format of the project file that contains the stage information.
The file for a design named `name` should be placed under `hw/ip/name/data/name.prj.hjson`.
For example, `file: gpio.prj.hjson`:

```hjson
{
    name:               "gpio"
    version:            "1.0"
    life_stage:         "L1"
    design_stage:       "D2"
    verification_stage: "V1"
    dif_stage:          "S0"
    notes:              "information shown on the dashboard"
}
```

### Commit ID

When a design transitions from one stage to another, the project file can optionally provide a commit ID for the transition to be able to recreate the repository at the point of that transition.
This is optional for all transitions except for sign-off, where it is required.
The commit ID has its own entry in the project Hjson file, as shown below.

```hjson
{
    name:               "gpio"
    version:            "1.0"
    life_stage:         "L1"
    design_stage:       "D2"
    verification_stage: "V1"
    dif_stage:          "S0"
    commit_id:          "92e4298f8c2de268b2420a2c16939cd0784f1bf8"
    notes:              "information shown on the dashboard"
}
```

### Other optional fields

Additionally, the tool that generates the dashboard accepts the following optional fields: the design specification, the DV document and the checklist.
They are set as partial paths (reference relative to the top of the repository) to the respective documents as shown below.
They are converted to complete URLs in the generated dashboard.

```hjson
{
    design_spec:  "hw/ip/gpio/doc"
    dv_doc:      "hw/ip/gpio/doc/dv"
    hw_checklist: "hw/ip/gpio/doc/checklist"
    sw_checklist: "sw/device/lib/dif/dif_gpio"
}
```

## Versioning

The _Version_ of a design element indicates its progress towards its _final feature set for expected product_.
Typically all designs are expected to simply be in 1.0 version, but there are reasons for exceptions.
Designs which have a specification that defines an _intermediate goal_ are indicated as < 1.0 version.
There are many times where this is useful: when the intermediate goal is a beneficial subset of functionality to enable other development; when the final feature set is not known but a sufficient set is ready for development; when the final feature set is postponed until a future date, but owners are keen to get the design started; etc.
In essence, the sub-1.0 designation indicates that it is understood that the stage metrics are temporary pending a final feature set.
Rarely will a sub-1.0 design be taken past Feature Complete and Testing Complete stages.
An exception is a proof of concept to show what a sign-off process looks like for a design that has modifications expected in the future.
This was the case with public launch, where we took five designs to completion to test out the sign-off process, the verification methodology, and the checklist system.
In several of these cases, the feature set was not final product complete.

Once a design has completed all stages for a product feature set, the sign-off process intends to end all development for that design.
Its Life Stage should transition to sign-off after the review process, and no more modifications should be made.
The commit ID of the version that was signed off is recorded in the `commit_id` field of the `.prj.hjson` file.

After sign-off, three events could cause a change.

* Possibility 1: If a bug is found in top-level testing, software development, etc., the design should stay in its current revision (assumedly 1.0) but revert in design and/or verification staging until the bug is fixed and a new sign-off process occurs, followed by a new tag to replace the previous one.
* Possibility 2: if a small collection of new features are requested, a new version increment of 0.1 would be created, and the design and verification stages would be reset.
The expectation is that this would create its life as a newly tracked revision number, while the previous (assumedly 1.0) version retains its status.
* Possibility 3: if enough new features are requested to greatly change the spirit of the design, a new version increment of 1.0 would be created in a fashion similar to above.
This would require a new RFC process, and thus the Life Stage would start again as L0 - Specification.

### Multiple versions of a design

Over the course of the project, designs may *regress* from signed-off to an earlier stage when new features are added.
When regressing a signed-off design, the old signed-off version should remain in the project file as a retrievable version.
This is indicated as two versions as shown in this example.

```hjson
{
    name:                   "uart",
    revisions: [
      {
        version:            "1.0",
        life_stage:         "L2",
        design_stage:       "D3",
        verification_stage: "V3",
        dif_stage:          "S0",
        commit_id:          "92e4298f8c2de268b2420a2c16939cd0784f1bf8",
        notes:              ""
      }
      {
        version:            "1.1",
        life_stage:         "L1",
        design_stage:       "D2",
        verification_stage: "V2",
        dif_stage:          "S0",
        commit_id:          "f3039d7006ca8ebd45ae0b52b22864983876175d",
        notes:              "Rolled back to D2 as the register module is updated",
      }
    ]
}
```

One may choose to commemorate a non-signed-off version of a design if it reached enough maturity to be a useful version to checkpoint before regressing.
In this case the version number should also be incremented.

No hard rules for version numbering are mandated at this stage.
The subject will be revisited as we get closer to locking down the design to take it to a silicon implementation milestone.

## Reporting of Stages

The stages are reported externally via a script-generated table exposed on the external website.
This status is a summary of all `prj.hjson` files of all designs in the system, with multiple lines where there are multiple versions.
The link to that table is [here]({{< relref "hw" >}}).
