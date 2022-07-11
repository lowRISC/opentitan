---
title: "Designing Hardware"
---

This document aims to clarify how to get started with a hardware design within the OpenTitan project.
Design in this context nominally refers to a new [Comportable Peripheral]({{< relref "../rm/comportability_specification" >}}) but can include high level constructs like device reset strategy, etc.
This is primarily aimed at creating a new design from scratch, but has sections on how to contribute to an existing design.
It is targeted to RTL designers to give clarity on the typical process for declaring features, finding others to review, etc.
We aim for a healthy balance between adding clarity while not over prescribing rules and process.
There are times when a more regimented approach is warranted, and those will be highlighted in this document.
Feedback and improvements are welcome.


## Stages of a Design

The life stages of a design within the OpenTitan are described in the [Hardware Development Stages]({{< relref "doc/project/development_stages.md" >}}) document.
This separates the life of the design into three broad stages: Specification, In Development, and Signed off.
This document attempts to give guidance on how to get going with the first stage and have a smooth transition into the Development stage.
They are not hard and fast rules but methods we have seen work well in the project.


## Concept and RFC

The concept of a design might come from a variety of inspirations: a known required module already slated for future product need; a new design needed for a proposed product feature; an inspiration worthy of being discussed more broadly; perhaps even a new approach to an existing design (higher performance; more secure; etc).
Regardless of the inspiration, the concept should be codified into a brief proposal with basic features.
This is as opposed to minor modification proposals to an existing design, which can be handled as a GitHub pull request or issue filing associated with the existing design.
This proposal should be in **Google Doc** medium for agile review capability.
Ideally this proposal document would be created in the Team Drive, but if the author does not have access to the team drive, they can share a privately-created document.

Design proposals should follow the recommended [RFC (Request for Comment)]({{< relref "../project/rfc_process.md" >}}) process, which handles all such proposals.
If the RFC potentially contains information that could be certification-sensitive (guidance to be shared), send a note to security@opentitan.org first for feedback.
The OpenTitan Technical Committee may be able to suggest other collaborators to help with early stage review.

An example of a canonical RFC will be provided *here* (TODO).


## Detailed Specification

Once past initial review of the feature set and high level description, as well as potential security review, the full detailed specification should be completed, still in Google Doc form.
The content, form, and format are discussed in the [design methodology]({{< relref "design.md" >}}) and [documentation methodology]({{< relref "../rm/markdown_usage_style.md" >}}) guides.
The outcome of this process should be a specification that is ready for further detailed review by other project members.
The content and the status of the proposal can be shared with the team.

An example of a canonical detailed specification is the pinmux specification which can be found in the TeamDrive under TechnicalSpecifications --> deprecated, for those that have access to that resource.
(Google Docs that have been converted into Markdown on GitHub are archived here).

Note that when developing OpenTitan security IP, designers should follow the [Secure Hardware Design Guidelines]({{< relref "doc/security/implementation_guidelines/hardware" >}}).

## Specification Publication

Once the specification is published to the wider team, the author(s) need to address input, comments, questions, etc., continuing to hone the proposal.
Other team members should also feel empowered to help address these questions and feedback.
It is acceptable to keep an unanswered-questions section of the document and move forward where there is agreement.


## Initial Skeleton Design

In parallel with publication and review of the specification, the initial skeleton design can commence.
There are many ways to get past this "big bang" of necessary implementation and get it through eventual code review.
One recommended method is as follows:
* Start with a skeleton that includes a complete or near-complete definition of the register content in Hjson format
* Combine with a basic Markdown including that file
* Combine with an IP-top-level Verilog module that instantiates the auto-generated register model (see the [register tool documentation]({{< relref "../rm/register_tool" >}})), includes all of the known IP-level IO, clocking and reset.

This is not mandatory but allows the basics to come in first with one review, and the full custom details over time.
Regardless the first check-ins of course should be compilable, syntax error free,
[coding style guide](https://github.com/lowRISC/style-guides/blob/master/VerilogCodingStyle.md)
friendly, [Comportability]({{< relref "../rm/comportability_specification" >}}) equivalent, etc., as indicated by the [design methodology user guide]({{< relref "design.md" >}}).

A good example of an initial skeleton design can be seen in [Pull Request #166](https://github.com/lowRISC/opentitan/pull/166) for the AES module.

As part of the GitHub filing process, the Google Doc specification must be converted into a Markdown specification.
(Tip: there are Google Doc add-ons that can convert the specification into Markdown format).
Once this is completed, any specifications on the Team Drive should be moved to the deprecated section of the drive, with a link at the top indicating that the document is for historical purposes only.
This applies only for those specifications that originated on the Drive.


## Full Design

As the design develops within the OpenTitan repository, it transitions into "D0", "D1", etc., [design stages]({{< relref "doc/project/development_stages.md" >}}) and will be eventually plugged into the top level.
Following the recommended best practices for digestible pull requests suggests that continuing to stage the design from the initial skeleton into the full featured design is a good way to make steady progress without over-burdening the reviewers.

## Top Level Inclusion

Once an IP block is ready, it can be included in the top-level design.
To do so, follow the steps below.

* Get an agreement on if and how the IP block should be integrated.
* Ensure that the IP block is of acceptable quality.
* Ensure that the top level simulation is not adversely affected.
* Open a Pull Request with the necessary code changes.

If it is not clear on how to proceed, feel free to file an issue requesting assistance.

## Change of Interrupts

Changing the interrupts of an IP block needs some extra work in addition to the RTL change.
1. If a DV environment exists, its testbench (`tb.sv`) will need the ports connected.
1. If the IP block has been instantiated in a top-level, that top-level will need re-generating to include the new ports.
1. The auto-generated DIFs will need re-generating.
1. The PLIC test should also be updated.

Item 1 is reasonably self-explanatory.
The sections below show how to do items 2-4.

### Update TOP

```console
$ make -C hw top
```

After you revise the IP `.hjson`, IP top module, IP register interface, and DV testbench `tb.sv`, you can re-generate top-levels with the command above.
This reads the `.hjson` file and updates the interrupt signal and re-generates the PLIC module if needed.

### New DIF

Unfortunately, re-generating TOP does not resolve everything.
If the interrupt names are changed or new interrupts are introduced, the DIF for the IP block should be re-generated.

```console
$ ./util/make_new_dif.py --mode=regen --only=autogen
```

The command above updates the DIF (auto-generated part) under `sw/device/lib/dif/`.

If DIF for the IP block already uses the interrupt enums inside, you need to manually revise the reference.
In most cases, the interrupt name is `kDif`, followed by the IP name in PascalCase (e.g `SpiDevice`), then `Irq`, then the interrupt name in PascalCase (e.g. `RxFull`).
For example, `kDifSpiDeviceIrqRxFull`.
To refer to an interrupt in the top-level PLIC enum, the format is `kTopEarlgreyPlicIrqId`, followed by the IP name in PascalCase, then the interrupt name in PascalCase.
For example, `kTopEarlgreyPlicIrqIdSpiDeviceRxFull`.

### PLIC Unittest

If the number of interrupts has changed, you need to revise the SW unit test manually.

Open `sw/device/lib/dif/dif_rv_plic_unittest.cc` and change the `RV_PLIC_PARAM_NUM_SRC` macro to the current interrupt number.
Then, find `RV_PLIC_IE0_*_REG_OFFSET`, `RV_PLIC_IP0_*_REG_OFFSET` and revise the Bit value or add lines below if new `IE`, `IP` registers are added.
