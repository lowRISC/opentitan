---
title: "Design Methodology within OpenTitan"
---

The design methodology within OpenTitan combines the challenges of industry-strength design methodologies with open source ambitions.
When in conflict, quality must win, and thus we aim to create a final design product that is equal to the quality required from a full production silicon chip tapeout.

## Language and Tool Selection

Starting with the language, the strategy is to use the SystemVerilog language, restricted to a feature set described by the lowRISC
[Verilog Style Guide](https://github.com/lowRISC/style-guides/blob/master/VerilogCodingStyle.md).
All IP should be developed and delivered under the feature set described by this style guide.
Inconsistencies or lack of clarity within the style guide should be solved by filing and helping close an issue on the style guide in the
[lowrisc/style-guides GitHub repo](https://github.com/lowRISC/style-guides).

For professional tooling, the team has chosen several industry-grade tools for its design signoff process.
Wherever possible we attempt to remain tool-agnostic, but we must choose a selection of tools as our ground truth for our own confidence of signoff-level assurances.
As a project we promote other open source methodologies and work towards a future where these are signoff-grade as well.
The discussions on how the design tools are used and which ones are chosen are given below in separate sections.

## Comportability and the Importance of Architectural Conformity

The OpenTitan program is adopting a design methodology aimed at unifying as much as possible the interfaces between individual designs and the rest of the SOC.
These are detailed in the [Comportability Specification]({{< relref "doc/rm/comportability_specification" >}}).
This document details how peripheral IP interconnects with the embedded processor, the chip IO, other designs, and the security infrastructure within the SOC.
Not all of the details are complete at this time, but will be tracked and finalized within that specification.

TODO: briefly discuss key architectural decisions, and how we came to the conclusion, with pointers to more thorough documentation. Some candidates:
*   Processor/RISC-V strategy
*   Bus strategy
*   Reset strategy

## Defining Design Complete: stages and tracking

Designs within the OpenTitan project come in a variety of completion status levels.
Some designs are "tapeout ready" while others are still a work in progress.
Understanding the status of a design is important to gauge the confidence in its advertised feature set.
To that end, we've designated a spectrum of design stages in the [OpenTitan Hardware Development Stages]({{< relref "doc/project/development_stages.md" >}}) document.
This document defines the design stages and references where one can find the current status of each of the designs in the repository.

## Documentation

Documentation is a critical part of any design methodology.
Within the OpenTitan project there are two important tooling components to efficient and effective documentation.

The first is the [Hugo](https://gohugo.io) tool, which converts an annotated Markdown file into a rendered HTML file (including this document).
See the linked manual for information about the annotations and how to use it to create enhanced auto-generated additions to standard Markdown files.
To automate the process a script [build_docs.py]({{< relref "doc/ug/documentation" >}}) is provided for generating the documentation.

The second is the [reggen]({{< relref "doc/rm/register_tool" >}}) register tool that helps define the methodology and description language for specifying hardware registers.
These descriptions are used by `build_docs.py` to ensure that the technical specifications for the IP are accurate and up to date with the hardware being built.

Underlying and critical to this tooling is the human-written content that goes into the source Markdown and register descriptions.
Clarity and consistency is key.
See the [Markdown Style Guide]({{< relref "doc/rm/markdown_usage_style.md" >}}) for details and guidelines on the description language.

## Usage of Register Tool

One design element that is prime for consistent definitions and usages is in the area of register definitions.
Registers are critical, being at the intersection of hardware and software, where uniformity can reduce confusion and increase re-usability.
The [register tool]({{< relref "doc/rm/register_tool" >}}) used within OpenTitan is custom for the project's needs, but flexible to add new features as they arise.
It attempts to stay lightweight yet solve most of the needs in this space.
The description language (using HJSON format) described within that specification also details other features described in the
[Comportability Specification]({{< relref "doc/rm/comportability_specification" >}}).

## Linting Methodology

Linting is a productivity tool for designers to quickly find typos and bugs at the time when the RTL is written.
Capturing fast and efficient feedback on syntactic and semantic (as well as style) content early in the process proves to be useful for high quality as well as consistent usage of the language.
Running lint is especially useful with SystemVerilog, a weakly-typed language, unlike more modern hardware description languages.
Running lint is faster than running a simulation.

### Sign-off Linting using AscentLint

For sign-off we have standardized on the [AscentLint](https://www.realintent.com/rtl-linting-ascent-lint/) tool from RealIntent for this task due to its fast run-times and comprehensive set of rules that provide concise error and warning messages.

The sign-off lint flow leverages a new lint rule policy named _"lowRISC Lint Rules"_ that has been tailored towards our [Verilog Style Guide](https://github.com/lowRISC/style-guides/blob/master/VerilogCodingStyle.md).
The lint flow run scripts and waiver files are available in the GitHub repository of this project, but due to the proprietary nature of the lint rules and their configuration, the _"lowRISC Lint Rules"_ lint policy file can not be publicly provided.
However, the _"lowRISC Lint Rules"_ are available as part of the default policies in AscentLint release 2019.A.p3 or newer (as `LRLR-v1.0.policy`).
This enables designers that have access to this tool to run the lint flow provided locally on their premises.

For developers of design IP, the recommendation is to set up the AscentLint flow for their IP as described in the [Lint Flow README]({{< relref "hw/lint/doc/README.md" >}}), and use the flow locally to close the errors and warnings.
Linting errors and warnings can be closed by fixing the code in question (preferred), or waiving the error.
These waivers have to be reviewed as part of the Pull Request review process.

For other developers that do not have access to this tool, the recommendation is to run their code through whatever linting tool they have available at their disposal before creating a design Pull Request (e.g. the open source Verilator tool).
Once the Pull Request has been merged, these developers can then work with the maintainers to enable sign-off linting on their design.

Note that all designs with enabled AscentLint targets will be run through the tool in eight-hour intervals and the results are published as part of the tool dashboards on the [hardware IP overview page](https://docs.opentitan.org/hw), enabling designers to close the lint errors and warnings even if they cannot run the sign-off tool locally.

Goals for linting closure per design milestone are given in the [OpenTitan Development Stages]({{< relref "doc/project/development_stages" >}}) document.

### Style Linting using Verible

In order to complement the sign-off lint flow explained above, we also leverage the Verible style linter, which captures different aspects of the code and detects style elements that are in violation with our [Verilog Style Guide](https://github.com/lowRISC/style-guides/blob/master/VerilogCodingStyle.md).

The tool is open source and freely available on the [Verible GitHub page](https://github.com/google/verible/).
Hence, the recommendation for IP designers is to install the tool as described [here]({{< relref "doc/ug/install_instructions" >}}) and in the [Lint Flow README]({{< relref "hw/lint/doc/README.md" >}}), and use the flow locally to close the errors and warnings.

Note, however, that we do not have a waiver strategy in place yet.
Until that is the case, the recommendation is to use good judgment and fix all violations that can be addressed without too much effort.

Similarly to the sign-off flow, all designs with enabled Verible lint targets will be run through the tool in eight-hour intervals and the results are published as part of the tool dashboards on the [hardware IP overview page](https://docs.opentitan.org/hw), enabling designers to close the lint errors and warnings even if they cannot run the sign-off tool locally.

## Assertion Methodology

The creation and maintenance of assertions within RTL design code is an essential way to get feedback if a design is being used improperly.
Common examples include asserting that a full FIFO should never be written to, a state machine doesn't receive an input while in a particular state, or two signals should remain mutually exclusive.
Often these will eventually result in a downstream error (incorrect data, bus collisions, etc.), but early feedback at the first point of inconsistency gives designers and verifiers alike fast access to easier debug.

Within OpenTitan we attempt to maintain uniformity in assertion style and syntax using SystemVerilog Assertions and a list of common macros.
An overview of the included macros and how to use them is given in this
[Design Assertion README file]({{< relref "hw/formal/README.md" >}}).
This document also describes how to formally verify assertions using
[JasperGold](https://www.cadence.com/content/cadence-www/global/en_US/home/tools/system-design-and-verification/formal-and-static-verification/jasper-gold-verification-platform/formal-property-verification-app.html)
from the company Cadence.

## CDC Methodology

Logic designs that have signals that cross from one clock domain to another unrelated clock domain are notorious for introducing hard to debug problems.
The reason is that design verification, with its constant and idealized timing relationships on signals, does not represent the variability and uncertainty of real world systems.
For this reason, maintaining a robust Clock Domain Crossing verification strategy ("CDC methodology") is critical to the success of any multi-clock design.

Our general strategy is threefold:
maintain a list of proven domain crossing submodules;
enforce the usage of these submodules;
use a production-worthy tool to check all signals within the design conform to correct crossing rules.
The *CDC Methodology document* (TODO:Coming Soon) gives details on the submodules and explains more rationale for the designs chosen.

The tool chosen for this program is not finalized.
We will choose a sign-off-grade CDC checking tool that provides the features needed for CDC assurance.
It is understandable that not all partner members will have access to the tool.
Once chosen, the project will use it as its sign-off tool, and results will be shared in some form (TODO: final decision).
CDC checking errors can be closed by fixing the code in question (preferred), or waiving the error.
CDC waivers should be reviewed as part of the Pull Request review process.
Details on how to run the tool will be provided once the decision has been finalized.

The team will standardize on a suite of clock-crossing modules that can be used for most multi-clock designs.
Many of those will be documented in the `hw/ip/prim/doc` directory.

Similar to the linting tool, due to the proprietary nature of the CDC tool, it is possible that not all content towards running the tool will be checked in in the open source repository.
For those items, we will work with the tool provider to allow other partners to also use the tool.
When this methodology is finalized the details will be given here. (TODO)

## DFT

Design For Testability is another critical part of any design methodology.
It is the preparation of a design for a successful manufacturing test regime.
This includes, but is not limited to, the ability to use scan chains for testing digital logic;
the optimization of design logic to allow maximum access of test logic for fault coverage;
the ability to observe and control memory cells and other storage macros;
the control of analog designs and other items that are often outside the reach of test logic;
built in self test (BIST) insertion for logic and memories.
In this context, our primary concern at this stage is what impact does this have on the RTL that makes up the IP in our library.

DFT in OpenTitan is particularly interesting for two primary reasons:
the RTL in the OpenTitan repository is targeted towards an FPGA implementation, but must be prepared for a silicon implementation
(see the FPGA vs Silicon discussion later in this document);
the whole purpose of a DFT methodology is full and efficient access to all logic and storage content,
while the whole purpose of a security microcontroller is restricting access to private secured information.
In light of the latter dilemma, special care must be taken in a security design to ensure DFT has access at only the appropriate times, but not while in use in production.

At this time the DFT methodology for OpenTitan is not finalized.
The expectation is that the RTL collateral will undergo a DFT introduction -
likely with the propagation of such signals as `testmode`, `scanmode`, `bistmode`, etc -
at a stage before final project completion.
At this point there are a few references to such signals but they are not yet built into a coherent whole.
At that future time the DFT considerations will be fully documented and carried out throughout all IP.

## Generated Code

The OpenTitan project contains a lot of generated code through a variety of methods.
Most modern SystemVerilog-based projects work around the weaknesses in the language in such a way.
But our first goal is to take full advantage of the language as much as possible, and only resort to generated code where necessary.

At the moment, all generated code is checked in with the source files.
The pros and cons of this decision are still being discussed, and the decision may be reversed, to be replaced with an over-arching build-all script to prepare a final design as source files changed.
Until that time, all generated files (see for example the output files from the
[register generation tool]({{< relref "doc/rm/register_tool" >}}))
are checked in.
There is an over-arching build file in the repository under `hw/Makefile` that builds all of the `regtool` content.
This is used by an Azure Pipelines pre-submit check script to ensure that the source files produce a generated file that is identical to the one being submitted.

## Getting Started with a Design

The process for getting started with a design involves many steps, including getting clarity on its purpose, its feature set, authorship, documentation, etc.
These are discussed in the [Getting Started with a Design]({{< relref "getting_started_design.md" >}}) document.

## FPGA vs Silicon

One output of the OpenTitan project will be silicon instantiations of hardware functionality described in this open source repository.
The RTL repository defines design functionality at a level satisfactory to prove the hardware and software functionality in an FPGA (see [user guides]({{< relref "doc/ug" >}})).
That level is so-called "tapeout ready".
Once the project reaches that milestone, the team will work with a vendor or vendors to ensure a trustworthy, industry-quality, fully functional OpenTitan chip is manufactured.

It is important that any IP that *can* be open *is* open to ensure maximal trustworthiness and transparency of the final devices.

To that end, OpenTitan will define compliance collateral that ensures correctness - that the FPGA and the eventual silicon work the same.
Due to fundamental economic and technical limitations, there may, and likely will, be differences between these incarnations.
Some examples include the following:

* Silicon versions by definition use different technologies for fundamental vendor collateral, including memories, analog designs, pads, and standard cells.
* Some of the silicon collateral is beyond the so-called "foundry boundry" and not available for open sourcing.

Some IP blocks will undergo hardening of designs to protect them against physical attack to meet security and certification requirements.
Some of this hardening, for instance in fuses, may be of necessity proprietary.
These changes will not impact the functionality of the design, but are described in processes unique to an ASIC flow vs. the emulated flow of an FPGA.

Even with these differences, the overriding objective is compliance equivalence between the FPGA and silicon versions.
This may require instantiation-specific differences in the software implementation of the compliance suite.

Consider the embedded flash macro.
This design is highly dependent upon the silicon technology node.
In the open source repository, the embedded flash macro is emulated by a model that approximates the timing one would typically find in silicon.
It lacks the myriad timing knobs and configuration points required to control the final flash block.
This necessitates that the compliance suite will have initialization sections for flash that differ between FPGA and silicon.

We consider this demonstration of "security equivalence" to be an open, unsolved problem and committed to clearly delimiting any differences in the compliance suite implementation.
