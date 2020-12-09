---
title: "Design Verification Methodology within OpenTitan"
---

Verification within OpenTitan combines the challenges of industry-strength verification methodologies with open source ambitions.
When in conflict, quality must win, and thus we aim to create a verification product that is equal to the quality required from a full production silicon chip tapeout.

For the purpose of this document, each design (IPs or the full chip) verified within the OpenTitan project will be referred to as the 'design under test' or 'DUT' ('RTL' or 'design' may be used interchangeably as well), and the design verification as 'DV'.

## Language and Tool Selection

The following are the key techniques used to perform design verification within OpenTitan:

*  Dynamic simulations of the design with functional tests
*  Formal Property Verification (FPV)

For running dynamic simulations, the strategy is to use the [UVM1.2 methodology](https://www.accellera.org/downloads/standards/uvm) on top of a foundation of SystemVerilog based verification to develop constrained-random functional tests.
Each DUT will include within the repository, a UVM testbench, a [DV plan]({{< relref "doc/ug/dv_methodology/index.md#dv-plan" >}}), overall [DV document]({{< relref "doc/ug/dv_methodology/index.md#dv-document" >}}), a suite of tests, and a method to build, run tests and report the current status.
For FPV, some DUTs may also include an SV testbench along with design properties captured in the SystemVerilog Assertions (SVA) language.
As the project is still in development, the current status will not be completed for all IP, but that is the ultimate goal.
See discussion below on tracking progress.

For professional tooling, the team has chosen [Synopsys' VCS](https://www.synopsys.com/verification/simulation/vcs.html) as the simulator of choice with respect to the tracking of verification completeness and [JasperGold](https://www.cadence.com/content/cadence-www/global/en_US/home/tools/system-design-and-verification/formal-and-static-verification/jasper-gold-verification-platform.html) for FPV.
Wherever possible we attempt to remain tool-agnostic, but we must choose a simulator as our ground truth for our own confidence of signoff-level assurances.
Likewise, for FPV, [Synopsys VC Formal](https://www.synopsys.com/verification/static-and-formal-verification/vc-formal.html) is also supported within the same flow, and can be used by those with access to VC Formal licenses.
At this time there is also some support for Cadence's Xcelium, for those organizations which have few Synopsys VCS licenses.
However support is not as mature as for VCS, which remains the tool for signoff.
Furthermore, as a project we promote other open source verification methodologies - Verilator, Yosys, cocoTB, etc - and work towards a future where these are signoff-grade.
The discussions on how those are used within the program are carried out in a different user guide.

## Defining Verification Complete: Stages and Checklists

Verification within the OpenTitan project comes in a variety of completion status levels.
Some designs are "tapeout ready" while others are still a work in progress.
Understanding the status of verification is important to gauge the confidence in the design's advertised feature set.
To that end, we've designated a spectrum of design and verification stages in the  [OpenTitan Hardware Development Stages]({{< relref "doc/project/development_stages.md" >}}) document.
It defines the verification stages and references where one can find the current verification status of each of the designs in the repository.
Splitting the effort in such a way enables the team to pace the development effort and allows the progress to be in lock-step with the design stages.
The list of tasks that are required to be completed to enable the effort to transition from one stage to the next is defined in the [checklists]({{< relref "doc/project/checklist" >}}) document.
Verification is said to be complete when the checklist items for all stages are marked as done.
We will explain some of the key items in those checklists in the remainder of this document.

## Documentation

DV effort needs to be well documented to not only provide a detailed description of what tests are being planned, but also how the overall effort is strategized and implemented.
The first is provided by the **DV plan** document and the second, by the **DV document**.
The [**project status**]({{< relref "doc/project/development_stages.md#indicating-stages-and-making-transitions" >}}) document tracks to progression of the effort through the stages.

In addition to these documents, a nightly **regression dashboard** tabulating the test and coverage results will provide ability to track progress towards completion of the verification stages.

To effectively document all these pieces, there are some key tooling components which are also discussed briefly below.

### DV plan

A DV plan consist of two parts a testplan that captures at a high level, a list of tests that are being planned to verify all design features listed in the design specification.
A functional coverage plan that captures at high level a list of functional coverage points and coverage crosses needed to verify that the features listed in the design specification is tested by the list of tests.
the DV plan is written in Hjson format and is made available in the corresponding `data` directory of each DUT

The Hjson schema enables this information to be human-writable and machine-parsable, which facilitates an automated and documentation-driven DV effort.
The complete DV plan is parsed into a data structure that serves the following purposes:

*  Provide the ability to insert the testplan and coverage plan as tables into the DV document itself, so that all of the required information is in one place
*  Annotate the nightly regression results to allow us to track our progress towards executing the testplan and coverage collection
  *  this feature is not yet available and is [under active development](#pending-work-items)

The [testplanner]({{< relref "util/dvsim/testplanner/README.md" >}}) tool provides some additional information on the Hjson DV plan anatomy and some of the features and constructs supported.
The [build_docs]({{< relref "README.md#documentation" >}}) tool works in conjunction with the `testplanner` tool to enable its insertion into the DV document as a table.

### DV document

The DV document contains the DV plan and additionally it captures the overall strategy, intent, the testbench block diagram, a list of interfaces / agents, VIPs, reference models, the functional coverage model, assertions and checkers. It also covers FPV goals, if applicable.
This is written in [Markdown]({{< relref "doc/rm/markdown_usage_style" >}}) and is made available in the corresponding `doc` directory of each DUT.

A [template]({{< relref "hw/dv/doc/dv_doc_template" >}}) for the DV documentation as well as the testbench block diagram in the OpenTitan team drive  (under the 'design verification' directory) are available to help get started.

### Regression Dashboard

The DV document provides a link to the latest [nightly](#nightly) regression and coverage results dashboard uploaded to the web server.
This dashboard contains information in a tabulated format mapping the written tests to planned tests (in the DV plan) to provide ability to track progress towards executing the DV plan.
**This feature is currently not yet available and is under active development.**

## Automation

We rely on automation wherever possible, to avoid doing repetitive tasks manually.
With this in mind, there are three key areas where the whole testbench, or part of it is auto-generated.
These are described below.

### Initial UVM Testbench Generation

As is the case with design, we strive for conformity in our verification efforts as well.
The motivation for this is not just aesthetics, but also to reap the advantages of [code reuse](#code-reuse), which we rely heavily on.
To help achieve this, we provide a verification starter tool-kit called [uvmdvgen]({{< relref "util/uvmdvgen/README.md" >}}).
It can be used to completely auto-generate the complete initial DV enviroment for a new DUT, including the [documentation](#documentation) pieces (DV plan as well as DV document), the complete UVM environment including the testbench, to the collaterals for building and running tests along with some common tests.
This significantly helps reduce the development time.
It can also be used to auto-generate the initial skeleton source code for building a new reusable verification component for an interface (a complete UVM agent).

### UVM Register Abstraction Layer (RAL) Model

The UVM RAL model for DUTs containing CSRs is auto-generated using the [reggen]({{< relref "util/reggen/README.md" >}}) tool.
The specification for capturing the CSRs in the Hjson format can be found in the [Register Tool]({{< relref "doc/rm/register_tool" >}}) documentation.
We currently check-in the auto-generated UVM RAL model along with our UVM testbench code and rely on CI checks for consistency.
In future, we may move to a flow where it is not checked into the repository, but auto-generated on-the-fly as a part of the simulation.

### Testbench Automation

For a parameterized DUT that may possibly have multiple flavors instantiated in the chip, it would be prohibitively difficult to manually maintain the DV testbenches for all those flavors.
To cater to this, we develop a generic UVM testbench and rely on custom tooling to auto-generate the specific parameter sets that are required to undergo the full verification till signoff.
<!-- TODO: have this point to TLUL DV document -->
An effort of this sort is planned for verifying the [TileLink XBAR]({{< relref "hw/ip/tlul/doc" >}}).

## Code Reuse

SystemVerilog / UVM is structured to make code highly reusable across different benches.
To that end, several commonly used verification infrastructure pieces are provided to aid the testbench development, which are discussed below.

### DV Base Library

We provide an elementary scaffolding / base layer for constructing UVM testbenches via a [DV base library]({{< relref "hw/dv/sv/dv_lib/README" >}}) of classes to help us get off the ground quickly.
Most, if not all testbenches in OpenTitan (whether developed for a comportable IP or not) extend from this library, which provides a common set of features.
A UVM testbench feature (stimulus / sequence, checking logic or functional coverage element) that is generic enough to be applicable for use in all testbenches is a valid candidate to be added to the DV base library.
By doing so, we improve synergies across our testbenches and reduce the overall development effort & time to market.
The features are discussed in more detail in the document referenced above.
The actual UVM testbenches for some of the IPs extend from this library as the final layer.

### Comportable IP DV Library

Defining a common ground to develop all OpenTitan IPs as described in the [Comportable IP specification]({{< relref "doc/rm/comportability_specification" >}}) provides us an excellent path to maximize code reuse and shorten the testbench development time even further.
In view of that, we provide the [Comportable IP DV library]({{< relref "hw/dv/sv/cip_lib/doc" >}}) of classes, which themselves extend from DV base library to form the second layer.
These provide a common set of DV features that are specific to Comportable IPs.
The actual UVM testbenches for the Comportable IPs extend from this library as the third and the final layer.

### Common Verification Components

In addition to the above library of classes, there are several common plug-and-play verification compoments (a.k.a. universal verification components or UVCs) provided for use in testbenches at `hw/dv/sv` location.
A few examples of these are as follows:

*  [Common interfaces]({{< relref "hw/dv/sv/common_ifs" >}})
*  [DV utilities]({{< relref "hw/dv/sv/dv_utils/README" >}})
*  [CSR utilities]({{< relref "hw/dv/sv/csr_utils/README" >}})
*  [Device memory model]({{< relref "hw/dv/sv/mem_model/README" >}})
*  Interface agents
  *  [TileLink agent]({{< relref "hw/dv/sv/tl_agent/README" >}})
  *  [UART agent]({{< relref "hw/dv/sv/uart_agent/README" >}})

This is not an exhaustive list since we are still actively developing and adding more such components as we speak.
Please navigate to the above code location to find more sure UVCs.

## DV Efforts in OpenTitan

The overall OpenTitan DV effort is spread across 3 tiers:

*  IP level DV
*  Core (Ibex) level DV
*  Chip level DV

### IP Level DV

IP level DV testbenches are small and provide fine grained control of stimulus and corner case generation.
Tests at this level run relatively quickly and development cycles are shorter.
Coverage closure is more intensive since there are typically no pre-verified sub-modules.
To achieve our coverage goals, we take a constrained random approach to generate the stimulus.
The DV environment models the behavior of the DUT more closely to perform checks (typically within the scoreboard) independently of the stimulus.
In some IPs (specifically the ones that provide cryptographic functions), we also employ the use of open source third party C libraries as reference models to check the behavior of the DUT through DPI-C calls.

Each of the IP level DV environments are described in further detail within their own [DV document](#dv-document).
To find all of them, please navigate to this [landing page]({{< relref "hw" >}}).
The [UART DV document]({{< relref "hw/ip/uart/doc/dv" >}}) documentation which can be found there can be used as an example / reference.

### Core Ibex Level DV

The RISC-V CPU core Ibex used in OpenTitan has its own DV testbench and it is verified to full coverage closure.
Please see the [Ibex DV documentumentation](https://github.com/lowRISC/opentitan/blob/master/hw/vendor/lowrisc_ibex/doc/verification.rst) for more details.

### Chip Level DV

The chip level DV effort is aimed at ensuring that all of the IPs are integrated correctly into the chip.
For IPs that are pre-verified sub-modules, we perform [integration testing](#integration-testing).
These are simple functional tests written in C which are cross-compiled and run natively on the Ibex core.
The software compilation flow to enable this is explained in further detail in the [getting started with SW]({{< relref "getting_started_sw.md" >}}) document.
Further, there is a mechanism for the C test running on the CPU to signal the SystemVerilog testbench the test pass or fail indication based on the observed DUT behavior.
We also provide an environment knob to 'stub' the CPU and use a TL agent to drive the traffic via the CPU's data channel instead, in cases where more intensive testing is needed.
<!-- TODO: add link to chip DV document -->
The chip DV document, which is currently under active development will explain these methodologies and flows in further detail.

## Key Test Focus Areas

When progressing through the verification stages, there are key focus areas or testing activities that are perhaps common across all DUTs.
These are as follows.

### Progressing towards [V1]({{< relref "doc/project/development_stages#hardware-verification-stages" >}})

These set of tests (not exhaustive) provide the confidence that the design is ready for vertical integration.

#### Basic Sanity Test

At this stage, just a skeleton testbench environment is available and most components lack functionality.
A basic sanity test drives the clock, brings the DUT out of reset, checks if all outputs are legal values (not unknown) and exercise a major datapath with simple set of checks.
This paves the way for more complex testing.
During the DV plan and the DV document review, the key stake holders at the higher level who consume the DUT as an IP (for example, design and DV engineers wotking at the chip level into which the IP is integrated) may drive the requirements for the level of testing to be done.
This test (or set of tests) is also included as a part of the sanity regression to maintain the code health.

#### CSR Suite of Tests

The very first set of real tests validate the SW interface laid out using the regtool.
These prove that the SW interface is solid and all assumptions in CSRs in terms of field descriptions and their accessibility are correctly captured and there are no address decode bugs.

### Progressing towards [V2]({{< relref "doc/project/development_stages#hardware-verification-stages" >}})

Bulk of testing in this stage focus on functionally testing the DUT.
There however are certain categories of tests that may need additional attention.
These categories are fairly generic and apply to most DUTs.

#### Power Tests

It is vital to be able to predict the power consumption of our SoC in early development stages and refactor the design as needed to optimize the RTL.
Typically, DV tests that mimic idle and high power consumption scenarios are written and FSDB generated from those tests are used for analysis.

This is perhaps applicable when an actual ASIC will be built out of our SoC.
At that time, we could have lower power requirements in terms of being able to put parts of the SoC in different power 'islands' in retention voltage or be power collapsed.
If and when such requirements are fully specified for the product, we need to ensure that power-aware tests have been added to verify this.

#### Performance Tests

ASICs vary widely in terms of their target applications.
For some, performance testing may take the center stage, and for some, it may not be as important.
No matter what the target application is, there is almost always some kind of requirement in terms of sustained bandwidth on a particular interface captured in the DUT specification.
These set of tests ensure that those requirements are indeed met.

#### Security & Error Tests

Error tests focus on generating stimulus that may not be considered legal and ensure that the DUT can detect, react and behave accordingly, instead of locking up or worse, exposing sensitive information.
These types of tests are particularly important for a security chip such as ours.
These are typically handled via directed tests since it can be prohibitively time consuming to develop complex scoreboards that can handle the error-checking when running completely unconstrained random sequences.
A classic example of this is the illegal / error access tests via the TileLink interface, which are run for all DUTs.
Here, we constrain a random sequence to generate TL accesses that are considered illegal and ensure that the DUT responds with an error when appropriate.
Another example is testing RAMs that support ECC / error correction.

While some of the examples listed above pertain to concrete features in the design, we are actively also exploring alternative ways of finding and covering security holes that may not be uncovered via traditional DV efforts.

#### Debug Tests

This mainly applies to DUTs that contain a processing element (CPU).
These focus verifying the debug features supported by the CPU at the chip level based on the [RISCV debug specification](https://riscv.org/specifications/debug-specification).

#### Stress Tests

Stress tests lean heavily on constrained random techniques, and exercise multiple interfaces and / or design features simultaneously.
This is done by forking off multiple individual test sequences in parallel (or sequentially if the pieces of hardware exercised by the tests sequences overlap).
Stress tests are hard to debug due to lot of things happening in parallel and the scoreboard may not be written as robustly initially to handle those scenarios.
To mitigate that, they are constructed with knobs to control the level of constraints applied to the randomization (of individual sequences), so that the scoreboard can be made more robust incrementally to handle the corner cases.
The level of constraints are then slowly eased to allow deeper state space exploration, until all areas of the DUT are satisfactorily stressed.
Stress tests are ideal for bug hunting and closing coverage.

### Progressing towards [V3]({{< relref "doc/project/development_stages#hardware-verification-stages" >}})

The main focus of testing at this stage is to meet our [regression](#nightly) and [coverage](#coverage-collection) goals.
Apart from that, there are cleanup activities to resolve all pending TODO items in the DV code base and fix all compile and run time warnings (if any) thrown by the simulator tools.

## Assertions

In DV, we follow the same assertion methodology as indicated in the [design methodology]({{< relref "./design.md#assertion-methodology" >}}).
Wherever possible, the assertion monitors developed for FPV are reused in UVM testbenches when running dynamic simulations.
An example of this is the [TLUL Protocol Checker]({{< relref "hw/ip/tlul/doc/TlulProtocolChecker.md" >}}).

## Regressions

There are 2 main types of regressions suites - 'sanity' and 'nightly'.

### Sanity

Due to heavy code reuse, breakages happen quite often.
It is necessary for each DUT testbench to provide a set of simple sanity test that accesses a major datapath in the DUT.
Categorizing such tests into a sanity suite provides a quick path for users who touch common / shared piece of code to run those tests for all DUTs and ensure no breakages occur.
If the DUT testbench has more than one compile-time configuration, there needs to be at least 1 sanity test per configuration.

Ideally, the sanity regression is run as a part of the CI check whenever a PR is submitted. Due to use of proprietary tools for running DV simulations, this cannot be accomplished. Instead, we run a daily cron job locally on the up-to-date `master` branch to identify such breakages and deploy fixes quickly.

### Nightly

While development mostly happens during the work day, nighttime and weekends are better utilized to run all of our simulations (a.k.a "regression").
Achieving 100% pass rate in our nightly regressions consistently is a key to asserting 'verification complete'.
The main goals (for all DUTs) are:

*  Run each constrained random test with a sufficiently large number of seeds (arbitrarily chosen to be 100)
   * Pass completely random seed values to the simulator when running the tests
*  Spawn jobs via LSF to leverage compute resources at one's disposal
*  Run resource intensive simulations without impacting daytime development
*  Collect and merge coverage
*  Publish DV plan-annotated regression and coverage results in the regression dashboard

To re-iterate, these capabilities do not exist yet, but they will be made available soon.
One of the key requirements of nightly regressions is to complete overnight, so that the results are available for analysis and triage the next morning.
If test runtimes are longer, we could define a weekly regression based on need.
In general, it is a good practice to periodically profile the simulation to identify bottlenecks in terms of simulation performance (which often is a result of specific coding style choices).

## Coverage Collection

Collecting, analyzing, and reporting coverage with waivers is a requirement to assert 'verification complete'.
Any gaps in our measured coverage need to be understood and either waived (no need to cover) or closed by additional testing.
The end goal is to achieve 100% coverage across all applicable coverage metrics.
This process is known as "coverage closure", and is done in close collaboration with the designer(s).
Coverage collected from all tests run as a part of the regression is merged into a database for analysis.
Our primary tool of choice for our coverage closure needs is Synopsys VCS & Verdi.
However, the use of other simulators is welcome.

**Why do we need coverage?**

The common answer is to flush out bugs in the design.
This is not accurate enough.
Making sure there are no bugs in a design, while it is important it is not sufficient.
One must also make sure the design works as intended.
That is, it must provide all the functionality specified in the design specification.
So a more precise answer for why we need coverage is to flush out flaws in the design.
These flaws can be either design bugs or deficiencies in the design with respect to the specification.

Another reason for why we need coverage is to answer the seemingly simple but important question:
**When are we done testing?**
Do we need 1, 10, or 100 tests and should they run 10, 100, or 1000 regressions?
Only coverage can answer this question for you.

There are two key types of coverage metrics: code coverage and functional coverage.
Both are important and are covered in more detail below.
For this topic, we define 'pre-verified sub-modules' as IPs within the DUT that have already been (or are planned to be) verified to complete sign-off within individual test benches.

### Code Coverage

Commercial simulators typically provide a way to extract coverage statistics from our regressions.
Tools automatically analyze the design to extract key structures such as lines, branches, FSMs, conditions, and IO toggle and provide them as different metrics to measure coverage against (to what extent is our stimulus through constrained random tests covering these structures).
These metrics are explained briefly below:

* **Line Coverage**: This metric measures which lines of SystemVerilog RTL code were executed during the simulation.
  This is probably the most intuitive metric to use.
  Note that `assign` statements are always listed as covered using this metric.
* **Toggle Coverage**: This metric measures every logic bit to see if it transitions from 1 &rarr; 0 and 0 &rarr; 1.
  It is very difficult, and not particularly useful to achieve 100% toggle coverage across a design.
  Instead, we focus on closing toggle coverage only on the IO ports of the DUT and IO ports of pre-verified IPs within the DUT.
* **FSM state Coverage**: This metric measures which finite state machine states were executed during a simulation.
* **FSM transition Coverage**: This metric measures which arcs were simulated for each finite state machine in the design.
* **Conditional Coverage**: This metric tracks all combinations of conditional expressions simulated.
* **Branch Coverage**: This metric is similar to line coverage, but not quite the same.
  It tracks the flow of simulation (e.g. if/else blocks) as well as conditional expressions.
  Note that un-hit FSM state/transition coverage almost always shows up as un-hit branch coverage as well.

Code coverage is sometimes referred to as implicit coverage as it is generated based on the code and takes no additional effort to implement.

### Functional Coverage

Unlike code coverage, functional coverage requires the designer and/or DV engineer to write additional cover points and covergroups.
For this reason functional coverage is sometimes referred to as explicit coverage.
Cover points and covergroups are more complex constructs that capture whether signals (that reflect the current state of the design) have met an interesting set or a sequence of values (often called corner cases)
These constructs also allow us to capture whether multiple scenarios have occurred simultaneously through crosses.
This is also often referred to as cross coverage.
These constructs are typically encapsulated in a class and are sometimes referred to as the 'functional coverage model'.
They are sampled in 'reactive' components of the testbench, such as monitors and/or the scoreboards.
They can also be embedded within the RTL to sample interesting scenarios through DV stimulus.

Here are the metrics used with a brief explanation:

* **Covergroup Coverage**: Observes values on buses, registers and so on.
  This can verify that a specific value or range of values was seen on a bus and that no illegal values were seen.
  Simulators can be set to throw an error if an illegal value is seen.
  One use of a covergroup is to define something called cross coverage.
  This asserts that several coverage points are hit at once. For example, we might want to see a FIFO's full and write enable signals be asserted at the same time.
  This is called a coverage cross.
* **Cover Property coverage**:
   * **Assertion coverage using SVA**
   * **procedural code**

Most often property coverage is implemented using SystemVerilog Assertions (SVA).
This observes events or series of events.
As an example think of the TL UL register bus used in OpenTitan.
A cover property cover point could be the handshaking between valid and ready.
SVA also allows the design engineer to add cover for procedures and variables not visible on output pins.
Note, an assertion precondition counts as a cover point.


#### Do we need both types of coverage

Reaching a 100% code coverage does not tell you the whole story.
Think of the simple example of an AND gate with inputs A, B, and output O.
To get to 100% code coverage only two different input combinations are needed: 00 and 11, these two will produce all possible outcomes of O.

![single AND gate](dv_method_single_gate.svg)


The coverage will indicate that all code was exercised.
But we do not know that our design works as intended.
All we know is that A, B, and O have been observed to take on both logic 0 and 1.
We could not say for certain that the design was in fact an AND gate: it could just as easily be an OR gate.
So we need functional coverage to tell us this.
The first thing functional coverage will tell us is if we observed all possible values on the inputs.
And by adding a cross between the inputs and the output it will tell us which gate we are looking at.


Reaching 100% functional coverage is not enough either.
Remember functional coverage requires the designer to manually add coverage point into the design.
Going back to our AND gate, let us say we take two of these and OR the outputs of the two.

![multi gate](dv_method_multi_gate.svg)


If we only add the cover points from our original example, these will still exercise the new output of our system and therefore result in reaching 100% functional coverage, but half of the design was not exercised.
This is called a coverage hole and code coverage would have indicated that a part of the code was never exercised.

While functional coverage will tell you if your design is working correctly, code coverage will highlight if your DV plan is incomplete, or if there are any uncovered/unreachable features in the design.
Coverage holes can be addressed accordingly through either updating the design specification and argumenting the DV plan / written tests, or by optimizing the design to remove unreachable logic if possible.
There may be features that cannot be tested and cannot be removed from the design either.
These would have to be analyzed and excluded from the coverage collection as a waiver.
This is an exercise the DV and the designer typically perform together.
This is discussed in more detail below.

### Exclusions

Post-simulation coverage analysis typically yields items that may need to be waived off for various reasons.
This is documented via exclusions, which are generated by the simulator tools.
The following are some of the best practices when adding exclusions:

*  Designers are required to sign-off on exclusions in a PR review
*  Provide annotations for ALL exclusions to explain the reasoning for the waiver
*  Annotate exclusions with a standardized prefix (this makes writing exclusions and reviewing them easier)
   Exclusions almost always fall under a set of categories that can be standardized.
   Annotation can be prefixed with a catehgory tag reflecting one of those categories, like this:

   `[CATEGORY-TAG] <additional explanation if required>`

   These categories are as follows:

   *  **UNR**: Unreachable code due to design constraints, or module inputs being tied off in a certain way will result in specific coverage items being unreachable.
      Additional explanation is optional.
   *  **NON_RTL**: Simulation constructs in RTL that can be safely excluded in structural coverage collection.
      These include tasks and functions, initial / final blocks that are specifically used for simulation such as backdoor write and read functions for memory elements.
      Additional explanation is optional.
   *  **UNSUPPORTED**: Item being excluded is a part of design feature that is not supported.
      Additional explanation is optional.
      *  IP designed by some other team / third party is incorporated, but only a subset of the features are in use. Remaining ones are not supported.
      *  Features that are added into the design but are not made a part of the design specification for the current generation / chip being taped out
      *  UVC / agent with detailed coverage items where certain crosses are not supported by the design (ex: TL agent with fcov on full spectrum of burst with all sizes and lengths, but only a subset of it actually being supported).
      Additional explanation is **mandatory**.
   *  **EXTERNAL**: Items that are already covered in another bench.
      Additional explanation is **mandatory**.
   *  **LOW_RISK**: Items that are prohibitively hard to hit, given the resource constraints and are deemed to be of low risk and low value.
      Features that are added to the design AND are described adequately in the design spec AND a collective upfront decision has been made in agreement with SW/architecture/design/DV to not verify it due to resource constraints.
      Additional explanation is **mandatory**.

### Integration Testing

For a DUT containing pre-verified sub-modules, the DV effort can be slightly eased.
From the code coverage collection perspective, such sub-modules can be 'black boxed' where we turn off all other metrics within their hierarchies and only collect the toggle coverage on their IOs.
This eases our effort by allowing us to develop less complex tests and verification logic (pertaining to those pre-verified modules) since our criteria for closure reduces to only functionally exercising the IOs and their interactions with the rest of the DUT to prove that sub-modules are properly connected.

Of course, the rest of the sub-modules and glue-logic within the DUT that are not pre-verified do need to undergo the full spectrum of coverage closure.
We achieve this by patterning the compile-time code coverage model in a particular way (this is a simulator tool-specific capability; for VCS, this is same as the coverage hierarchy file that is written and passed to the simulator with the `-cm_hier` option).

### Coverage Collection Guidelines

Coverage closure is perhaps the most time-consuming part of the whole DV effort, often with low return.
Conservatively collecting coverage on everything might result in poor ROI of DV user's time.
Also, excessive coverage collection slows down the simulation.
This section aims to capture some of the best practices related to coverage closure.

It is recommended to follow these guidelines when collecting coverage:

*  Shape the coverage collection at compile time if possible by only enabling coverage collection on DUT/sub-modules and nodes, and/or metrics of interest
*  Collect toggle coverage only on IOs of DUT and all of its sub-modules
  *  If this is not worthwhile, then collect coverage on top-level DUT IOs and IOs of pre-verified sub-modules
*  Collect all coverage metrics (except toggle based on above bullet) on the DUT and all of its non-pre-verified sub-modules
*  Treat pre-verified sub-modules as ['black-box'](#integration-testing) in terms of coverage collection

### Unreachable Coverage Analysis

Instead of manually reviewing coverage reports to find unreachable code, we use VCS UNR to generate a UNR exclusion file which lists all the unreachable codes.
VCS UNR (Unreachability) is a formal solution that determines the unreachable coverage objects automatically from simulation.
The same coverage hierarchy file and the exclusion files used for the simulation can be supplied to VCS UNR.

Follow these steps to run and submit the exclusion file.
1. Generate the VCS coverage database for the block by running full regression with `--cov` switch.
2. Launch the VCS UNR flow:
```
util/dvsim/dvsim.py path/to/<dut>_sim_cfg.hjson --cov-unr
```
3. If no exclusion file is generated, there is no unreachable code in RTL.
   If there is an exclusion file generated, the output should be reviewed by both designer and verification engineer.
   When the unreachable code is sensible and we decide to exclude it in coverage report, create a PR to add to ['common_cov_excl.el'](https://github.com/lowRISC/opentitan/blob/master/hw/dv/tools/vcs/common_cov_excl.el) or block specific exclusion file, such as ['uart_cov_excl.el'](https://github.com/lowRISC/opentitan/blob/master/hw/ip/uart/dv/cov/uart_cov_excl.el)

Here are some guidelines for using UNR and checking in generating exclusion.
1. It's encouraged that designers run UNR to check the design in the early design stage (D1/D2), but adding exclusions for unreachable coverage should be done between the D2 and V3 stage when the design is frozen (no feature update is allowed, except bug fix).
Getting to 90% coverage via functional tests is easy.
Over 90% is the hard part as there may be a big chunk of unreachable codes.
It is cumbersome to go through a coverage report to manually add exclusions, but the VCS UNR flow provides a path to weed out all of the unreachable ones.
However, it is not the right thing to add a coverage exclusion file to reach the 80% needed for V2 since the design isn't stable at that period.
2. If any RTL changes happen to the design after the coverage exclusion file has been created, it needs to be redone and re-reviewed.
3. All coverage exclusion files and coverage configuration file (if it's not using default [cover.cfg](https://github.com/lowRISC/opentitan/blob/master/hw/dv/tools/vcs/cover.cfg)) should be checked during sign-off.
4. Keep the VCS generated `CHECKSUM` along with exclusions, which is served as a crosscheck to ensure that the exclusion isn't applied when there is some change on the corresponding codes and the exclusion is outdated.
We should not use `--exclude-bypass-checks` to disable the check, otherwise, it's needed to have additional review to make sure exclusions match to the design.
5. For IP verified in IP-level test bench, UNR should be run in IP-level to generate exclusion.
For IP verified in top-level, UNR should be run in top-level.
There is no reuse of exclusions from IP to top, since they are independently closed for coverage.

Note: VCS UNR doesn't support assertion or functional coverage.

## X-Propagation (Xprop)

Standard RTL simulations (RTL-sim) ignore the uncertainty of X-valued control signals and assign predictable output values.
As a result, classic RTL-sim often fail to detect design problems related to the lack of Xprop, which actually can be detected in gate-level simulations (gate-sim).
With Xprop in RTL-sim, we can detect these problems without having to run gate-sim.

Synopsys VCS and Cadence Xcelium both provide the following 2 modes for Xprop.
  * **Optimistic Mode**: Closer to actual hardware behavior and is the more commonly used mode
  * **Pessimistic Mode**: More pessimistic than a standard gate-sim

Example:
```systemverilog
always @(posedge clk) begin
  if (cond) out <= a;
  else      out <= b;
end
```

In the above example, results of 'out' are shown as following.

a | b | cond | Classic RTL-sim | Gate-sim | Actual Hardware | Xprop Optimistic | Xprop Pessimistic |
--|---|------|-----------------|----------|-----------------|------------------|-------------------|
0 | 0 |  X   |        0        |     0    |       0         |         0        |         X         |
0 | 1 |  X   |        1        |     X    |       0/1       |         X        |         X         |
1 | 0 |  X   |        0        |     X    |       0/1       |         X        |         X         |
1 | 1 |  X   |        1        |     X    |       1         |         1        |         X         |

We choose **Pessimistic Mode** as we want to avoid using X value in the condition.
Xprop is enabled by default when running simulations for all of our DUTs due to the acceptable level of overhead it adds in terms of wall-clock time (less than 10%).

It's mandatory to enable Xprop when running regression for coverage closure.
To test Xprop more effectively, the address / data / control signals are required to be driven to Xs when invalid (valid bit is not set).
For example, when a_valid is 0 in the TLUL interface, we drive data, address and control signals to unknown values.
```systemverilog
  function void invalidate_a_channel();
    vif.host_cb.h2d.a_opcode  <= tlul_pkg::tl_a_op_e'('x);
    vif.host_cb.h2d.a_param   <= '{default:'x};
    vif.host_cb.h2d.a_size    <= '{default:'x};
    vif.host_cb.h2d.a_source  <= '{default:'x};
    vif.host_cb.h2d.a_address <= '{default:'x};
    vif.host_cb.h2d.a_mask    <= '{default:'x};
    vif.host_cb.h2d.a_data    <= '{default:'x};
    vif.host_cb.h2d.a_user    <= '{default:'x};
    vif.host_cb.h2d.a_valid   <= 1'b0;
  endfunction : invalidate_a_channel
```

## FPV

This section is TBD.

## Reviews

One of the best ways to convince ourselves that we have done our job right is by seeking from as well as providing feedback to our contributors.
We have the following types of reviews for DV.

### Code Reviews

Whenever a pull-request is made with DV updates, at least one approval is required by a peer and / or the original code developer to enable the changes to be submitted.
DV updates are scrutinized in sufficient detail to enforce coding style, identify areas of optimizations / improvements and promote code-reuse.

### Sign-off Reviews

In the initial work stage of verification, the DV document and the completed DV plan documents are reviewed face-to-face with the following individuals:

*  Designer(s)
*  DV peers
*  Leads
*  Chip level (or higher level) designers and DV engineers within which the DUT is integrated
*  Software team
*  Product architect

The goal of this review is to achieve utmost clarity in the planning of the DV effort and resolve any queries or assumptions.
The feedback in this review flows both ways - the language in the design specification could be made more precise, or missing items in both, the design specification as well as in the DV plan could be identified and added.
This enables the development stage to progress smoothly.

Subsequently, the intermediate transitions within the verification stages are reviewed within the GitHub pull-request made for updating the checklist and the [project status]({{< relref "doc/project/development_stages.md#indicating-stages-and-making-transitions" >}}).

Finally, after the verification effort is complete, there is a final sign-off review to ensure all checklist items are completed satisfactorily without any major exceptions or open issues.

## Filing Issues

We use the [OpenTitan GitHub Issue tracker](https://github.com/lowRISC/opentitan/issues) for filing possible bugs not just in the design, but also in the DV code base or in any associated tools or processes that may hinder progress.

## Getting Started with DV

The process for getting started with DV involves many steps, including getting clarity on its purpose, setting up the testbench, documentation, etc.
These are discussed in the [Getting Started with DV]({{< relref "getting_started_dv.md" >}}) document.

## Pending Work Items

These capabilities are currently under active development and will be available sometime in the near future:

*  Provide ability to run regressions
