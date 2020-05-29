---
title: "Hardware Dashboard"
---

This page serves as the landing spot for all hardware development within the OpenTitan project.

We start off by providing links to the [results of various tool-flows](#results-of-toolflows) run on all of our [Comportable]({{< relref "doc/rm/comportability_specification" >}}) IPs.
This includes DV simulations, FPV and lint, all of which are run with the `dvsim` tool which serves as the common frontend.

The [Comportable IPs](#comportable-ips) following it provides links to their design specifications and DV plans, and tracks their current stage of development.
See the [Hardware Development Stages]({{< relref "/doc/project/development_stages.md" >}}) for description of the hardware stages and how they are determined.

Next, we focus on all available [processor cores](#processor-cores) and provide links to their design specifications, DV plans and the DV simulation results.

Finally, we provide the same set of information for all available [top level designs](#top-level-designs), including an additional dashboard with preliminary synthesis results for some of these designs.


## Results of tool-flows

* [DV simulation summary results, with coverage (nightly)](https://reports.opentitan.org/hw/top_earlgrey/dv/summary.html)
* FPV summary results (nightly) (TBD)
* [Lint summary results (nightly)](https://reports.opentitan.org/hw/top_earlgrey/lint/ascentlint/summary.html)
* [Style lint summary results (nightly)](https://reports.opentitan.org/hw/top_earlgrey/lint/veriblelint/summary.html)

## Comportable IPs

{{< dashboard "hw/ip" >}}

## Processor cores

* `core_ibex`
  * [User manual](https://ibex-core.readthedocs.io/en/latest)
  * [DV plan](https://ibex-core.readthedocs.io/en/latest/verification.html)
  * DV simulation results, with coverage (nightly) (TBD)

## Top level designs

* `top_earlgrey`
  * [Design specification]({{< relref "hw/top_earlgrey/doc" >}})
  * DV plan (TBD)
  * [DV simulation results, with coverage (nightly)](https://reports.opentitan.org/hw/top_earlgrey/dv/latest/results.html)
  * FPV results (nightly) (TBD)
  * [Lint results (nightly)](https://reports.opentitan.org/hw/top_earlgrey/lint/ascentlint/latest/results.html)
  * [Style lint results (nightly)](https://reports.opentitan.org/hw/top_earlgrey/lint/veriblelint/latest/results.html)
  * [Synthesis results (nightly)](https://reports.opentitan.org/hw/top_earlgrey/syn/latest/results.html)
