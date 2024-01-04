# Hardware

This page serves as the landing spot for all hardware development within the OpenTitan project.

We start off by providing links to the [results of various tool-flows](#results-of-toolflows) run on all of our [Comportable](../doc/contributing/hw/comportability/README.md) IPs.
This includes DV simulations, FPV and lint, all of which are run with the `dvsim` tool which serves as the common frontend.

The [Comportable IPs](#comportable-ips) following it provides links to their design specifications and DV documents, and tracks their current stage of development.
See the [Hardware Development Stages](../doc/project_governance/development_stages.md) for description of the hardware stages and how they are determined.

Next, we focus on all available [processor cores](#processor-cores) and provide links to their design specifications, DV documents and the DV simulation results.

Finally, we provide the same set of information for all available [top level designs](#top-level-designs).

## Results of tool-flows

* [DV simulation summary results, with coverage (nightly)](https://reports.opentitan.org/integrated/hw/top_darjeeling/dv/summary/latest/report.html)
* [FPV sec_cm results (weekly)](https://reports.opentitan.org/integrated/hw/top_darjeeling/formal/sec_cm/summary/latest/report.html)
* [FPV ip results (weekly)](https://reports.opentitan.org/integrated/hw/top_darjeeling/formal/ip/summary/latest/report.html)
* [FPV prim results (weekly)](https://reports.opentitan.org/integrated/hw/top_darjeeling/formal/prim/summary/latest/report.html)
* [AscentLint summary results (nightly)](https://reports.opentitan.org/integrated/hw/top_darjeeling/lint/ascentlint/summary/latest/report.html)
* [Verilator lint summary results (nightly)](https://reports.opentitan.org/integrated/hw/top_darjeeling/lint/verilator/summary/latest/report.html)
* [Style lint summary results (nightly)](https://reports.opentitan.org/integrated/hw/top_darjeeling/lint/veriblelint/summary/latest/report.html)
* [DV Style lint summary results (nightly)](https://reports.opentitan.org/integrated/hw/top_darjeeling/dv/lint/veriblelint/summary/latest/report.html)
* [FPV Style lint summary results (nightly)](https://reports.opentitan.org/integrated/hw/top_darjeeling/fpv/lint/veriblelint/summary/latest/report.html)

## Comportable IPs

{{#dashboard comportable }}

## Processor cores

* `core_ibex`
  * [User manual](https://ibex-core.readthedocs.io/en/latest)
  * [DV document](https://ibex-core.readthedocs.io/en/latest/03_reference/verification.html)
  * DV simulation results, with coverage (nightly) (TBD)

## Darjeeling chip-level results

* [Datasheet](./top_darjeeling/doc/datasheet.md)
* [Specification](./top_darjeeling/doc/design/README.md)
* [DV Document](./top_darjeeling/dv/README.md)
* [DV simulation results, with coverage (nightly)](https://reports.opentitan.org/integrated/hw/top_darjeeling/dv/latest/report.html)
* [Connectivity results (nightly)](https://reports.opentitan.org/integrated/hw/top_darjeeling/conn/jaspergold/latest/report.html)
* [AscentLint results (nightly)](https://reports.opentitan.org/integrated/hw/top_darjeeling/lint/ascentlint/latest/report.html)
* [Verilator lint results (nightly)](https://reports.opentitan.org/integrated/hw/top_darjeeling/lint/verilator/latest/report.html)
* [Style lint results (nightly)](https://reports.opentitan.org/integrated/hw/top_darjeeling/lint/veriblelint/latest/report.html)
* [DV Style lint results (nightly)](https://reports.opentitan.org/integrated/hw/top_darjeeling/dv/lint/veriblelint/latest/report.html)
* [CDC results (nightly)](https://reports.opentitan.org/integrated/hw/top_darjeeling/cdc/latest/report.html)

### Darjeeling-specific comportable IPs

<!--
  Note: there should be a dashboard link here, but we don't currently
  have any dashboard to serve! The missing data caused the
  documentation build to fail, so we've chopped it out for now.
-->
TODO: There is no dashboard yet!
