# Hardware

This page serves as the landing spot for all hardware development within the OpenTitan project.

We start off by providing links to the [results of various tool-flows](#results-of-toolflows) run on all of our [Comportable](../doc/contributing/hw/comportability/README.md) IPs.
This includes DV simulations, FPV and lint, all of which are run with the `dvsim` tool which serves as the common frontend.

The [Comportable IPs](#comportable-ips) following it provides links to their design specifications and DV documents, and tracks their current stage of development.
See the [Hardware Development Stages](../doc/project_governance/development_stages.md) for description of the hardware stages and how they are determined.

Next, we focus on all available [processor cores](#processor-cores) and provide links to their design specifications, DV documents and the DV simulation results.

Finally, we provide the same set of information for all available [top level designs](#top-level-designs).

## Block-level results of tool-flows

* [DV simulation summary results, with coverage (nightly)](https://reports.opentitan.org/hw/top_earlgrey/dv/summary/latest/report.html)
* [FPV sec_cm results (weekly)](https://reports.opentitan.org/hw/top_earlgrey/formal/sec_cm/summary/latest/report.html)
* [FPV ip results (weekly)](https://reports.opentitan.org/hw/top_earlgrey/formal/ip/summary/latest/report.html)
* [FPV prim results (weekly)](https://reports.opentitan.org/hw/top_earlgrey/formal/prim/summary/latest/report.html)
* [AscentLint summary results (nightly)](https://reports.opentitan.org/hw/top_earlgrey/lint/ascentlint/summary/latest/report.html)
* [Verilator lint summary results (nightly)](https://reports.opentitan.org/hw/top_earlgrey/lint/verilator/summary/latest/report.html)
* [Style lint summary results (nightly)](https://reports.opentitan.org/hw/top_earlgrey/lint/veriblelint/summary/latest/report.html)
* [DV Style lint summary results (nightly)](https://reports.opentitan.org/hw/top_earlgrey/dv/lint/veriblelint/summary/latest/report.html)
* [FPV Style lint summary results (nightly)](https://reports.opentitan.org/hw/top_earlgrey/fpv/lint/veriblelint/summary/latest/report.html)

## Comportable IPs

{{#dashboard comportable }}

## Processor cores

* `core_ibex`
  * [User manual](https://ibex-core.readthedocs.io/en/latest)
  * [DV document](https://ibex-core.readthedocs.io/en/latest/03_reference/verification.html)
  * DV simulation results, with coverage (nightly) (TBD)

## Earl Grey top-level

* [Datasheet](./top_earlgrey/doc/datasheet.md)
* [Specification](./top_earlgrey/doc/design/README.md)
* [DV Document](./top_earlgrey/dv/README.md)
* [DV simulation results, with coverage (nightly)](https://reports.opentitan.org/hw/top_earlgrey/dv/latest/report.html)
* [Connectivity results (nightly)](https://reports.opentitan.org/hw/top_earlgrey/conn/jaspergold/latest/report.html)
* [AscentLint results (nightly)](https://reports.opentitan.org/hw/top_earlgrey/lint/ascentlint/latest/report.html)
* [Verilator lint results (nightly)](https://reports.opentitan.org/hw/top_earlgrey/lint/verilator/latest/report.html)
* [Style lint results (nightly)](https://reports.opentitan.org/hw/top_earlgrey/lint/veriblelint/latest/report.html)
* [DV Style lint results (nightly)](https://reports.opentitan.org/hw/top_earlgrey/dv/lint/veriblelint/latest/report.html)
* [CDC results (nightly)](https://reports.opentitan.org/hw/top_earlgrey/cdc/latest/report.html)

### Earl Grey-specific comportable IPs

{{#dashboard top_earlgrey }}

## Darjeeling top-level

* [Datasheet](./top_darjeeling/doc/datasheet.md)
