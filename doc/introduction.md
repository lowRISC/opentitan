# OpenTitan

## Introduction to OpenTitan

[OpenTitan](https://opentitan.org) is an open source secure silicon ecosystem producing both silicon IP and complete top-level designs capable of supporting numerous applications, including a discrete secure micro-controller and an integrated secure execution environment (both supporting Root of Trust functionality with secure boot and DICE attestation).
OpenTitan will make design and implementation of secure silicon more transparent, trustworthy, and secure for enterprises, platforms, and chip manufacturers.
OpenTitan is administered by lowRISC CIC as a [collaborative, partner-centric project](./project_governance/README.md) to produce high quality, open IP for instantiation as a full-featured product.
This repository exists to enable collaboration across participating OpenTitan project partners and the broader open silicon community.

## Getting Started

Start at the [Getting Started](./getting_started/README.md) page to begin your OpenTitan journey.
Other helpful OpenTitan resources include the [contribution](./contributing/README.md) and the [tools guides](../util/README.md).
The [Hardware book](../hw/README.md) also contains useful technical documentation on the SoC, our RISC-V Ibex processor core, and the individual IP blocks.
For questions about how project organization and governance, see the [project landing spot](./project_governance/README.md).

## Understanding OpenTitan

* [Use Cases](./use_cases/README.md)
* [Threat Model](./security/threat_model/README.md)
* [Security](./security/README.md)

## Datasheets

* [OpenTitan Earl Grey (Standalone Chip) Datasheet](../hw/top_earlgrey/doc/datasheet.md)
* [OpenTitan Darjeeling (Integrated Admissible Architecture) Datasheet](../hw/top_darjeeling/doc/datasheet.md)

## Documentation

* [Hardware](../hw/README.md)
* [Software](../sw/README.md)

## Development

* [Getting Started](./getting_started/README.md)
* [Contributor's Reference](./contributing/README.md)
* [Tool References](../util/README.md)
* [Style Guides](./contributing/style_guides/README.md)

## Repository Structure

The underlying
[repo](https://www.github.com/lowrisc/opentitan)
is set up as a monolithic repository to contain RTL, helper scripts, technical documentation, and other software necessary to produce our hardware designs.

Unless otherwise noted, everything in the repository is covered by the Apache License, Version 2.0. See the [LICENSE](https://github.com/lowRISC/opentitan/blob/master/LICENSE) file and [repository README](https://github.com/lowRISC/opentitan/blob/master/README.md) for more information on licensing and see the user guides below for more information on development methodology.
