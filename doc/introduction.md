---
title: "OpenTitan"
---

## Introduction to OpenTitan

[OpenTitan](https://opentitan.org) is an open source silicon Root of Trust (RoT) project.
OpenTitan will make the silicon RoT design and implementation more transparent, trustworthy, and secure for enterprises, platform providers, and chip manufacturers.
OpenTitan is administered by lowRISC CIC as a collaborative [project]({{< relref "doc/project" >}}) to produce high quality, open IP for instantiation as a full-featured product.
This repository exists to enable collaboration across partners participating in the OpenTitan project.

## Getting Started

To get started with OpenTitan, see the [Getting Started]({{< relref "doc/getting_started" >}}) page.
For additional resources when working with OpenTitan, see the [list of user guides]({{< relref "doc/ug" >}}).
For details on coding styles or how to use our project-specific tooling, see the [reference manuals]({{< relref "doc/rm" >}}).
Lastly, the [Hardware Dashboard page]({{< relref "hw" >}}) contains technical documentation on the SoC, the Ibex processor core, and the individual IP blocks.
For questions about how the project is organized, see the [project]({{< relref "doc/project" >}}) landing spot for more information.

## Understanding OpenTitan

* [Use Cases]({{< relref "doc/use_cases" >}})
* [Threat Model]({{< relref "doc/security/threat_model" >}})
* [Security]({{< relref "doc/security" >}})

## Datasheets

* [OpenTitan Earl Grey Chip Datasheet]({{< relref "hw/top_earlgrey/doc" >}})

## Documentation

* [Hardware]({{< relref "hw" >}})
* [Software]({{< relref "sw" >}})

## Development

* [Getting Started]({{< relref "doc/getting_started" >}})
* [User Guides]({{< relref "doc/ug" >}})
* [Reference Manuals]({{< relref "doc/rm" >}})
* [Style Guides]({{< relref "doc/sg" >}})

## Repository Structure

The underlying
[repo](http://www.github.com/lowrisc/opentitan)
is set up as a monolithic repository to contain RTL, helper scripts, technical documentation, and other software necessary to produce our hardware designs.

Unless otherwise noted, everything in the repository is covered by the Apache License, Version 2.0. See the [LICENSE](https://github.com/lowRISC/opentitan/blob/master/LICENSE) file and [repository README](https://github.com/lowRISC/opentitan/blob/master/README.md) for more information on licensing and see the user guides below for more information on development methodology.
