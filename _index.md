# Introduction to OpenTitan

The OpenTitan project aims to design and ship an open source, industry-leading piece of secure silicon for Root of Trust applications.
OpenTitan is administered by lowRISC CIC as a collaborative
[project]({{< relref "doc/project.md" >}})
to produce high quality, open IP for instantiation as a full-featured
[product]({{< relref "doc/product.md" >}}).
This repository exists to enable collaboration across partners participating in the OpenTitan project.

To get started using or contributing to the OpenTitan codebase, see the
[list of user guides]({{< relref "doc/ug" >}}).
For details on coding styles or how to use our project-specific tooling, see the
[reference manuals]({{< relref "doc/rm" >}}).
[This page]({{< relref "hw" >}})
contains technical documentation on the SoC, the Ibex processor core, and the individual IP blocks.

While the repository is currently private and the work embargoed at these early stages, it will eventually be released publicly.

## Repository Structure

The underlying
[repo](http://www.github.com/lowrisc/opentitan)
is set up as a monolithic repository to contain RTL, helper scripts, technical documentation, and other software necessary to produce our hardware designs.

See also [repository readme]({{< relref "README.md" >}}) for licensing information and the development methodology.

## Documentation Sections

* [Project]({{< relref "doc/project.md" >}})
  * How the OpenTitan project is organized
  * Governance of the program, how to get involved
  * Progress tracking
* [Product]({{< relref "doc/product.md" >}})
  * What is the OpenTitan product
  * Architecture and technical hardware specifications
  * Software roadmap
  * Security and manufacturing
* [User Guides]({{< relref "doc/ug" >}})
  * How to get started with the repo
  * How to emulate on an FPGA
  * How verification is done in OpenTitan
  * How validation is done on FPGA in the project
* [Reference Manuals]({{< relref "doc/rm" >}})
  * Defining comportable IP peripherals
  * Coding style guides for Verilog, Python, and Markdown
  * OpenTitan tools
  * Working with vendor tools
* [Hardware Specifications]({{< relref "hw" >}})
  * Top-level SoC
  * Ibex processor core
  * Comportable IP blocks
* [Tools]({{< relref "util" >}})
  * Readme's of OpenTitan tools
