# OpenTitan

![OpenTitan logo](https://docs.opentitan.org/doc/opentitan-logo.png)

## About the project

[OpenTitan](https://opentitan.org) is an open source silicon Root of Trust
(RoT) project.  OpenTitan will make the silicon RoT design and implementation
more transparent, trustworthy, and secure for enterprises, platform providers,
and chip manufacturers.  OpenTitan is administered by [lowRISC
CIC](https://www.lowrisc.org) as a collaborative project to produce high
quality, open IP for instantiation as a full-featured product. See the
[OpenTitan site](https://opentitan.org/) and [OpenTitan
docs](https://docs.opentitan.org) for more information about the project.

## About this repository

This repository contains hardware, software and utilities written as part of the
OpenTitan project. It is structured as monolithic repository, or "monorepo",
where all components live in one repository. It exists to enable collaboration
across partners participating in the OpenTitan project.

## Documentation

The project contains comprehensive documentation of all IPs and tools. You can
access it [online at docs.opentitan.org](https://docs.opentitan.org/).

## How to contribute

Have a look at [CONTRIBUTING](https://github.com/lowRISC/opentitan/blob/master/CONTRIBUTING.md) and our [documentation on
project organization and processes](https://docs.opentitan.org/doc/project/)
for guidelines on how to contribute code to this repository.

## Licensing

Unless otherwise noted, everything in this repository is covered by the Apache
License, Version 2.0 (see [LICENSE](https://github.com/lowRISC/opentitan/blob/master/LICENSE) for full text).

## Publications
If you use this version of OpenTitan in your work or research, you can cite us:

```
@article{10.1145/3690823,
author = {Ciani, Maicol and Parisi, Emanuele and Musa, Alberto and Barchi, Francesco and Bartolini, Andrea and Kulmala, Ari and Psiakis, Rafail and Garofalo, Angelo and Acquaviva, Andrea and Davide, Rossi},
title = {Unleashing OpenTitan's Potential: a Silicon-Ready Embedded Secure Element for Root of Trust and Cryptographic Offloading},
year = {2024},
publisher = {Association for Computing Machinery},
address = {New York, NY, USA},
issn = {1539-9087},
url = {https://doi.org/10.1145/3690823},
doi = {10.1145/3690823},
abstract = {The rapid advancement and exploration of open-hardware RISC-V platforms are catalyzing substantial changes across critical sectors, including autonomous vehicles, smart-city infrastructure, and medical devices. Within this technological evolution, OpenTitan emerges as a groundbreaking open-source RISC-V design, renowned for its comprehensive security toolkit and role as a standalone system-on-chip (SoC). OpenTitan encompasses different SoC implementations such as Earl Grey, fully implemented and silicon proven, and Darjeeling, announced but not yet fully implemented. The former targets a stand-alone system-on-chip implementation, the latter oriented towards an integrable implementation. Therefore, the literature currently lacks of a silicon-ready embedded implementation of an open-source Root of Trust, despite the effort put by lowRISC on the Darjeeling implementation of OpenTitan. We address the limitations of existing implementations, focusing on optimizing data transfer latency between memory and cryptographic accelerators to prevent under-utilization and ensure efficient task acceleration. Our contributions include a comprehensive methodology for integrating custom extensions and IPs into the Earl Grey architecture, architectural enhancements for system-level integration, support for varied boot modes, and improved data movement across the platform. These advancements facilitate the deployment of OpenTitan in broader SoCs, even in scenarios lacking specific technology-dependent IPs, providing a deployment-ready research vehicle for the community. We integrated the extended Earl Grey architecture into a reference architecture in 22nm FDX technology node, and then we benchmarked the enhanced architecture’s performance analyzing the latency introduced by the external memory hierarchic levels, presenting significant improvements in cryptographic processing speed, achieving up to 2.7x speedup for SHA-256/HMAC and 1.6x for AES accelerators, compared to baseline Earl Grey architecture.},
note = {Just Accepted},
journal = {ACM Trans. Embed. Comput. Syst.},
month = sep,
keywords = {RISC-V, OpenTitan, Embedded System Security, Secure System-on-Chips}
}

```
