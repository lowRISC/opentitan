# OpenTitan

![OpenTitan logo](doc/opentitan-logo.png)

## About the project

[OpenTitan](https://opentitan.org) is an open source silicon Root of Trust
(RoT) project.  OpenTitan will make the silicon RoT design and implementation
more transparent, trustworthy, and secure for enterprises, platform providers,
and chip manufacturers.  OpenTitan is administered by [lowRISC
CIC](https://www.lowrisc.org) as a collaborative project to produce high
quality, open IP for instantiation as a full-featured product. See the the
[OpenTitan site](https://opentitan.org/) and [OpenTitan
docs](https://docs.opentitan.org) for more information about the project.

## About this repository

This repository contains hardware, software and utilities written as part of the
OpenTitan project. It is structured as monolithic repository, or "monorepo",
where all components live in one repository. It exists to enable collaboration
across partners participating in the OpenTitan project.

## Documentation

The project contains comprehensive documentation of all IPs and tools. You can
either access it [online](https://docs.opentitan.org/) or build it
locally by following the steps below.

1. Ensure that you have the required Python modules installed (to be executed
in the repository root):

```command
$ sudo apt install curl python3 python3-pip
$ pip3 install --user -r python-requirements.txt
```

2. Execute the build script:

```command
$ ./util/build_docs.py --preview
```

This compiles the documentation into `./build/docs` and starts a local
server, which allows you to access the documentation at
[http://127.0.0.1:1313](http://127.0.0.1:1313).

## How to contribute

Have a look at [CONTRIBUTING](./CONTRIBUTING.md) for guidelines on how to
contribute code to this repository.

## Licensing

Unless otherwise noted, everything in this repository is covered by the Apache
License, Version 2.0 (see
[LICENSE](./LICENSE) for full text).
