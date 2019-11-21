# Docker Container

Docker container based on Ubuntu 16.04 LTS containing various hardware and
software development tools for OpenTitan. Current list of tools:

* Python 3
* fusesoc
* OpenOCD
* RISCV toolchain
* Verilator

## Local Build Instructions

Skip this step if planning to use the pre-built container. To build in local
mode:

```shell
$ cd ${REPO_TOP}
$ sudo docker build -t opentitan -f util/container/Dockerfile .
```

## Using the Container

To run container in interactive mode:

```shell
$ docker run -it -v ${REPO_TOP}:/repo -w /repo opentitan --user $(id -u):$(id -g)
```

## Pre-built Container

There is an experimental version of the container available. To download, run:

```shell
$ time docker pull gcr.io/opentitan/hw_dev
```

Use `gcr.io/opentitan/hw_dev` as the container name in any Docker commands.
