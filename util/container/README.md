# Docker Container

Docker container based on Ubuntu 18.04 LTS containing various hardware and
software development tools for OpenTitan, as listed in the
[OpenTitan documentation](https://docs.opentitan.org/doc/ug/install_instructions/).

## Local Build Instructions

Skip this step if planning to use the pre-built container. To build in local
mode:

```shell
$ cd $REPO_TOP
$ sudo docker build -t opentitan -f util/container/Dockerfile .
```

## Using the Container

To run container in interactive mode:

```shell
$ docker run -it -v $REPO_TOP:/repo -w /repo opentitan --user $(id -u):$(id -g)
```

## Pre-built Container

There is an experimental version of the container available. To download, run:

```shell
$ docker pull gcr.io/opentitan/hw_dev
```

Use `gcr.io/opentitan/hw_dev` as the container name in any Docker commands.
