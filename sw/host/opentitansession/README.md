# OpenTitanSession Tool

The OpenTitanSession tool can be used to start a proxy server for OpenTitanTool clients to connect to.

This allows for resources like FPGAs to be connected to a remote machine and used remotely by one or more users.

The tool can be built and run using Bazel:

```sh
bazel run //sw/host/opentitansession -- help
```
