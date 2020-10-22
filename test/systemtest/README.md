# OpenTitan System Tests

System tests are end-to-end tests for the whole OpenTitan system. They operate
on build outputs (typically in `build-bin`) and can be used to check that the
full system, consisting of software, hardware, and tooling, works as expected.

Tests can be executed against different target platforms (such as FPGAs or
simulations), even though not all OpenTitan-supported targets are supported at
the moment.

## Available tests

* `earlgrey/test_sim_verilator.py`: Run various software tests against a
  Verilator-built simulation of the Earl Grey design.
* `earlgrey/test_fpga_nexysvideo.py`: Run various software tests against the
  Earl Grey design running on a Nexys Video FPGA board.

## Run the tests

### Prerequisites

Before the tests can be run, the various components of OpenTitan need to be
built and present in the `BIN_DIR` directory (typically `$REPO_TOP/build-bin`).

Alternatively, the tests can be executed against any pre-built OpenTitan
snapshot available from GitHub releases, or from CI.

To test build artifacts from CI follow these steps:

* Go to an individual build job in the
  ["CI" pipelines of Azure Pipelines](https://dev.azure.com/lowrisc/opentitan/_build?definitionId=9&_a=summary).
  (The page where the individual steps for a single change are listed, not the
  job overview page.)
* In the information bar on the top click on a link labeled "5 published"
  (or something similar). It will take you to a page titeled "Artifacts".
* Expand the "opentitan-dist" artifact, and download the file
  `opentitan-snapshot-xxx.tar.xz`.
* Untar this file and set the `BIN_DIR` environment variable to point to the
  extracted directory, for example:

  ```sh
  tar -xf opentitan-snapshot-20191101-1-2462-g3ad4fd1b.tar.xz
  export BIN_DIR=$PWD/opentitan-snapshot-20191101-1-2462-g3ad4fd1b
  ```

### Configuration

Tests running on FPGA boards need some configuration to help with the discovery
of things like the UART port. To configure these settings, copy the
configuration file example from `test/systemtest/test-localconf.yaml.example`
to one of the supported configuration file locations:

* `$OPENTITAN_TEST_LOCALCONF`
* `$XDG_CONFIG_HOME/opentitan/test-localconf.yaml`
* `$HOME/.config/opentitan/test-localconf.yaml`

### Test execution

The pytest documentation gives a good overview of the available options to run
tests in the [Usage and Invocations](https://docs.pytest.org/en/stable/usage.html)
chapter. Here's a quick reference.

```sh
# Run all tests
pytest test/systemtest

# Run tests in a specific file
pytest test/systemtest/earlgrey/test_sim_verilator.py

# Run a specific test in a specific parametrization
pytest test/systemtest/earlgrey/test_sim_verilator.py -k test_apps_selfchecking[usbdev_test]

# Run tests with more verbose output
pytest test/systemtest -sv --log-cli-level=DEBUG
```
