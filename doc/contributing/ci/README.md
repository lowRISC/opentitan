# OpenTitan Continuous Integration

All changes to the OpenTitan source code are tested thoroughly in a continuous integration system.
Tests run automatically when changes are proposed for inclusion by submitting a pull request, and on the `master` branch after changes are merged.
This ensures that the OpenTitan source code meets certain quality criteria at all points in time, as defined by the tests which are executed.

Read on to learn more about the types of tests, and the infrastructure that runs these tests.

## How to report CI problems

If you detect CI failures which look like they might not be related to the tested code, but the test infrastructure, please file an [issue on GitHub](https://github.com/lowRISC/opentitan/issues).
In urgent cases also reach out on Slack and send an email to lowRISC IT at [internal-tech@lowrisc.org](mailto:internal-tech@lowrisc.org).
Note that lowRISC is based in the UK and most active during European business hours.

## Overview

<!--
Source: https://docs.google.com/drawings/d/1-Zjm3k2S0TNmne3F9z3rpTFJfLJJvvmrBAsfx_HG5lk/edit

Download the SVG from Google Draw, open it in Inkscape once and save it without changes to add width/height information to the image.
-->
![CI Overview](continuous_integration_overview.svg)

OpenTitan uses [GitHub Actions](https://github.com/features/actions) as continuous integration provider: test jobs are described in an GitHub Actions-specific way, and then executed on compute resources, some of which are provided by GitHub, and others of which are provided by lowRISC.

Two things are special in the way OpenTitan does continuous integration: private CI, and testing on FPGA boards.

"Private CI" is a term we use for a subset of test jobs which require tighter access control.
The primary use case for private CI are tests using proprietary EDA tools, where the license agreement prevents us from testing arbitrary code with it, from showing the configuration or the output in public, etc.
We run such test jobs in a separate environment where only OpenTitan project members have access.
The test result (pass/fail) is still shared publicly to enable outside contributors to at least get some feedback if their pull request passed our tests.

To test OpenTitan (both the hardware and the software) on FPGAs we have various FPGA boards connected to a machine at lowRISC.
We configure GitHub Actions to schedule test jobs on this machine when FPGA testing is required.
The results and logs of these test runs are shown publicly.

## Test descriptions

All tests are described in a GitHub Actions-specific YAML syntax.
`$REPO_TOP/.github/workflows/ci.yml` is the main configuration file for all public CI jobs.
The private CI jobs are described in a separate private repository, [lowrisc/opentitan-private-ci](https://github.com/lowRISC/opentitan-private-ci), to keep the job descriptions internal for legal reasons.

GitHub Actions documentation can be found at https://docs.github.com/en/actions.

## Compute resources: runners

Each job in the YAML file also specifies which type of compute resource it wants to run on.
An individual compute resource is called a *runner*, and we separate runners by giving them distinct labels for runners with different capability.

For OpenTitan, we have the following runner labels available:
* The *ubuntu-22.04* label is backed a GitHub-provided pool of VMs which are free of charge for us.
  They are described in more detail in the [GitHub Actions documentation](https://docs.github.com/en/actions/using-github-hosted-runners/using-github-hosted-runners/about-github-hosted-runners).
* The *ubuntu-22.04-vivado* label is backed by containers with a lowRISC-specific setup with Xilinx Vivado installed, but has no access to tools with special license restrictions.
* The *ubuntu-22.04-&lt;vendor&gt;* labels have proprietary EDA tools installed and access to the respective licenses.
* The *ubuntu-22.04-fpga* label currently consists of containers on a single machine with our FPGA boards connected to it.

All self-hosted runners (i.e. non-GitHub runners) are managed by lowRISC IT.

All runners provide ephemeral test environments: the test environment is initialized at the start of a test job and completely destroyed at the end.
This is achieved by running tests in Docker containers which are recreated after each run.
The base image used for all lowRISC-hosted runners is available [as lowrisc/eda-runner-ubuntu-22.04 on DockerHub](https://hub.docker.com/r/lowrisc/eda-runner-ubuntu-22.04).
(The build rules/Dockerfile for this image are lowRISC-internal.)

lowRISC-provided runners run in a Kubernetes cluster on Google Cloud (GCP), where we also define the resources allocated for the individual runners.
The number of runners automatically scale depending on the number of scheduled jobs and has an upper limit.

## Job scheduling, build triggers and status reporting

When an event, e.g. the creation of new pull requests, are triggered, GitHub Actions compares them with the configured workflow triggers in the `.github/workflows/ci.yml` file.
It then processes the workflow description and queues and dispatches test jobs to the respective runners, taking test dependencies into account.

After the runner has completed a test job it reports back the result GitHub Actions, which makes this information (build artifacts and logs) available to users through the web UI.
The status of GitHub Actions is displayed below a pull request, as marks next to commits, and in various other places.
