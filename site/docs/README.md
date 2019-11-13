# Documentation Site
This directory contains the configuration required to build and deploy the
[documentation site](https://docs.opentitan.org) as well as the continuous
deployment configuration that pushes a rebuilt copy of the documentation after
every commit.

# Documentation Builder
In order to speed up the deployment there is a GCR image
(`gcr.io/active-premise-257318/builder`) that contains all of the project's
python requirements pre-installed.  This cuts the deployment from several
minutes to around twenty seconds.  To rebuild and deploy the image use the
`deploy-builder.sh` script.
