# Design Parameters

TODO: Presently this file just serves to document the I3C roles intended to be supported by the design.
In time it shall be expanded to describe all of the top-level design parameters.

## I3C Role Configuration

Five role configurations are intended to be supported:

| Required I3C role(s)                                                                          | PrimaryCtrl | SecondaryCtrl | Target | Available |
|-----------------------------------------------------------------------------------------------|-------------|---------------|--------|-----------|
| Primary and Secondary Controller functionality; implies Target functionality and a single bus |      1      |       1       |    1   |     -     |
| Primary Controller and Target; these may be on a single bus or separated buses                |      1      |       0       |    1   |    Yes    |
| Primary controller only                                                                       |      1      |       0       |    0   |    Yes    |
| Secondary Controller; implies Target functionality and a single bus                           |      0      |       1       |    1   |     -     |
| Target only, no Controller logic                                                              |      0      |       0       |    1   |    Yes    |

It should be noted that in this first release, operation as a Secondary Controller is not supported, so not all of these configurations are yet available.
