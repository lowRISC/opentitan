# TOP Earl Grey

## How to run simulation
Please run the following command to build and run tests:
`make TEST_NAME=<test-name>`

Please see adjoining Makefile file for list of available tests to run. Please
see `hw/dv/tools/README.md` for additional details on options that can be passed
(such as enabling waves, running with specific seed etc.).

_Note_: Currently, `ibex` core raises an assertion but it doesn't harm UART TX
and GPIO functionalities. Please ignore until it is resolved.
