# Options
There are two main options available for coremark SIM, ITERATIONS

## ITERATIONS
Controls how many iteartions are run.  By default this value is 0 and will cause coremark to run >10s.
For simulation and verilator, set to 1 for a reduced run

## For verilator
make distclean; make SIM=1 ITERATIONS=1
SIM=1 matces the verilator UART baudrates

## For DV / FPGA
make distclean; make ITERATIONS=1/N
