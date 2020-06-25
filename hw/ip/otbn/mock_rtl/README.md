# OTBN RTL Mock

This RTL implements the basic functionality to implement the arithmetic
capabilities of the wide side of OTBN. It exists purely for implementation
trials to get an estimate of area and early visibility of any timing issues.  It
has a very simple self checking testbench and lint but otherwise no
verification. It is not intended to complete or even good RTL and whilst it may
inform the actual OTBN implementation it doesn't form part of it.

To run the self checking testbench in VCS (Verilator is not supported as it uses
constructs verilator doesn't support):

```
fusesoc --cores-root . run --target=sim --tool=vcs --setup --build lowrisc:ip:otbn_mock
./build/lowrisc_ip_otbn_mock_0.1/sim-vcs/lowrisc_ip_otbn_mock_0.1
```

It will report 'Test PASS' or give some errors

To run verilator lint:

```
fusesoc --cores-root . run --target=lint lowrisc:ip:otbn_mock
```
