## Overview
`Hello_world` is the demo program used to show case basic functionality of the system.
The test itself does 2 main things:
* Echo pin changes over UART.
* Echo SPI input over UART.

## GPIO Changes Over UART
This function primarily exercises the GPIO and UART blocks.
The test monitors changing values on the GPIO line and reports them over UART.

## SPI Echo Over UART
All data input over SPI is echo'd on UART in a word aligned fashion.
The sample output below is hello_world run on a verilator model.
```shell
$ ./Vtop_earlgrey_verilator --rominit=sw/boot_rom/rom.vmem --flashinit=sw/examples/hello_world/sw.vmem
```

Output:
```
dddd 1234 tgbf
```

```
SPI: dddd
SPI: 1234
SPI: tgbf
```
