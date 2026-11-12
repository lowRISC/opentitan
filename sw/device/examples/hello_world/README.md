# Hello World Example

## Overview

`hello_world` is the demo program used to showcase basic functionality of the system.
It does two main things:
* Echoes received UART characters back over UART and displays the lower nibble (`bits [3:0]`) of the last ASCII character on four user LEDs (`IOR10`–`IOR13`, `LED4`–`LED7` on CW340).
* Polls four GPIO switch inputs (`IOB6`, `IOB9`, `IOB10`, `IOR5`, mapped to `GPIO #8`–`#11`) and logs changes over UART.

## Running on CW340

On the CW340 board, the standard FPGA setup isolates the onboard LEDs and DIP switches (`SW1` and `SW2` on the bottom side are `OFF`).
To observe the demo physically on the board:
* Slide `SW2` (`LED ISOLATE`) switches **5–8** to `ON` to enable `LED4`–`LED7`.
* Slide `SW1` (`SW ISOLATE`) switches **1, 4, 5, and 8** to `ON` to connect top-side `SW4` (`USRDIP`) switches **1, 4, 5, and 8** (`USRDIP0`, `USRDIP3`, `USRDIP4`, `USRDIP7`) to `IOB6`, `IOB9`, `IOB10`, and `IOR5`. (Slide `SW1` and `SW2` back to `OFF` before running automated hardware tests.)

Make sure the CW340 FPGA already has `test_rom` loaded (for example by running `uart_smoketest_fpga_cw340_test_rom` once after power-on), then build and bootstrap `hello_world`:

```sh
./bazelisk.sh build --output_groups=fpga_cw340_binary //sw/device/examples/hello_world
./bazelisk.sh run //sw/host/opentitantool -- --rcfile= --interface=hyper340 \
  --exec="bootstrap --clear-uart=true $(ci/scripts/target-location.sh //sw/device/examples/hello_world --output_groups=fpga_cw340_binary)" \
  console
```
