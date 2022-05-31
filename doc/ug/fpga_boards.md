---
title: "Get an FPGA Board"
---

FPGA boards come at different price points, with the price being a good indicator for how much logic the FPGA can hold.
The following sections give details of how to obtain our supported FPGA boards.

## ChipWhisperer CW310

The ChipWhisperer CW310 board is produced by [NewAE Technology](https://www.newae.com/).
It is available with a Xilinx Kintex 7 XC7K160T or XC7K410T FPGA.
At the moment, the version with the smaller Xilinx Kintex 7 XC7K160T FPGA is not supported by OpenTitan.
The ChipWhisperer CW310 board with the bigger Xilinx Kintex 7 XC7K410T FPGA is the main development FPGA board for OpenTitan.

### Ordering

You can get the ChipWhisperer CW310 board from the [NewAE Technology web store](https://store.newae.com/cw310-bergen-board-large-fpga-k410t-for-full-emulation/).

In the future, the board might also be listed on [Mouser](https://eu.mouser.com/manufacturer/newae-technology/).

### Notes

* By default the board ships with a US and European power plug.
  Optionally, a UK power plug can be selected in the NewAE Technology web store.
* The board is available in two options.
  The normal option is suitable for e.g. regular hardware and software development.
  If you also plan to do Side Channel Analysis (SCA), you should make sure to order the SCA option which misses some decoupling capacitors.
