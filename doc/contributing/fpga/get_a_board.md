# Get an FPGA Board

This page lists the FPGA boards supported by the OpenTitan project.

## ChipWhisperer CW340 OpenTitan Kit (recommended)

The ChipWhisperer CW340 OpenTitan Kit is produced by [NewAE Technology](https://www.newae.com/).
The kit consists of the CW340 baseboard and the CW341 Kintex UltraScale KU095 FPGA.
This platform is the primary development target for the OpenTitan project with an FPGA that is large enough to run all current variants of OpenTitan.

You can get the ChipWhisperer CW340 OpenTitan Kit from [Mouser](https://www.mouser.com/access/?pn=343-NAE-CW340-OTKIT).

## ChipWhisperer CW310

The ChipWhisperer CW310 board is produced by [NewAE Technology](https://www.newae.com/).
It is available with a Xilinx Kintex 7 XC7K160T or XC7K410T FPGA.
At the moment, the version with the smaller Xilinx Kintex 7 XC7K160T FPGA is not supported by OpenTitan.
The ChipWhisperer CW310 board with the bigger Xilinx Kintex 7 XC7K410T FPGA is an FPGA board that can be used for general purpose OpenTitan development (though some features may need to be disabled).

You can get the ChipWhisperer CW310 from [Mouser](https://www.mouser.com/access/?pn=343-NACW310K410TNORM) or the [NewAE Technology web store](https://store.newae.com/cw310-bergen-board-large-fpga-k410t-for-full-emulation/).

### Notes

* By default the board ships with a US and European power plug.
  Optionally, a UK power plug can be selected in the NewAE Technology web store.
* The board is available in two options.
  The normal option is suitable for e.g. regular hardware and software development.
  If you also plan to do Side Channel Analysis (SCA), you should make sure to order the SCA option which misses some decoupling capacitors.
