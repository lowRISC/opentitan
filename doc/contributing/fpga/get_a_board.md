# Get an FPGA Board

This page lists the FPGA boards supported by the OpenTitan project.

## ChipWhisperer CW340 OpenTitan Kit (recommended)

The ChipWhisperer CW340 OpenTitan Kit is produced by [NewAE Technology](https://www.newae.com/).
The kit consists of:
- CW340 baseboard, and
- the CW341 Kintex UltraScale KU095 FPGA.
This platform is the primary development target for the OpenTitan project with an FPGA that is large enough to run all current variants of OpenTitan.

You can get the ChipWhisperer CW340 OpenTitan Kit from [Mouser](https://www.mouser.com/access/?pn=343-NAE-CW340-OTKIT).

### HyperDebug Board

The CW340 base board has ST Zio connectors to facilitate connecting an STM32 NUCLEO-L552ZE-Q board (referred to in the code base as the "HyperDebug" board) to act as an intermediary between your host machine and OpenTitan (emulated on the FPGA).
The OpenTitan project provides firmware and tooling (inside `opentitanlib`) to interact with an emulated OpenTitan chip using HyperDebug.
To enable more advance test cases, you can purchase a NUCLEO board to connect to your CW340 base board from either:
- [DigiKey](https://www.digikey.com/en/products/detail/stmicroelectronics/nucleo-l552ze-q/11501277)
- [Mouser](https://www.mouser.com/ProductDetail/STMicroelectronics/NUCLEO-L552ZE-Q?qs=%252B6g0mu59x7JMzV%2FcT2vTmQ%3D%3D&mgh=1&gclid=CjwKCAiA0JKfBhBIEiwAPhZXD180uAwZiK1O9QEDchhdubtkSJ9rUAx25hV3fbKHeqKZHfze9OPL3RoCRpkQAvD_BwE)
- [Newark](https://www.newark.com/stmicroelectronics/nucleo-l552ze-q/dev-board-32bit-arm-cortex-m33f/dp/52AH4118?gclid=CjwKCAiA0JKfBhBIEiwAPhZXDx9tzkzzB52vjBvXeWpsT0IuU3Tw_Z2VqjkpzEtpxVX_91m_nwP6sBoCJRUQAvD_BwE&mckv=_dc%7Cpcrid%7C%7Cplid%7C%7Ckword%7C%7Cmatch%7C%7Cslid%7C%7Cproduct%7C52AH4118%7Cpgrid%7C%7Cptaid%7C%7C&CMP=KNC-GUSA-PMAX-Shopping-High-ROAS)

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
