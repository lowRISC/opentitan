# Install Vivado

Generating a bitstream for Xilinx devices requires a [Vivado](https://www.xilinx.com/products/design-tools/vivado.html) installation.
Please note that the "WebPACK" edition __does not__ support the Xilinx Kintex UltraScale XCKU095 used on the CW341 board.

For software development, Vivado is *not* necessary for most workflows.
We previously used Vivado's `updatemem` to splice ROM & OTP images into the bitstream, which required the (free) Lab edition of Vivado.
This has since been migrated to instead use an FPGA-specific IP to program memories over JTAG, and thus is no longer necessary.

## Install Xilinx Vivado

_**Vivado Version:** The recommendation is to use Vivado {{#tool-version vivado }}._

Following the arrival of Vivado ML Edition, you will need to follow the links for that, eg. Products -> Hardware Development -> Vivado ML.
Then click on 'Vivado Archive' in the Version list and locate version {{#tool-version vivado }} of Vivado Design Suite.

See [Download and Installation](https://docs.xilinx.com/r/{{#tool-version vivado }}-English/ug973-vivado-release-notes-install-license/Download-and-Installation) for installation instructions.

When asked what edition to install, choose "Vivado HL Design Edition".
On the feature selection screen, select at least the following features:

![Vivado features selection screen](features.png)

After installing Vivado, you will need to add Vivado's paths to your shell environment.
See [Launching the Vivado IDE from the Command Line on Windows or Linux](https://docs.xilinx.com/r/{{#tool-version vivado }}-English/ug892-vivado-design-flows-overview/Launching-the-Vivado-IDE-from-the-Command-Line-on-Windows-or-Linux) for instructions.
