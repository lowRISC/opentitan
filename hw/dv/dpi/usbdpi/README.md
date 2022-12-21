#USBDPI

This DPI model is used with top-level testing of the USB device as well as forming
part of the ['Hello, USB!'](/sw/device/examples/hello_usbdev') example
application.

It must meet the following requirements:

 - Implements a simple model of USB host behaviour with bus framing; in reality
   the bus frames have a periodicity of 1ms, but to reduce the simulation time
   the frame period is modified to 0.17ms.

 - *hello_usbdev*
   Sets up each of endpoints 1 and 2 as serial communications in both directions.
   Once more then two characters have been received on endpoint 1, the software
   transmits the sign-on message 'Hello, USB!' via endpoint 1.

 - *usbdev_test*
   USB endpoint 1 is used for a simple data transmission test from the DPI model
   to the USB device

 - *usbdev_stream_test*
   USB endpoints [1:n] are used for bulk transfers of LFSR-generated data to the
   DPI model where the received data is checked. In parallel with that, these
   streams are combined with DPI-generated LFSR streams and sent to the
   corresponding OUT endpoints of the device.
   
   The test has passed when all outbound data has been sent from the software,
   and all inbound data has been received and checked successfully.

**Future development:**

 - detection of error conditions, invalid responses etc, and signalling of
   such errors to the software so that the software can report the test status
   as failed.

 - generation of error conditions, bus resets, suspend states, and invalid
   transmissions, data corruptions and responses, probably in response to a test
   number/programme supplied by (i) the test environment, or (ii) the software
   running on the simulated CPU; this shall become the basis for a set of
   top-level verification tests in CI.

## Overview

The DPI model applies (simulated) power to the device (detected by the device via
the 'sense' input), and the device - under software control - indicates that it
is a Full Speed device. After a suitable delay, the DPI model will set the device
address and then read the device and configuration descriptors.

Next it selects the configuration to be used, as a real host would, and proceeds
to read a test descriptor from the CPU software via a vendor-specific command.
This instructs the DPI model what behavior is required of it.

TODO - a lot more detail, but the model itself is still very much in a state of
flux
